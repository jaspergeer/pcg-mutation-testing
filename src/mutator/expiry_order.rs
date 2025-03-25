use super::utils::bogus_source_info;
use super::utils::borrowed_places;
use super::utils::filter_borrowed_places_by_capability;
use super::utils::filter_owned_places_by_capability;
use super::utils::fresh_basic_block;
use super::utils::fresh_local;
use super::utils::is_mut;
use super::utils::has_named_local;
use super::utils::pcg_node_to_current_place;
use super::utils::local_node_to_current_place;

use std::collections::HashMap;
use std::collections::HashSet;

use super::mutator_impl::Mutant;
use super::mutator_impl::MutantLocation;
use super::mutator_impl::MutantRange;
use super::mutator_impl::PeepholeMutator;

use crate::rustc_interface::middle::mir::BasicBlockData;
use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::BorrowKind;
use crate::rustc_interface::middle::mir::FakeReadCause;
use crate::rustc_interface::middle::mir::MutBorrowKind;
use crate::rustc_interface::middle::mir::Place as MirPlace;
use crate::rustc_interface::middle::mir::PlaceRef;
use crate::rustc_interface::middle::mir::Rvalue;
use crate::rustc_interface::middle::mir::Statement;
use crate::rustc_interface::middle::mir::StatementKind;
use crate::rustc_interface::middle::mir::Terminator;
use crate::rustc_interface::middle::mir::TerminatorKind;
use crate::rustc_interface::middle::ty::Region;
use crate::rustc_interface::middle::ty::RegionKind;
use crate::rustc_interface::middle::ty::RegionVid;
use crate::rustc_interface::middle::ty::Ty;
use crate::rustc_interface::middle::ty::TyCtxt;

use pcs::free_pcs::CapabilityKind;
use pcs::free_pcs::PcgLocation;

use pcs::combined_pcs::PCGNode;
use pcs::combined_pcs::PCGNodeLike;

use pcs::utils::maybe_old::MaybeOldPlace;
use pcs::utils::place::Place;
use pcs::utils::PlaceRepacker;

use pcs::borrow_pcg::borrow_pcg_edge::BlockedNode;
use pcs::borrow_pcg::borrow_pcg_edge::BorrowPCGEdgeLike;
use pcs::borrow_pcg::borrow_pcg_edge::BorrowPCGEdgeRef;
use pcs::borrow_pcg::borrow_pcg_edge::LocalNode;
use pcs::borrow_pcg::edge::borrow::BorrowEdge;
use pcs::borrow_pcg::edge::kind::BorrowPCGEdgeKind;
use pcs::borrow_pcg::edge_data::EdgeData;
use pcs::borrow_pcg::graph::BorrowsGraph;
use pcs::borrow_pcg::region_projection::RegionProjection;

// fn order_by_expiry<'tcx, 'mir>(
//     borrows_graph: &BorrowsGraph<'tcx>,
//     repacker: PlaceRepacker<'mir, 'tcx>,
//     loc: &PcgLocation<'tcx>,
// ) -> Vec<Place<'tcx>> {
//     let mut ordered_places: Vec<Place<'tcx>> = vec![];

//     let mut to_visit: Vec<PCGNode<'tcx>> = borrows_graph
//         .frozen_graph()
//         .leaf_nodes(repacker)
//         .map(BlockedNode::from)
//         .collect();

//     let mut blocking_map: HashMap<PCGNode<'tcx>, usize> = HashMap::new();
//     for edge in borrows_graph.edges() {
//         for node in edge.blocked_nodes(repacker) {
//             let count = blocking_map.entry(node).or_insert(0);
//             let num_nodes_blocking = edge.blocked_by_nodes(repacker).len();
//             *count += num_nodes_blocking;
//         }
//     }

//     let mut to_visit: Vec<PCGNode<'tcx>> = borrows_graph
//         .nodes(repacker)
//         .drain()
//         .filter(|node| !blocking_map.contains_key(node))
//         .collect();

//     while let Some(curr) = to_visit.pop() {
//         if let Some(place) = pcg_node_to_current_place(curr) {
//             if has_named_local(place, repacker.body()) {
//                 ordered_places.push(place);
//             }
//         }

//         let maybe_local_node = curr.try_to_local_node(repacker);
//         let blocked_edges = maybe_local_node.iter().flat_map(|local_node_ref| {
//             let local_node = *local_node_ref;
//             borrows_graph.edges_blocked_by(local_node, repacker)
//         });

//         for edge in blocked_edges {
//             let mut blocked_nodes = edge.blocked_nodes(repacker);
//             for node in blocked_nodes.drain() {
//                 let count = blocking_map.get_mut(&node).unwrap();
//                 *count -= 1;
//                 if *count == 0 {
//                     blocking_map.remove(&node);
//                     to_visit.push(node);
//                 }
//             }
//         }
//     }
//     assert!(blocking_map.is_empty());

//     let write_only_in_loc = {
//         let borrows_state = loc.borrows.post_operands();
//         let mut owned_write = {
//             let owned_capabilities = loc.states.post_operands();
//             filter_owned_places_by_capability(&owned_capabilities, |ck| {
//                 ck == CapabilityKind::Write
//             })
//         };
//         let mut borrowed_write = {
//             let borrow_capabilities = borrows_state.capabilities();
//             filter_borrowed_places_by_capability(&borrow_capabilities, |ck| {
//                 ck == CapabilityKind::Write
//             })
//         };
//         owned_write.extend(borrowed_write.drain());
//         owned_write
//     };

//     ordered_places.drain(..)
//                   .filter(|place| !write_only_in_loc.contains(place))
//                   .collect()
// }


fn places_blocking<'mir, 'tcx>(
    place: Place<'tcx>,
    borrows_graph: &BorrowsGraph<'tcx>,
    repacker: PlaceRepacker<'mir, 'tcx>,
    is_blocking_edge: impl Fn(&HashSet<BorrowPCGEdgeKind>) -> bool,
    is_valid_edge: impl Fn(&BorrowPCGEdgeKind) -> bool,
) -> HashSet<Place<'tcx>> {
    let node = place.into();
    let mut to_visit: Vec<(BorrowPCGEdgeRef<'_, '_>,
                           HashSet<BorrowPCGEdgeKind<'_>>)> =
        borrows_graph
        .frozen_graph()
        .get_edges_blocking(node, repacker)
        .drain()
        .filter(|edge| is_valid_edge(edge.kind()))
        .map(|edge| (edge, HashSet::new()))
        .collect();
    let mut places: HashSet<Place<'tcx>> = HashSet::new();

    while let Some((curr, mut kind_set)) = to_visit.pop() {
        kind_set.insert(curr.kind().clone());
        if is_blocking_edge(&kind_set) {
            let mut nodes: Vec<_> = curr
                .blocked_by_nodes(repacker)
                .drain()
                .flat_map(local_node_to_current_place)
                .collect();
            places.extend(nodes.drain(..));
        }
        let mut incident_nodes = curr.blocked_by_nodes(repacker);
        let mut adjacent_edges = incident_nodes
            .drain()
            .map(BlockedNode::from)
            .flat_map(|node| {
                borrows_graph
                    .frozen_graph()
                    .get_edges_blocking(node, repacker)
            })
            .filter(|edge| is_valid_edge(edge.kind()))
            .map(|edge| (edge, kind_set.clone()));

        to_visit.extend(adjacent_edges);
    }
    places
}

fn places_to_statements<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mut Body<'tcx>,
    mut places: Vec<Place<'tcx>>,
) -> Vec<Statement<'tcx>> {
    places
        .drain(..)
        .map(|place| {
            let mir_place = PlaceRef::from(*place).to_place(tcx);
            let region = Region::new_var(tcx, RegionVid::MAX);
            let target_ty = Ty::new_mut_ref(tcx, region, mir_place.ty(&body.local_decls, tcx).ty);
            let target = fresh_local(body, target_ty);
            Statement {
                source_info: bogus_source_info(body),
                kind: StatementKind::Assign(Box::new((
                    MirPlace::from(target),
                    Rvalue::Ref(region, BorrowKind::Shared, mir_place),
                ))),
            }
        })
        .collect()
}

pub struct BorrowExpiryOrder;

impl PeepholeMutator for BorrowExpiryOrder {
    fn generate_mutants<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        curr: &PcgLocation<'tcx>,
        next: &PcgLocation<'tcx>,
    ) -> Vec<Mutant<'tcx>> {
        let repacker = PlaceRepacker::new(&body, tcx);

        let mut mutant_sequences: Vec<(Vec<Statement<'tcx>>, Body<'tcx>)> = vec![];

        let mut initialized_places = {
            let mut owned_init: HashSet<_> = {
                let owned_capabilities = next.states.post_operands();
                filter_owned_places_by_capability(&owned_capabilities, repacker, |ck| {
                    !ck.iter().any(|c| c.is_write())
                })
            };
            let mut borrowed_init = {
                let borrows_state = next.borrows.post_operands();
                filter_borrowed_places_by_capability(&borrows_state, repacker, |ck| {
                    !ck.iter().any(|c| c.is_write())
                })
            };
            owned_init.extend(borrowed_init.drain());
            owned_init
        };

        let borrows_graph = next.borrows.post_operands().graph();

        for place_ref in initialized_places.iter() {
            let place = *place_ref;
            if has_named_local(place, body) {
                let mut blocking_places = places_blocking(
                    place,
                    &borrows_graph,
                    repacker,
                    |kind_set| {
                       kind_set
                        .iter()
                        .any(|kind| match kind {
                            BorrowPCGEdgeKind::Borrow(borrow_edge) =>
                                borrow_edge.kind().iter().all(|kind| is_mut(*kind)),
                            _ => false,
                        })
                    },
                    |kind| match kind {
                        BorrowPCGEdgeKind::Abstraction(_) => false,
                        _ => true,
                    },
                );
                for blocking_place in blocking_places.drain() {
                    if has_named_local(blocking_place, body)
                        && initialized_places.contains(&blocking_place) {
                        let mut mutant_body = body.clone();
                        let mut mutant_sequence = places_to_statements(
                            tcx,
                            &mut mutant_body,
                            vec![place, blocking_place],
                        );
                        mutant_sequences.push((mutant_sequence, mutant_body));
                    }
                }
            }
        }

        mutant_sequences
            .drain(..)
            .map(|(mutant_sequence, mut mutant_body)| {
                let curr_bb_index = curr.location.block;
                let bb = mutant_body
                    .basic_blocks_mut()
                    .get_mut(curr_bb_index)
                    .unwrap();
                let mut tail_statements = bb
                    .statements
                    .drain(next.location.statement_index..)
                    .collect();

                let bb_terminator = bb.terminator.take();
                let tail_bb_index = fresh_basic_block(&mut mutant_body);
                let mut tail_bb = mutant_body
                    .basic_blocks_mut()
                    .get_mut(tail_bb_index)
                    .unwrap();
                tail_bb.statements.append(&mut tail_statements);
                tail_bb.terminator = bb_terminator;

                let bogus_source_info = bogus_source_info(&mutant_body);

                let mutant_bb_index = fresh_basic_block(&mut mutant_body);
                let mutant_bb = mutant_body
                    .basic_blocks_mut()
                    .get_mut(mutant_bb_index)
                    .unwrap();
                mutant_bb.statements = mutant_sequence;
                mutant_bb.terminator = Some(Terminator {
                    source_info: bogus_source_info,
                    kind: TerminatorKind::Unreachable,
                });

                let start_loc = MutantLocation {
                    basic_block: mutant_bb_index.into(),
                    statement_index: 0,
                };

                let end_loc = MutantLocation {
                    basic_block: mutant_bb_index.into(),
                    statement_index: mutant_bb.statements.len(),
                };

                let bb = mutant_body
                    .basic_blocks_mut()
                    .get_mut(curr_bb_index)
                    .unwrap();
                bb.terminator = Some(Terminator {
                    source_info: bogus_source_info,
                    kind: TerminatorKind::FalseEdge {
                        real_target: tail_bb_index,
                        imaginary_target: mutant_bb_index,
                    },
                });

                Mutant {
                    body: mutant_body,
                    range: MutantRange {
                        start: start_loc,
                        end: end_loc,
                    },
                    // info: format!("mutant sequence: {:?}", &mutant_sequence).to_string(),
                    info: format!("created new basic block {:?}", mutant_bb_index).to_string(),
                }
            })
            .collect()
    }

    fn run_ratio(&mut self) -> (u32, u32) {
        (1, 1)
    }

    fn name(&mut self) -> String {
        "borrow-expiry-order".into()
    }
}

pub struct AbstractExpiryOrder;

impl PeepholeMutator for AbstractExpiryOrder {
    fn generate_mutants<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        curr: &PcgLocation<'tcx>,
        next: &PcgLocation<'tcx>,
    ) -> Vec<Mutant<'tcx>> {
        let repacker = PlaceRepacker::new(&body, tcx);

        let mut mutant_sequences: Vec<(Vec<Statement<'tcx>>, Body<'tcx>)> = vec![];

        let mut initialized_places = {
            let mut owned_init: HashSet<_> = {
                let owned_capabilities = next.states.post_operands();
                filter_owned_places_by_capability(&owned_capabilities, repacker, |ck| {
                    // true
                    !ck.iter().any(|c| c.is_write())
                })
            };
            let mut borrowed_init = {
                let borrows_state = next.borrows.post_operands();
                filter_borrowed_places_by_capability(&borrows_state, repacker, |ck| {
                    // true
                    !ck.iter().any(|c| c.is_write())
                })
            };
            owned_init.extend(borrowed_init.drain());
            owned_init
        };

        let borrows_graph = next.borrows.post_operands().graph();

        for place_ref in initialized_places.iter() {
            let place = *place_ref;
            if has_named_local(place, body) {
                let mut blocking_places = places_blocking(
                    place,
                    &borrows_graph,
                    repacker,
                    |kind_set| {
                       kind_set
                        .iter()
                        .any(|kind| match kind {
                            BorrowPCGEdgeKind::Abstraction(_) => true,
                            _ => false,
                        }) &&
                            kind_set
                            .iter()
                            .any(|kind| match kind {
                                BorrowPCGEdgeKind::Borrow(borrow_edge) =>
                                    borrow_edge.kind().iter().all(|kind| is_mut(*kind)),
                                _ => false,
                            })
                    },
                    |_| true,
                );
                for blocking_place in blocking_places.drain() {
                    if has_named_local(blocking_place, body)
                        && initialized_places.contains(&blocking_place) {
                        let mut mutant_body = body.clone();
                        let mut mutant_sequence = places_to_statements(
                            tcx,
                            &mut mutant_body,
                            vec![place, blocking_place],
                        );
                        mutant_sequences.push((mutant_sequence, mutant_body));
                    }
                }
            }
        }

        mutant_sequences
            .drain(..)
            .map(|(mutant_sequence, mut mutant_body)| {
                let curr_bb_index = curr.location.block;
                let bb = mutant_body
                    .basic_blocks_mut()
                    .get_mut(curr_bb_index)
                    .unwrap();
                let mut tail_statements = bb
                    .statements
                    .drain(next.location.statement_index..)
                    .collect();

                let bb_terminator = bb.terminator.take();
                let tail_bb_index = fresh_basic_block(&mut mutant_body);
                let mut tail_bb = mutant_body
                    .basic_blocks_mut()
                    .get_mut(tail_bb_index)
                    .unwrap();
                tail_bb.statements.append(&mut tail_statements);
                tail_bb.terminator = bb_terminator;

                let bogus_source_info = bogus_source_info(&mutant_body);

                let mutant_bb_index = fresh_basic_block(&mut mutant_body);
                let mutant_bb = mutant_body
                    .basic_blocks_mut()
                    .get_mut(mutant_bb_index)
                    .unwrap();
                mutant_bb.statements = mutant_sequence;
                mutant_bb.terminator = Some(Terminator {
                    source_info: bogus_source_info,
                    kind: TerminatorKind::Unreachable,
                });

                let start_loc = MutantLocation {
                    basic_block: mutant_bb_index.into(),
                    statement_index: 0,
                };

                let end_loc = MutantLocation {
                    basic_block: mutant_bb_index.into(),
                    statement_index: mutant_bb.statements.len(),
                };

                let bb = mutant_body
                    .basic_blocks_mut()
                    .get_mut(curr_bb_index)
                    .unwrap();
                bb.terminator = Some(Terminator {
                    source_info: bogus_source_info,
                    kind: TerminatorKind::FalseEdge {
                        real_target: tail_bb_index,
                        imaginary_target: mutant_bb_index,
                    },
                });

                Mutant {
                    body: mutant_body,
                    range: MutantRange {
                        start: start_loc,
                        end: end_loc,
                    },
                    info: format!("created new basic block {:?}", mutant_bb_index).to_string(),
                }
            })
            .collect()
    }

    fn run_ratio(&mut self) -> (u32, u32) {
        (1, 1)
    }

    fn name(&mut self) -> String {
        "abstract-expiry-order".into()
    }
}
