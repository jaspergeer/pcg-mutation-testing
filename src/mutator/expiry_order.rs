use super::utils::bogus_source_info;
use super::utils::borrowed_places;
use super::utils::fresh_basic_block;
use super::utils::fresh_local;
use super::utils::is_mut;
use super::utils::has_named_local;
use super::utils::local_node_to_current_place;

use std::collections::HashSet;

use super::mutator_impl::Mutant;
use super::mutator_impl::MutantLocation;
use super::mutator_impl::MutantRange;
use super::mutator_impl::PeepholeMutator;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::BorrowKind;
use crate::rustc_interface::middle::mir::Place as MirPlace;
use crate::rustc_interface::middle::mir::PlaceRef;
use crate::rustc_interface::middle::mir::Rvalue;
use crate::rustc_interface::middle::mir::Statement;
use crate::rustc_interface::middle::mir::StatementKind;
use crate::rustc_interface::middle::mir::Terminator;
use crate::rustc_interface::middle::mir::TerminatorKind;
use crate::rustc_interface::middle::ty::Region;
use crate::rustc_interface::middle::ty::RegionVid;
use crate::rustc_interface::middle::ty::Ty;
use crate::rustc_interface::middle::ty::TyCtxt;

use pcg::free_pcs::PcgLocation;

use pcg::pcg::EvalStmtPhase;

use pcg::utils::place::Place;
use pcg::utils::CompilerCtxt;

use pcg::borrow_pcg::borrow_pcg_edge::BlockedNode;
use pcg::borrow_pcg::borrow_pcg_edge::BorrowPcgEdgeLike;
use pcg::borrow_pcg::borrow_pcg_edge::BorrowPcgEdgeRef;
use pcg::borrow_pcg::edge::kind::BorrowPcgEdgeKind;
use pcg::borrow_pcg::edge_data::EdgeData;
use pcg::borrow_pcg::graph::BorrowsGraph;

fn places_blocking<'mir, 'tcx>(
    place: Place<'tcx>,
    borrows_graph: &BorrowsGraph<'tcx>,
    ctx: CompilerCtxt<'mir, 'tcx>,
    is_blocking_edge: impl Fn(&HashSet<BorrowPcgEdgeKind>) -> bool,
    is_valid_edge: impl Fn(&BorrowPcgEdgeKind) -> bool,
) -> HashSet<Place<'tcx>> {
    // println!();
    // println!("PLACES BLOCKING {:?}", &place);
    let node = place.into();
    let mut to_visit: Vec<(BorrowPcgEdgeRef<'_, '_>,
                           HashSet<BorrowPcgEdgeKind<'_>>)> =
        borrows_graph
        .frozen_graph()
        .get_edges_blocking(node, ctx)
        .into_iter()
        .filter(|edge| is_valid_edge(edge.kind()))
        .map(|edge| (edge, HashSet::new()))
        .collect();
    let mut places: HashSet<Place<'tcx>> = HashSet::new();

    while let Some((curr, mut kind_set)) = to_visit.pop() {
        // println!("VISIT {:?}", &curr);
        kind_set.insert(curr.kind().clone());
        if is_blocking_edge(&kind_set) {
            let mut nodes: Vec<_> = curr
                .blocked_by_nodes(ctx)
                .flat_map(local_node_to_current_place)
                .collect();
            places.extend(nodes.drain(..));
        }
        let mut incident_nodes = curr.blocked_by_nodes(ctx);
        // println!("ADJACENT NODES {:?}", &incident_nodes);
        let mut adjacent_edges = incident_nodes
            .map(BlockedNode::from)
            .flat_map(|node| {
                borrows_graph
                    .frozen_graph()
                    .get_edges_blocking(node, ctx)
            })
            .filter(|edge| is_valid_edge(edge.kind()))
            .map(|edge| (edge, kind_set.clone()));
        to_visit.extend(adjacent_edges);
    }
    // println!("blocking_places for {:?}: {:?}", &place, &places);
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
    fn generate_mutants<'mir, 'tcx>(
        ctx: CompilerCtxt<'mir, 'tcx>,
        body: &Body<'tcx>,
        curr: &PcgLocation<'tcx>,
        next: &PcgLocation<'tcx>,
    ) -> Vec<Mutant<'tcx>> {
        let mut mutant_sequences: Vec<(Vec<Statement<'tcx>>, Body<'tcx>)> = vec![];

        let borrows_graph = next.states[EvalStmtPhase::PostOperands].borrow_pcg().graph();

        let mutably_borrowed_places: HashSet<Place<'tcx>> =
            borrowed_places(&borrows_graph, is_mut)
            .map(|(place, _)| (*place).into())
            .collect();

        for place_ref in mutably_borrowed_places.iter() {
            let place = *place_ref;
            if has_named_local(place, body) {
                let mut blocking_places = places_blocking(
                    place,
                    &borrows_graph,
                    ctx,
                    |kind_set| {
                       kind_set
                        .iter()
                        .any(|kind| match kind {
                            BorrowPcgEdgeKind::Borrow(borrow_edge) =>
                                borrow_edge.kind().iter().any(|kind| is_mut(*kind)),
                            _ => false,
                        })
                    },
                    |kind| match kind {
                        BorrowPcgEdgeKind::Borrow(borrow_edge) =>
                            borrow_edge.kind().iter().any(|kind| is_mut(*kind)),
                        _ => true,
                    },
                );
                for blocking_place in blocking_places.drain() {
                    if has_named_local(blocking_place, body) {
                        let mut mutant_body = body.clone();
                        let mut mutant_sequence = places_to_statements(
                            ctx.tcx(),
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
                    statement_index: curr.location.statement_index,
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
    fn generate_mutants<'mir, 'tcx>(
        ctx: CompilerCtxt<'mir, 'tcx>,
        body: &Body<'tcx>,
        curr: &PcgLocation<'tcx>,
        next: &PcgLocation<'tcx>,
    ) -> Vec<Mutant<'tcx>> {
        let mut mutant_sequences: Vec<(Vec<Statement<'tcx>>, Body<'tcx>)> = vec![];

        let borrows_graph = next.states[EvalStmtPhase::PostOperands].borrow_pcg().graph();

        let mutably_borrowed_places: HashSet<Place<'tcx>> =
            borrowed_places(&borrows_graph, is_mut)
            .map(|(place, _)| (*place).into())
            .collect();

        for place_ref in mutably_borrowed_places.iter() {
            let place = *place_ref;
            if has_named_local(place, body) {
                let mut blocking_places = places_blocking(
                    place,
                    &borrows_graph,
                    ctx,
                    |kind_set| {
                       kind_set
                        .iter()
                        .any(|kind| match kind {
                            BorrowPcgEdgeKind::Abstraction(_) => true,
                            _ => false,
                        }) &&
                            kind_set
                            .iter()
                            .any(|kind| match kind {
                                BorrowPcgEdgeKind::Borrow(borrow_edge) =>
                                    borrow_edge.kind().iter().any(|kind| is_mut(*kind)),
                                _ => false,
                            })
                    },
                    |kind| match kind {
                        BorrowPcgEdgeKind::Borrow(borrow_edge) =>
                            borrow_edge.kind().iter().any(|kind| is_mut(*kind)),
                        _ => true,
                    },
                );
                for blocking_place in blocking_places.drain() {
                    if has_named_local(blocking_place, body) {
                        let mut mutant_body = body.clone();
                        let mut mutant_sequence = places_to_statements(
                            ctx.tcx(),
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
