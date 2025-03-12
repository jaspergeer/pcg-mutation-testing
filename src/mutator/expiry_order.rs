use super::utils::bogus_source_info;
use super::utils::borrowed_places;
use super::utils::fresh_local;
use super::utils::fresh_basic_block;
use super::utils::is_mut;

use std::collections::HashSet;
use std::collections::HashMap;
use std::collections::VecDeque;

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
use crate::rustc_interface::middle::ty::RegionVid;
use crate::rustc_interface::middle::ty::RegionKind;
use crate::rustc_interface::middle::ty::Ty;
use crate::rustc_interface::middle::ty::TyCtxt;

use pcs::free_pcs::CapabilityKind;
use pcs::free_pcs::PcgLocation;

use pcs::combined_pcs::PCGNode;
use pcs::combined_pcs::PCGNodeLike;

use pcs::utils::PlaceRepacker;
use pcs::utils::place::Place;
use pcs::utils::maybe_old::MaybeOldPlace;

use pcs::borrow_pcg::has_pcs_elem::HasPcgElems;
use pcs::borrow_pcg::graph::BorrowsGraph;
use pcs::borrow_pcg::edge_data::EdgeData;
use pcs::borrow_pcg::edge::kind::BorrowPCGEdgeKind;
use pcs::borrow_pcg::borrow_pcg_edge::BorrowPCGEdgeRef;
use pcs::borrow_pcg::borrow_pcg_edge::BorrowPCGEdgeLike;
use pcs::borrow_pcg::borrow_pcg_edge::BlockedNode;
use pcs::borrow_pcg::borrow_pcg_edge::LocalNode;
use pcs::borrow_pcg::region_projection::RegionProjection;

pub struct ExpiryOrder;

impl PeepholeMutator for ExpiryOrder {
    // fn mutably_lent_places<'mir, 'tcx>(
    //     borrows_state: &BorrowsState<'tcx>,
    //     owned_capabilities: &CapabilitySummary<'tcx>,
    //     repacker: &PlaceRepacker<'mir, 'tcx>,
    // ) -> HashSet<Place<'tcx>> {
    //     let graph = borrows_state.graph();
    //     let leaf_edges = graph.frozen_graph().leaf_edges(*repacker);

    //     let mut to_visit = leaf_edges
    //         .iter()
    //         .flat_map(|edge| match edge.kind() {
    //             BorrowPCGEdgeKind::Borrow(borrow_edge) => {
    //                 if borrow_edge.is_mut() {
    //                     edge.blocked_nodes(*repacker)
    //                 } else {
    //                     FxHashSet::default()
    //                 }
    //             }
    //             _ => FxHashSet::default(),
    //         })
    //         .collect::<VecDeque<_>>();

    //     let mut visited = HashSet::new();
    //     let mut mutably_lent_places = HashSet::new();

    //     while let Some(curr) = to_visit.pop_front() {
    //         if !visited.contains(&curr) {
    //             if let Some(place) = pcg_node_to_current_place(curr) {
    //                 if let Some(capability) = borrows_state.get_capability(curr) {
    //                     if let CapabilityKind::Lent = capability {
    //                         mutably_lent_places.insert(place);
    //                     }
    //                 } else if let Some(local_capability) = owned_capabilities.get(place.local) {
    //                     if let CapabilityLocal::Allocated(projections) = local_capability {
    //                         if let Some(capability) = projections.get(&place) {
    //                             if let CapabilityKind::Lent = capability {
    //                                 mutably_lent_places.insert(place);
    //                             }
    //                         }
    //                     }
    //                 }
    //             }

    //             if let Some(local_node) = curr.try_to_local_node() {
    //                 let children = graph
    //                     .edges_blocked_by(local_node, *repacker)
    //                     .flat_map(|edge| edge.blocked_nodes(*repacker));
    //                 for child in children {
    //                     to_visit.push_back(child);
    //                 }
    //                 visited.insert(curr);
    //             }
    //         }
    //     }
    //     mutably_lent_places
    // }
    //
    //
    // TODO create a sequence that expires borrows in topological order
    // then, for each place in the chain, place an access in an illegal position in the sequence

    fn generate_mutants<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        curr: &PcgLocation<'tcx>,
        next: &PcgLocation<'tcx>,
    ) -> Vec<Mutant<'tcx>> {
        fn expiry_order<'tcx, 'mir>(
            borrows_graph: &BorrowsGraph<'tcx>,
            repacker: PlaceRepacker<'mir, 'tcx>
        ) -> Vec<HashSet<Place<'tcx>>> {
            // TODO visit NODES rather than edges and increment only if the node is NOT REMOTE + edge is blocking (mut)
            // TODO really what we are looking for are borrow edges,
            // should this list include the leaves???
            // how do we do this when all the nodes are diff types
            let mut to_visit: VecDeque<(PCGNode<'_>, usize)> =
                borrows_graph
                .frozen_graph()
                .leaf_nodes(repacker)
                .map(BlockedNode::from)
                .map(|node| (node, 0))
                .collect();

            let mut place_depths: HashMap<Place<'_>, usize> = HashMap::new();

            let mut max_depth = 0;
            while let Some((curr, depth)) = to_visit.pop_front() {
                match curr {
                    PCGNode::RegionProjection(mut region_projection) =>
                        for maybe_old_place in region_projection.pcg_elems().iter() {
                            if let MaybeOldPlace::Current { place } = maybe_old_place {
                                if place_depths.get(place).iter().all(|place_depth| **place_depth < depth) {
                                    place_depths.insert(*place, depth);
                                    max_depth = std::cmp::max(max_depth, depth);
                                }
                            }
                        },
                    PCGNode::Place(maybe_remote_place) =>
                        if let Some(place) = maybe_remote_place.as_current_place() {
                            if place_depths.get(&place).iter().all(|place_depth| **place_depth < depth) {
                                place_depths.insert(place.into(), depth);
                                max_depth = std::cmp::max(max_depth, depth);
                            }
                        }
                }

                let maybe_local_node = curr.try_to_local_node(repacker);
                let blocked_edges =
                    maybe_local_node
                    .iter()
                    .flat_map(|local_node_ref| {
                        let local_node = *local_node_ref;
                        borrows_graph.edges_blocked_by(local_node, repacker)
                    });


                for edge in blocked_edges {
                    match edge.kind() {
                        BorrowPCGEdgeKind::Borrow(borrow_edge) => {
                            let mut blocked_nodes = edge.blocked_nodes(repacker);
                            let mut new_nodes =
                                blocked_nodes
                                    .drain()
                                    .map(|node| (node, depth + 1));
                            to_visit.extend(new_nodes);
                        }
                        BorrowPCGEdgeKind::BorrowPCGExpansion(_) => {
                            let mut blocked_nodes = edge.blocked_nodes(repacker);
                            let mut new_nodes =
                                blocked_nodes
                                    .drain()
                                    .map(|node| (node, depth));
                            to_visit.extend(new_nodes);
                        }
                        _=> (),
                    }
                }
            }

            let mut buckets: Vec<HashSet<Place<'_>>> = vec![];

            for i in (0..max_depth + 1) {
                buckets.push(HashSet::new());
            }

            for (place, depth) in place_depths.iter() {
                buckets.get_mut(*depth).unwrap().insert(*place);
            }

            buckets.drain(..).filter(|bucket| !bucket.is_empty()).collect()
        }

        fn places_blocking<'mir, 'tcx>(
            place: Place<'tcx>,
            borrows_graph: &BorrowsGraph<'tcx>,
            repacker: PlaceRepacker<'mir, 'tcx>
        ) -> HashSet<Place<'tcx>> {
            let node = place.into();
            let mut to_visit: VecDeque<(BorrowPCGEdgeRef<'_, '_>, bool)> =
                borrows_graph
                .frozen_graph()
                .get_edges_blocking(node, repacker)
                .drain()
                .map(|edge| (edge, false))
                .collect();
            let mut places: HashSet<Place<'tcx>> = HashSet::new();

            while let Some((curr, mut is_blocking)) = to_visit.pop_front() {
                if let BorrowPCGEdgeKind::Borrow(borrow_edge) = curr.kind() {
                    is_blocking = is_blocking || borrow_edge.is_mut(repacker);
                }
                if is_blocking {
                    let mut nodes: Vec<_> = curr
                        .blocked_by_nodes(repacker)
                        .drain()
                        .flat_map(MaybeOldPlace::try_from)
                        .flat_map(|maybe_old_place| match maybe_old_place {
                            MaybeOldPlace::Current { place } => Some(place),
                            _ => None
                        })
                        .collect();
                    places.extend(nodes.drain(..));
                }
                let mut incident_nodes = curr.blocked_by_nodes(repacker);
                let mut adjacent_edges =
                    incident_nodes
                    .drain()
                    .map(BlockedNode::from)
                    .flat_map(|node|
                              borrows_graph.frozen_graph()
                              .get_edges_blocking(node, repacker))
                    .map(|edge| (edge, is_blocking));

                to_visit.extend(adjacent_edges);
            }
            places
        }

        fn places_to_statements<'tcx>(
            tcx: TyCtxt<'tcx>,
            body: &mut Body<'tcx>,
            places: impl Iterator<Item = Place<'tcx>>,
        ) -> Vec<Statement<'tcx>> {
            places.map(|place| {
                let mir_place = PlaceRef::from(*place).to_place(tcx);
                let target = fresh_local(body, mir_place.ty(&body.local_decls, tcx).ty);
                let region = Region::new_var(tcx, RegionVid::MAX);
                Statement {
                    source_info: bogus_source_info(body),
                    kind: StatementKind::Assign(Box::new((
                        MirPlace::from(target),
                        Rvalue::Ref(region, BorrowKind::Shared, mir_place)
                    )))
                }
            }).collect()
        }

        // TODO there might be some borrows expired at the post operands of next
        // these will now be expired at the first statement of our new branch
        // we split between curr and next

        // TODO we could also just mark nodes by depth and then create mutants by
        // attempting to access a node while all of the nodes in a smaller depth
        // are still live
        // when a node is encountered at two depths, take the larger depth
        //
        // alternatively, we can top sort with a random seed and mutate from there?


        // let mutant_bb = BasicBlockData::new(
        //     None
        // );

        let repacker = PlaceRepacker::new(&body, tcx);
        let borrows_graph = next.borrows.post_operands().graph();
        let expiry_sequence: Vec<_> = {
            let mut expiry_order = expiry_order(&borrows_graph, repacker);
            expiry_order.drain(..).flatten().collect()
        };

        eprintln!("expiry sequence{:?}", &expiry_sequence);
        let mut mutant_sequences = vec![];
        for i in 0..expiry_sequence.len() {
            let blocking_places = places_blocking(expiry_sequence[i], &borrows_graph, repacker);
            for j in 0..i {
                if blocking_places.contains(&expiry_sequence[j]) {
                    let mut mutant_body = body.clone();
                    let mut mutant_sequence =
                        places_to_statements(tcx,
                                             &mut mutant_body,
                                             expiry_sequence
                                             .iter()
                                             .map(|place| *place));
                    let blocked_statement = mutant_sequence.remove(i);
                    mutant_sequence.insert(j, blocked_statement);
                    mutant_sequences.push((mutant_sequence, mutant_body));
                }
            }
        }

        eprintln!("mutant sequences: {:?}", &mutant_sequences);
        mutant_sequences.drain(..).map(|(mutant_sequence, mut mutant_body)| {
            let curr_bb_index = curr.location.block;
            let bb = mutant_body.basic_blocks_mut().get_mut(curr_bb_index).unwrap();
            let mut tail_statements =
                bb.statements.drain(next.location.statement_index..).collect();

            let bb_terminator = bb.terminator.take();
            let tail_bb_index = fresh_basic_block(&mut mutant_body);
            let mut tail_bb = mutant_body.basic_blocks_mut().get_mut(tail_bb_index).unwrap();
            tail_bb.statements.append(&mut tail_statements);
            tail_bb.terminator = bb_terminator;

            let bogus_source_info = bogus_source_info(&mutant_body);

            let mutant_bb_index = fresh_basic_block(&mut mutant_body);
            let mut mutant_bb = mutant_body.basic_blocks_mut().get_mut(mutant_bb_index).unwrap();
            mutant_bb.statements = mutant_sequence;
            mutant_bb.terminator = Some(Terminator {
                source_info: bogus_source_info,
                kind: TerminatorKind::Return
            });

            let start_loc = MutantLocation {
                basic_block: mutant_bb_index.into(),
                statement_index: 0,
            };

            let end_loc = MutantLocation {
                basic_block: mutant_bb_index.into(),
                statement_index: mutant_bb.statements.len() - 1,
            };

            let bb = mutant_body.basic_blocks_mut().get_mut(curr_bb_index).unwrap();
            bb.terminator = Some(Terminator {
                source_info: bogus_source_info,
                kind: TerminatorKind::FalseEdge {
                    real_target: tail_bb_index,
                    imaginary_target: mutant_bb_index,
                }
            });

            Mutant {
                body: mutant_body,
                range: MutantRange {
                    start: start_loc,
                    end: end_loc,
                },
                info: "todo".to_string(),
            }
        }).collect()
    }

    fn run_ratio(&mut self) -> (u32, u32) {
        (1, 1)
    }

    fn name(&mut self) -> String {
        "expiry-order".into()
    }
}
