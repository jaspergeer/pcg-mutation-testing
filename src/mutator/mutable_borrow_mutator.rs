use super::borrowed_places_with_capability_kind;
use super::owned_places_with_capability_kind;
use super::pcg_node_to_current_place;

use super::mutator_impl::Mutant;
use super::mutator_impl::MutantLocation;
use super::mutator_impl::MutantRange;
use super::mutator_impl::Mutator;

use std::collections::HashSet;
use std::collections::VecDeque;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::BorrowKind;
use crate::rustc_interface::middle::mir::Local;
use crate::rustc_interface::middle::mir::LocalDecl;
use crate::rustc_interface::middle::mir::MutBorrowKind;
use crate::rustc_interface::middle::mir::Place as MirPlace;
use crate::rustc_interface::middle::mir::PlaceRef;
use crate::rustc_interface::middle::mir::Rvalue;
use crate::rustc_interface::middle::mir::Statement;
use crate::rustc_interface::middle::mir::StatementKind;
use crate::rustc_interface::middle::ty::Region;
use crate::rustc_interface::middle::ty::RegionKind;
use crate::rustc_interface::middle::ty::Ty;
use crate::rustc_interface::middle::ty::TyCtxt;

use crate::rustc_interface::data_structures::fx::FxHashSet;

use pcs::FpcsOutput;

use pcs::free_pcs::CapabilityKind;
use pcs::free_pcs::CapabilityLocal;
use pcs::free_pcs::CapabilitySummary;
use pcs::free_pcs::PcgBasicBlock;
use pcs::free_pcs::PcgLocation;

use pcs::combined_pcs::PCGNode;
use pcs::combined_pcs::PCGNodeLike;

use pcs::utils::maybe_old::MaybeOldPlace;
use pcs::utils::maybe_remote::MaybeRemotePlace;
use pcs::utils::place::Place;
use pcs::utils::PlaceRepacker;

use pcs::borrow_pcg::borrow_pcg_capabilities::BorrowPCGCapabilities;
use pcs::borrow_pcg::borrow_pcg_edge::BorrowPCGEdgeLike;
use pcs::borrow_pcg::edge::kind::BorrowPCGEdgeKind;
use pcs::borrow_pcg::edge_data::EdgeData;
use pcs::borrow_pcg::graph::BorrowsGraph;
use pcs::borrow_pcg::state::BorrowsState;

pub struct MutableBorrowMutator;

impl Mutator for MutableBorrowMutator {
    fn generate_mutants<'mir, 'tcx>(
        &mut self,
        tcx: &TyCtxt<'tcx>,
        analysis: &mut FpcsOutput<'mir, 'tcx>,
        body: &Body<'tcx>,
    ) -> Vec<Mutant<'tcx>> {
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
        //             if let Some(place) = node_into_current_place(&(*repacker).tcx(), curr) {
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

        fn generate_mutants_for_bb<'mir, 'tcx>(
            tcx: &TyCtxt<'tcx>,
            body: &Body<'tcx>,
            analysis: &mut FpcsOutput<'mir, 'tcx>,
            pcg_bb: &PcgBasicBlock<'tcx>,
        ) -> Vec<Mutant<'tcx>> {
            pcg_bb
                .statements
                .iter()
                .enumerate()
                .flat_map(|(i, loc)| {
                    if pcg_bb.statements.len() - i > 3 /* Terminators are statements in the PCG */ {
                        generate_mutants_for_location(tcx, body, loc, &pcg_bb.statements[i + 1], &pcg_bb.statements[(i + 2)..])
                    } else {
                        vec![]
                    }
                })
                .collect::<Vec<_>>()
        }

        fn generate_mutants_for_location<'mir, 'tcx>(
            tcx: &TyCtxt<'tcx>,
            body: &Body<'tcx>,
            loc: &PcgLocation<'tcx>,
            next_loc: &PcgLocation<'tcx>,
            remaining_locs: &[PcgLocation<'tcx>],
        ) -> Vec<Mutant<'tcx>> {
            let repacker = PlaceRepacker::new(body, *tcx);

            let mutably_lent_in_loc = {
                let borrows_state = loc.borrows.post_operands();
                let borrow_capabilities = borrows_state.capabilities.as_ref();
                let owned_capabilities = loc.states.post_main();
                let mut owned_lent =
                    owned_places_with_capability_kind(&owned_capabilities, CapabilityKind::Lent);
                let mut borrowed_lent = borrowed_places_with_capability_kind(
                    &borrow_capabilities,
                    CapabilityKind::Lent,
                );
                owned_lent.extend(borrowed_lent.drain());
                owned_lent
            };

            let mutably_lent_in_next = {
                let borrows_state = next_loc.borrows.post_operands();
                let borrow_capabilities = borrows_state.capabilities.as_ref();
                let owned_capabilities = next_loc.states.post_main();
                let mut owned_lent =
                    owned_places_with_capability_kind(&owned_capabilities, CapabilityKind::Lent);
                let mut borrowed_lent = borrowed_places_with_capability_kind(
                    &borrow_capabilities,
                    CapabilityKind::Lent,
                );
                owned_lent.extend(borrowed_lent.drain());
                owned_lent
            };

            mutably_lent_in_loc
                .iter()
                .filter(|place| mutably_lent_in_next.contains(place))
                .flat_map(|place| {
                    // for each mutably lent place, seek to the statement at which it becomes exclusive (read?) again, if that location exists
                    // and insert a placemention to extend the borrow

                    let mir_place = PlaceRef::from(**place).to_place(*tcx);
                    let mut mutant_body = body.clone();

                    let fresh_local = Local::from_usize(mutant_body.local_decls.len());
                    let erased_region = Region::new_from_kind(*tcx, RegionKind::ReErased);

                    let borrow_ty = Ty::new_mut_ref(
                        *tcx,
                        erased_region,
                        mir_place.ty(&body.local_decls, *tcx).ty,
                    );

                    let statement_index = loc.location.statement_index;
                    let bb_index = loc.location.block;
                    let bb = mutant_body.basic_blocks_mut().get_mut(bb_index)?;
                    let statement_source_info = bb.statements.get(statement_index)?.source_info;

                    let borrow_expiry = remaining_locs.iter().find(|loc| {
                        let borrows_state = loc.borrows.post_operands();
                        let exclusive_in_loc = {
                            let borrows_state = loc.borrows.post_operands();
                            let borrow_capabilities = borrows_state.capabilities.as_ref();
                            let owned_capabilities = loc.states.post_main();
                            let mut owned_lent = owned_places_with_capability_kind(
                                &owned_capabilities,
                                CapabilityKind::Exclusive,
                            );
                            let mut borrowed_lent = borrowed_places_with_capability_kind(
                                &borrow_capabilities,
                                CapabilityKind::Exclusive,
                            );
                            owned_lent.extend(borrowed_lent.drain());
                            owned_lent
                        };
                        exclusive_in_loc.contains(place)
                    })?;

                    let expiry_index = borrow_expiry.location.statement_index;
                    let mention_place = Statement {
                        source_info: statement_source_info,
                        kind: StatementKind::PlaceMention(Box::new(mir_place)),
                    };

                    bb.statements.insert(expiry_index + 1, mention_place);

                    let default_mut_borrow = BorrowKind::Mut {
                        kind: MutBorrowKind::Default,
                    };
                    let default_mut_borrow = BorrowKind::Shared;
                    let new_borrow = Statement {
                        source_info: statement_source_info,
                        kind: StatementKind::Assign(Box::new((
                            MirPlace::from(fresh_local),
                            Rvalue::Ref(erased_region, default_mut_borrow, mir_place),
                        ))),
                    };
                    let info = format!(
                        "{:?} was mutably lent, so inserted {:?}, lent: {:?}",
                        mir_place, new_borrow, &mutably_lent_in_loc
                    );
                    bb.statements.insert(statement_index + 1, new_borrow);

                    let fresh_local_decl =
                        LocalDecl::with_source_info(borrow_ty, statement_source_info);
                    mutant_body
                        .local_decls
                        .raw
                        .insert(fresh_local.index(), fresh_local_decl);
                    // TODO also emit mutant w/ immutable reference to place

                    let borrow_loc = MutantLocation {
                        basic_block: loc.location.block.index(),
                        statement_index: statement_index + 1,
                    };

                    let mention_loc = MutantLocation {
                        basic_block: loc.location.block.index(),
                        statement_index: expiry_index + 1,
                    };

                    Some(Mutant {
                        body: mutant_body,
                        range: MutantRange {
                            start: borrow_loc,
                            end: mention_loc,
                        },
                        info: info,
                    })
                })
                .collect()
        }

        body.basic_blocks
            .indices()
            .flat_map(|bb_index| {
                analysis
                    .get_all_for_bb(bb_index)
                    .ok()?
                    .map(|pcg_bb| generate_mutants_for_bb(tcx, body, analysis, &pcg_bb))
            })
            .flatten()
            .collect()
    }

    fn run_ratio(&mut self) -> (u32, u32) {
        (1, 1)
    }

    fn name(&mut self) -> String {
        "mutably-lent-detector".into()
    }
}
