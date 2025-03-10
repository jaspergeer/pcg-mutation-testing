use super::utils::bogus_source_info;
use super::utils::borrowed_places;
use super::utils::fresh_local;

use std::collections::HashSet;

use super::mutator_impl::Mutant;
use super::mutator_impl::MutantLocation;
use super::mutator_impl::MutantRange;
use super::mutator_impl::PeepholeMutator;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::BorrowKind;
use crate::rustc_interface::middle::mir::FakeReadCause;
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

use pcs::free_pcs::CapabilityKind;
use pcs::free_pcs::PcgLocation;

pub struct BlockMutableBorrow;

impl PeepholeMutator for BlockMutableBorrow {
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
    fn generate_mutants<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        curr: &PcgLocation<'tcx>,
        next: &PcgLocation<'tcx>,
    ) -> Vec<Mutant<'tcx>> {
        fn generate_mutant_with_borrow_kind<'tcx>(
            tcx: TyCtxt<'tcx>,
            body: &Body<'tcx>,
            curr: &PcgLocation<'tcx>,
            lent_place: MirPlace<'tcx>,
            region: Region<'tcx>,
            borrow_kind: BorrowKind,
        ) -> Option<Mutant<'tcx>> {
            let mut mutant_body = body.clone();

            let borrow_ty =
                Ty::new_mut_ref(tcx, region, lent_place.ty(&body.local_decls, tcx).ty);

            let fresh_local = fresh_local(&mut mutant_body, borrow_ty);

            let statement_index = curr.location.statement_index;

            let place_live = Statement {
                source_info: bogus_source_info(&mutant_body),
                kind: StatementKind::StorageLive(fresh_local),
            };

            let place_dead = Statement {
                source_info: bogus_source_info(&mutant_body),
                kind: StatementKind::StorageDead(fresh_local),
            };

            let fake_read = Statement {
                source_info: bogus_source_info(&mutant_body),
                kind: StatementKind::FakeRead(Box::new((
                    FakeReadCause::ForLet(None),
                    MirPlace::from(fresh_local),
                ))),
            };

            let place_mention = Statement {
                source_info: bogus_source_info(&mutant_body),
                kind: StatementKind::PlaceMention(Box::new(
                        MirPlace::from(fresh_local))),
            };

            let new_borrow = Statement {
                source_info: bogus_source_info(&mutant_body),
                kind: StatementKind::Assign(Box::new((
                    MirPlace::from(fresh_local),
                    Rvalue::Ref(region, borrow_kind, lent_place),
                ))),
            };

            let info = format!(
                "{:?} was mutably lent, so inserted {:?}",
                lent_place, &new_borrow
            );

            let bb_index = curr.location.block;
            let bb = mutant_body.basic_blocks_mut().get_mut(bb_index)?;
            bb.statements.insert(statement_index + 2, place_dead);
            bb.statements.insert(statement_index + 2, place_mention);
            bb.statements.insert(statement_index + 2, fake_read);
            bb.statements.insert(statement_index, new_borrow);
            bb.statements.insert(statement_index, place_live);

            let borrow_loc = MutantLocation {
                basic_block: curr.location.block.index(),
                statement_index: statement_index,
            };

            let mention_loc = MutantLocation {
                basic_block: curr.location.block.index(),
                statement_index: statement_index + 2,
            };

            Some(Mutant {
                body: mutant_body,
                range: MutantRange {
                    start: borrow_loc,
                    end: mention_loc,
                },
                info: info,
            })
        }

        let mutably_lent_in_curr = {
            let borrows_graph = curr.borrows.post_main().graph();
            borrowed_places(borrows_graph, true).map(|(place, _)| place).collect::<HashSet<_>>()
        };

        let mutably_lent_in_next = {
            let borrows_graph = next.borrows.post_main().graph();
            borrowed_places(borrows_graph, true)
        };

        mutably_lent_in_next
            .filter(|(place, _)| !mutably_lent_in_curr.contains(place))
            .flat_map(|(place, region)| {
                let lent_place = PlaceRef::from(*place).to_place(tcx);
                vec![
                    generate_mutant_with_borrow_kind(
                        tcx,
                        body,
                        curr,
                        lent_place,
                        region,
                        BorrowKind::Shared,
                    ),
                    generate_mutant_with_borrow_kind(
                        tcx,
                        body,
                        curr,
                        lent_place,
                        region,
                        BorrowKind::Mut {
                            kind: MutBorrowKind::Default,
                        },
                    ),
                ]
                .drain(..)
                .flatten()
                .collect::<Vec<_>>()
            })
            .collect()
    }

    fn run_ratio(&mut self) -> (u32, u32) {
        (1, 1)
    }

    fn name(&mut self) -> String {
        "block-mutable-borrow".into()
    }
}
