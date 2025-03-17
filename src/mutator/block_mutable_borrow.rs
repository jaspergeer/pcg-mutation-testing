use super::utils::bogus_source_info;
use super::utils::borrowed_places;
use super::utils::fresh_local;
use super::utils::has_named_local;
use super::utils::is_mut;

use std::collections::HashSet;

use super::mutator_impl::Mutant;
use super::mutator_impl::MutantLocation;
use super::mutator_impl::MutantRange;
use super::mutator_impl::PeepholeMutator;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::BorrowKind;
use crate::rustc_interface::middle::mir::FakeReadCause;
use crate::rustc_interface::middle::mir::MutBorrowKind;
use crate::rustc_interface::middle::mir::Operand;
use crate::rustc_interface::middle::mir::Place as MirPlace;
use crate::rustc_interface::middle::mir::PlaceElem as MirPlaceElem;
use crate::rustc_interface::middle::mir::PlaceRef;
use crate::rustc_interface::middle::mir::Rvalue;
use crate::rustc_interface::middle::mir::Statement;
use crate::rustc_interface::middle::mir::StatementKind;
use crate::rustc_interface::middle::ty::Region;
use crate::rustc_interface::middle::ty::RegionKind;
use crate::rustc_interface::middle::ty::RegionVid;
use crate::rustc_interface::middle::ty::Ty;
use crate::rustc_interface::middle::ty::TyCtxt;

use pcs::free_pcs::CapabilityKind;
use pcs::free_pcs::PcgLocation;

use pcs::utils::PlaceRepacker;

pub struct BlockMutableBorrow;

impl PeepholeMutator for BlockMutableBorrow {
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
            // let region = Region::new_var(tcx, RegionVid::MAX);
            // let another_region = Region::new_var(tcx, RegionVid::MAX - 1);

            let borrow_ty = Ty::new_mut_ref(tcx, region, lent_place.ty(&body.local_decls, tcx).ty);

            let another_fresh_local = fresh_local(&mut mutant_body, borrow_ty);
            let fresh_local = fresh_local(&mut mutant_body, borrow_ty);

            let statement_index = curr.location.statement_index;

            // let place_live = Statement {
            //     source_info: bogus_source_info(&mutant_body),
            //     kind: StatementKind::StorageLive(fresh_local),
            // };

            // let place_dead = Statement {
            //     source_info: bogus_source_info(&mutant_body),
            //     kind: StatementKind::StorageDead(fresh_local),
            // };

            // let fake_read = Statement {
            //     source_info: bogus_source_info(&mutant_body),
            //     kind: StatementKind::FakeRead(Box::new((
            //         FakeReadCause::ForLet(None),
            //         MirPlace::from(fresh_local),
            //     ))),
            // };

            let fresh_local_deref =
                tcx.mk_place_elem(MirPlace::from(fresh_local), MirPlaceElem::Deref);

            let place_mention = Statement {
                source_info: bogus_source_info(&mutant_body),
                kind: StatementKind::PlaceMention(Box::new(MirPlace::from(another_fresh_local))), // lent_place)))
                                                                                                  // MirPlace::from(fresh_local)))),
            };

            let reborrow = Statement {
                source_info: bogus_source_info(&mutant_body),
                kind: StatementKind::Assign(Box::new((
                    MirPlace::from(another_fresh_local),
                    // Rvalue::Use(Operand::(fresh_local_deref))
                    Rvalue::Ref(region, borrow_kind, fresh_local_deref),
                ))),
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
            // bb.statements.push(place_dead);
            // bb.statements.insert(statement_index + 2, place_mention);
            // bb.statements.insert(statement_index, fake_read);
            // bb.statements.insert(statement_index, new_borrow);
            // bb.statements.insert(statement_index, place_live);
            // bb.statements.insert(statement_index + 2, place_mention);
            // bb.statements.push(reborrow);
            bb.statements.insert(statement_index + 2, reborrow);
            bb.statements.insert(statement_index, new_borrow);

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
            borrowed_places(borrows_graph, is_mut)
                .map(|(place, _)| place)
                .collect::<HashSet<_>>()
        };

        let mutably_lent_in_next = {
            let borrows_graph = next.borrows.post_main().graph();
            borrowed_places(borrows_graph, is_mut)
        };

        let repacker = PlaceRepacker::new(body, tcx);

        mutably_lent_in_next
            .filter(|(place, _)| has_named_local(*place, repacker))
            .filter(|(place, _)| !mutably_lent_in_curr.contains(place))
            .flat_map(|(place, region)| {
                let lent_place = PlaceRef::from(*place).to_place(tcx);
                vec![
                    // TODO Doesn't produce borrow checker violations for some reason
                    generate_mutant_with_borrow_kind(
                        tcx,
                        body,
                        curr,
                        lent_place,
                        region,
                        BorrowKind::Shared,
                    ),
                    // generate_mutant_with_borrow_kind(
                    //     tcx,
                    //     body,
                    //     curr,
                    //     lent_place,
                    //     region,
                    //     BorrowKind::Mut {
                    //         kind: MutBorrowKind::Default,
                    //     },
                    // ),
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
