use super::utils::borrowed_places;
use super::utils::filter_borrowed_places_by_capability;
use super::utils::filter_owned_places_by_capability;
use super::utils::fresh_local;
use super::utils::has_named_local;

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

pub struct MutablyLendReadOnly;

impl PeepholeMutator for MutablyLendReadOnly {
    fn generate_mutants<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        curr: &PcgLocation<'tcx>,
        next: &PcgLocation<'tcx>,
    ) -> Vec<Mutant<'tcx>> {
        let read_only_in_curr = {
            let borrows_state = curr.borrows.post_main();
            let mut owned_read = {
                let owned_capabilities = curr.states.post_main();
                filter_owned_places_by_capability(&owned_capabilities, |ck| {
                    ck == CapabilityKind::Read
                })
            };
            let mut borrowed_read = {
                let borrow_capabilities = borrows_state.capabilities();
                filter_borrowed_places_by_capability(&borrow_capabilities, |ck| {
                    ck == CapabilityKind::Read
                })
            };
            owned_read.extend(borrowed_read.drain());
            owned_read
        };

        let read_only_in_next = {
            let borrows_state = next.borrows.post_main();
            let mut owned_read = {
                let owned_capabilities = next.states.post_main();
                filter_owned_places_by_capability(&owned_capabilities, |ck| {
                    ck == CapabilityKind::Read
                })
            };
            // let mut borrowed_read = {
            //     let borrow_capabilities = borrows_state.capabilities();
            //     filter_borrowed_places_by_capability(borrow_capabilities, |ck| ck == CapabilityKind::Read)
            // };
            // owned_read.extend(borrowed_read.drain());
            owned_read
        };

        let repacker = PlaceRepacker::new(body, tcx);

        read_only_in_curr
            .iter()
            .filter(|place| has_named_local(**place, repacker))
            .filter(|place| read_only_in_next.contains(place))
            .flat_map(|place| {
                let mut mutant_body = body.clone();
                let region = Region::new_var(tcx, RegionVid::MAX);

                let read_only_place = PlaceRef::from(**place).to_place(tcx);

                let read_only_place_ty =
                    Ty::new_mut_ref(tcx, region, read_only_place.ty(&body.local_decls, tcx).ty);

                let fresh_local = fresh_local(&mut mutant_body, read_only_place_ty);

                let statement_index = curr.location.statement_index;
                let bb_index = curr.location.block;
                let bb = mutant_body.basic_blocks_mut().get_mut(bb_index)?;
                let statement_source_info = bb.statements.get(statement_index)?.source_info;

                let default_mut_borrow = BorrowKind::Mut {
                    kind: MutBorrowKind::Default,
                };
                let new_borrow = Statement {
                    source_info: statement_source_info,
                    kind: StatementKind::Assign(Box::new((
                        MirPlace::from(fresh_local),
                        Rvalue::Ref(region, default_mut_borrow, read_only_place),
                    ))),
                };
                let info = format!(
                    "{:?} was read-only, so inserted {:?}",
                    read_only_place, &new_borrow
                );
                bb.statements.insert(statement_index + 1, new_borrow);

                let borrow_loc = MutantLocation {
                    basic_block: curr.location.block.index(),
                    statement_index: statement_index + 1,
                };

                Some(Mutant {
                    body: mutant_body,
                    range: MutantRange {
                        start: borrow_loc.clone(),
                        end: borrow_loc,
                    },
                    info: info,
                })
            })
            .collect()
    }

    fn run_ratio(&mut self) -> (u32, u32) {
        (1, 1)
    }

    fn name(&mut self) -> String {
        "mutably-lend-read".into()
    }
}
