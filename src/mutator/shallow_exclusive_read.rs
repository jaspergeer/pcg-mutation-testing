use super::utils::filter_borrowed_places_by_capability;
use super::utils::filter_owned_places_by_capability;
use super::utils::fresh_local;

use super::mutator_impl::Mutant;
use super::mutator_impl::MutantLocation;
use super::mutator_impl::MutantRange;
use super::mutator_impl::PeepholeMutator;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::BorrowKind;
use crate::rustc_interface::middle::mir::FakeReadCause;
use crate::rustc_interface::middle::mir::MutBorrowKind;
use crate::rustc_interface::middle::mir::Place as MirPlace;
use crate::rustc_interface::middle::mir::PlaceElem as MirPlaceElem;
use crate::rustc_interface::middle::mir::PlaceRef;
use crate::rustc_interface::middle::mir::Statement;
use crate::rustc_interface::middle::mir::StatementKind;
use crate::rustc_interface::middle::ty::Region;
use crate::rustc_interface::middle::ty::RegionKind;
use crate::rustc_interface::middle::ty::Ty;
use crate::rustc_interface::middle::ty::TyCtxt;

use pcs::free_pcs::CapabilityKind;
use pcs::free_pcs::PcgLocation;
use pcs::utils::PlaceRepacker;

pub struct ShallowExclusiveRead;

impl PeepholeMutator for ShallowExclusiveRead {
    fn generate_mutants<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        curr: &PcgLocation<'tcx>,
        next: &PcgLocation<'tcx>,
    ) -> Vec<Mutant<'tcx>> {
        let shallow_exclusive_in_curr = {
            let repacker = PlaceRepacker::new(body, tcx);
            let mut owned_shallow_exclusive = {
                let owned_capabilities = curr.states.post_main();
                filter_owned_places_by_capability(&owned_capabilities, repacker, |ck| {
                    ck == Some(CapabilityKind::ShallowExclusive)
                })
            };
            let mut borrowed_shallow_exclusive = {
                let borrows_state = curr.borrows.post_main();
                filter_borrowed_places_by_capability(&borrows_state, repacker, |ck| {
                    ck == Some(CapabilityKind::ShallowExclusive)
                })
            };
            owned_shallow_exclusive.extend(borrowed_shallow_exclusive.drain());
            owned_shallow_exclusive
        };

        let shallow_exclusive_in_next = {
            let repacker = PlaceRepacker::new(body, tcx);
            let mut owned_shallow_exclusive = {
                let owned_capabilities = next.states.post_main();
                filter_owned_places_by_capability(&owned_capabilities, repacker, |ck| {
                    ck == Some(CapabilityKind::ShallowExclusive)
                })
            };
            let mut borrowed_shallow_exclusive = {
                let borrows_state = next.borrows.post_main();
                filter_borrowed_places_by_capability(&borrows_state, repacker, |ck| {
                    ck == Some(CapabilityKind::ShallowExclusive)
                })
            };
            owned_shallow_exclusive.extend(borrowed_shallow_exclusive.drain());
            owned_shallow_exclusive
        };

        shallow_exclusive_in_curr
            .iter()
            .filter(|place| shallow_exclusive_in_next.contains(place))
            .flat_map(|place| {
                let mut mutant_body = body.clone();

                // TODO the assumption here is that `shallow_exclusive_place` is a box
                // whose contents are uninitialized
                let shallow_exclusive_place = PlaceRef::from(**place).to_place(tcx);
                let write_only_subplace =
                    tcx.mk_place_elem(shallow_exclusive_place, MirPlaceElem::Deref);

                let statement_index = curr.location.statement_index;
                let bb_index = curr.location.block;
                let bb = mutant_body.basic_blocks_mut().get_mut(bb_index)?;
                let statement_source_info = bb.statements.get(statement_index)?.source_info;

                let new_read = Statement {
                    source_info: statement_source_info,
                    kind: StatementKind::FakeRead(Box::new((
                        FakeReadCause::ForLet(None),
                        write_only_subplace,
                    ))),
                };
                let info = format!(
                    "{:?} was ShallowExclusive, so inserted {:?}",
                    shallow_exclusive_place, &new_read
                );
                bb.statements.insert(statement_index + 1, new_read);

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
        "shallow-exclusive-read".into()
    }
}
