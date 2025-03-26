use super::utils::borrowed_places;
use super::utils::filter_borrowed_places_by_capability;
use super::utils::filter_owned_places_by_capability;
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

pub struct MoveFromBorrowed;

impl PeepholeMutator for MoveFromBorrowed {
    fn generate_mutants<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        curr: &PcgLocation<'tcx>,
        next: &PcgLocation<'tcx>,
    ) -> Vec<Mutant<'tcx>> {
        let lent_in_curr = {
            let borrows_graph = curr.borrows.post_main().graph();
            borrowed_places(borrows_graph, is_mut)
                .map(|(place, _)| place)
                .collect::<HashSet<_>>()
        };

        let lent_in_next = {
            let borrows_graph = next.borrows.post_operands().graph();
            borrowed_places(borrows_graph, is_mut)
                .map(|(place, _)| place)
                .collect::<HashSet<_>>()
        };

        // let mut initialized_places = {
        //     let repacker = PlaceRepacker::new(body, tcx);
        //     let mut owned_init: HashSet<_> = {
        //         let owned_capabilities = next.states.post_operands();
        //         filter_owned_places_by_capability(&owned_capabilities, repacker, |ck| {
        //             !ck.iter().any(|c| c.is_write())
        //         })
        //     };
        //     let mut borrowed_init = {
        //         let borrows_state = next.borrows.post_operands();
        //         filter_borrowed_places_by_capability(&borrows_state, repacker, |ck| {
        //             !ck.iter().any(|c| c.is_write())
        //         })
        //     };
        //     owned_init.extend(borrowed_init.drain());
        //     owned_init
        // };

        lent_in_curr
            .iter()
            .filter(|place| lent_in_next.contains(place))
            // .filter(|place| initialized_places.contains(place))
            .filter(|place| has_named_local(**place, body))
            .flat_map(|place| {
                let mut mutant_body = body.clone();
                let lent_place = PlaceRef::from(**place).to_place(tcx);

                let lent_place_ty = lent_place.ty(&body.local_decls, tcx).ty;

                let fresh_local = fresh_local(&mut mutant_body, lent_place_ty);

                let statement_index = curr.location.statement_index;
                let bb_index = curr.location.block;
                let bb = mutant_body.basic_blocks_mut().get_mut(bb_index)?;
                let statement_source_info = bb.statements.get(statement_index)?.source_info;

                let new_move = Statement {
                    source_info: statement_source_info,
                    kind: StatementKind::Assign(Box::new((
                        MirPlace::from(fresh_local),
                        Rvalue::Use(Operand::Move(lent_place)),
                    ))),
                };
                let info = format!("{:?} was lent, so inserted {:?}", lent_place, &new_move);
                bb.statements.insert(statement_index + 1, new_move);

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
        "move-from-borrowed".into()
    }
}
