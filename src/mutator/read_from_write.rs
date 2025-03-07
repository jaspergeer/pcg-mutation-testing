use super::utils::filter_borrowed_places_by_capability;
use super::utils::filter_owned_places_by_capability;
use super::utils::pcg_node_to_current_place;
use super::utils::fresh_local;

use super::mutator_impl::Mutant;
use super::mutator_impl::MutantLocation;
use super::mutator_impl::MutantRange;
use super::mutator_impl::PeepholeMutator;

use std::collections::HashSet;
use std::collections::VecDeque;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::BorrowKind;
use crate::rustc_interface::middle::mir::FakeReadCause;
use crate::rustc_interface::middle::mir::Local;
use crate::rustc_interface::middle::mir::LocalDecl;
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

pub struct ReadFromWriteOnly;

impl PeepholeMutator for ReadFromWriteOnly {
    fn generate_mutants<'mir, 'tcx>(
        tcx: &TyCtxt<'tcx>,
        body: &Body<'tcx>,
        curr: &PcgLocation<'tcx>,
        next: &PcgLocation<'tcx>,
    ) -> Vec<Mutant<'tcx>> {
        let repacker = PlaceRepacker::new(body, *tcx);

        let write_only_in_curr = {
            let borrows_state = curr.borrows.post_main();
            let mut owned_write = {
                let owned_capabilities = curr.states.post_main();
                filter_owned_places_by_capability(&owned_capabilities, |ck| ck == CapabilityKind::Write)
            };
            let mut borrowed_write = {
                let borrow_capabilities = borrows_state.capabilities.as_ref();
                filter_borrowed_places_by_capability(&borrow_capabilities, |ck| ck == CapabilityKind::Write)
            };
            owned_write.extend(borrowed_write.drain());
            owned_write
        };

        let write_only_in_next = {
            let borrows_state = next.borrows.post_main();
            let mut owned_write = {
                let owned_capabilities = next.states.post_main();
                filter_owned_places_by_capability(&owned_capabilities, |ck| ck == CapabilityKind::Write)
            };
            let mut borrowed_write = {
                let borrow_capabilities = borrows_state.capabilities.as_ref();
                filter_borrowed_places_by_capability(&borrow_capabilities, |ck| ck == CapabilityKind::Write)
            };
            owned_write.extend(borrowed_write.drain());
            owned_write
        };

        write_only_in_curr
            .iter()
            .filter(|place| write_only_in_next.contains(place))
            .flat_map(|place| {
                let lent_place = PlaceRef::from(**place).to_place(*tcx);
                let mut mutant_body = body.clone();

                let erased_region = Region::new_from_kind(*tcx, RegionKind::ReErased);
                let borrow_ty = Ty::new_mut_ref(
                    *tcx,
                    erased_region,
                    lent_place.ty(&body.local_decls, *tcx).ty,
                );

                let fresh_local = fresh_local(&mut mutant_body, borrow_ty);

                let statement_index = curr.location.statement_index;
                let bb_index = curr.location.block;
                let bb = mutant_body.basic_blocks_mut().get_mut(bb_index)?;
                let statement_source_info = bb.statements.get(statement_index)?.source_info;

                let default_mut_borrow = BorrowKind::Mut {
                    kind: MutBorrowKind::Default,
                };
                let new_read = Statement {
                    source_info: statement_source_info,
                    kind: StatementKind::FakeRead(Box::new((
                        FakeReadCause::ForLet(None),
                        MirPlace::from(fresh_local),
                    ))),
                };
                let info = format!(
                    "{:?} was write-only, so inserted {:?}",
                    lent_place, &new_read
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
        "read-from-write-only".into()
    }
}
