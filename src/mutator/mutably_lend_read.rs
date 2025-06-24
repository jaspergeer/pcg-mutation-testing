use super::utils::fresh_local;
use super::utils::has_named_local;

use super::mutator_impl::Mutant;
use super::mutator_impl::MutantLocation;
use super::mutator_impl::MutantRange;
use super::mutator_impl::PeepholeMutator;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::BorrowKind;
use crate::rustc_interface::middle::mir::MutBorrowKind;
use crate::rustc_interface::middle::mir::Place as MirPlace;
use crate::rustc_interface::middle::mir::PlaceRef;
use crate::rustc_interface::middle::mir::Rvalue;
use crate::rustc_interface::middle::mir::Statement;
use crate::rustc_interface::middle::mir::StatementKind;
use crate::rustc_interface::middle::ty::Region;
use crate::rustc_interface::middle::ty::RegionVid;
use crate::rustc_interface::middle::ty::Ty;

use pcg::free_pcs::CapabilityKind;
use pcg::free_pcs::PcgLocation;
use pcg::pcg::EvalStmtPhase;

use pcg::utils::CompilerCtxt;

pub struct MutablyLendReadOnly;

impl PeepholeMutator for MutablyLendReadOnly {
    fn generate_mutants<'mir, 'tcx>(
        ctx: CompilerCtxt<'mir, 'tcx>,
        body: &Body<'tcx>,
        curr: &PcgLocation<'tcx>,
        next: &PcgLocation<'tcx>,
    ) -> Vec<Mutant<'tcx>> {
        let read_only_in_curr: Vec<_> =
            curr.states[EvalStmtPhase::PostMain]
            .capabilities()
            .iter()
            .filter_map(|(place, ck)|
                        match ck {
                            CapabilityKind::Read => Some(place),
                            _ => None,
                        })
            .collect();

        let read_only_in_next: Vec<_> =
            next.states[EvalStmtPhase::PostOperands]
            .capabilities()
            .iter()
            .filter_map(|(place, ck)|
                        match ck {
                            CapabilityKind::Read => Some(place),
                            _ => None,
                        })
            .collect();

        read_only_in_curr
            .iter()
            .filter(|place| has_named_local(**place, body))
            .filter(|place| read_only_in_next.contains(place))
            .flat_map(|place| {
                let mut mutant_body = body.clone();
                let region = Region::new_var(ctx.tcx(), RegionVid::MAX);

                let read_only_place = PlaceRef::from(**place).to_place(ctx.tcx());

                let read_only_place_ty =
                    Ty::new_mut_ref(ctx.tcx(), region, read_only_place.ty(&body.local_decls, ctx.tcx()).ty);

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
