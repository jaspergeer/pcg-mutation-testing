use super::utils::borrowed_places;
use super::utils::fresh_local;
use super::utils::is_shared;
use super::utils::has_named_local;

use std::collections::HashSet;

use super::mutator_impl::Mutant;
use super::mutator_impl::MutantLocation;
use super::mutator_impl::MutantRange;
use super::mutator_impl::Mutation;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::BorrowKind;
use crate::rustc_interface::middle::mir::MutBorrowKind;
use crate::rustc_interface::middle::mir::Place as MirPlace;
use crate::rustc_interface::middle::mir::PlaceRef;
use crate::rustc_interface::middle::mir::Rvalue;
use crate::rustc_interface::middle::mir::Statement;
use crate::rustc_interface::middle::mir::StatementKind;
use crate::rustc_interface::middle::ty::Ty;

use pcg::pcg::EvalStmtPhase;
use pcg::free_pcs::PcgLocation;
use pcg::utils::CompilerCtxt;

// MutablyLendShared creates mutants which mutably borrow a place behind a shared borrow
pub struct MutablyLendShared;

impl Mutation for MutablyLendShared {
    fn generate_mutants<'mir, 'tcx>(
        &self,
        ctx: CompilerCtxt<'mir, 'tcx>,
        body: &Body<'tcx>,
        curr: &PcgLocation<'tcx>,
        next: &PcgLocation<'tcx>,
    ) -> Vec<Mutant<'tcx>> {
        let immutably_lent_in_curr = {
            let borrows_graph = curr.states[EvalStmtPhase::PostMain].borrow_pcg().graph();
            borrowed_places(borrows_graph, is_shared)
        };

        let immutably_lent_in_next = {
            let borrows_graph = next.states[EvalStmtPhase::PostOperands].borrow_pcg().graph();
            borrowed_places(borrows_graph, is_shared)
                .map(|(place, _)| place)
                .collect::<HashSet<_>>()
        };

        // We consider only places lent at the PostMain of `curr` and PostOperands of `next`
        // because borrows are killed only at the PostOperands phase.
        immutably_lent_in_curr
            .filter(|(place, _)| immutably_lent_in_next.contains(place))
            .filter(|(place, _)| has_named_local(*place, body))
            .flat_map(|(place, region)| {
                let lent_place = PlaceRef::from(*place).to_place(ctx.tcx());
                let mut mutant_body = body.clone();

                let borrow_ty =
                    Ty::new_mut_ref(ctx.tcx(), region, lent_place.ty(&body.local_decls, ctx.tcx()).ty);

                let fresh_local = fresh_local(&mut mutant_body, borrow_ty);

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
                        Rvalue::Ref(region, default_mut_borrow, lent_place),
                    ))),
                };
                let info = format!(
                    "{:?} was immutably lent, so inserted {:?}",
                    lent_place, &new_borrow
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
                    info,
                })
            })
            .collect()
    }

    fn name(&self) -> String {
        "mutably-lend-shared".into()
    }
}
