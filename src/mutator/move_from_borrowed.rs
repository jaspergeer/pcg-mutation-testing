use super::utils::borrowed_places;
use super::utils::fresh_local;
use super::utils::has_named_local;
use super::utils::is_mut;

use std::collections::HashSet;

use super::mutator_impl::Mutant;
use super::mutator_impl::MutantLocation;
use super::mutator_impl::MutantRange;
use super::mutator_impl::Mutation;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::Operand;
use crate::rustc_interface::middle::mir::Place as MirPlace;
use crate::rustc_interface::middle::mir::PlaceRef;
use crate::rustc_interface::middle::mir::Rvalue;
use crate::rustc_interface::middle::mir::Statement;
use crate::rustc_interface::middle::mir::StatementKind;

use pcg::pcg::EvalStmtPhase;
use pcg::free_pcs::PcgLocation;
use pcg::utils::CompilerCtxt;

// `MoveFromBorrowed` creates mutants which move out of a place behind a mutable borrow
pub struct MoveFromBorrowed;

impl Mutation for MoveFromBorrowed {
    fn generate_mutants<'mir, 'tcx>(
        &self,
        ctx: CompilerCtxt<'mir, 'tcx>,
        body: &Body<'tcx>,
        curr: &PcgLocation<'tcx>,
        next: &PcgLocation<'tcx>,
    ) -> Vec<Mutant<'tcx>> {
        let lent_in_curr = {
            let borrows_graph = curr.states[EvalStmtPhase::PostMain].borrow_pcg().graph();
            borrowed_places(borrows_graph, is_mut)
                .map(|(place, _)| place)
                .collect::<HashSet<_>>()
        };

        let lent_in_next = {
            let borrows_graph = next.states[EvalStmtPhase::PostOperands].borrow_pcg().graph();
            borrowed_places(borrows_graph, is_mut)
                .map(|(place, _)| place)
                .collect::<HashSet<_>>()
        };

        // We consider only places lent at the `PostMain` of `curr` and `PostOperands` of `next`
        // because borrows are killed only at the `PostOperands` phase.
        lent_in_curr
            .iter()
            .filter(|place| lent_in_next.contains(place))
            .filter(|place| has_named_local(**place, body))
            .flat_map(|place| {
                let mut mutant_body = body.clone();
                let lent_place = PlaceRef::from(**place).to_place(ctx.tcx());

                let lent_place_ty = lent_place.ty(&body.local_decls, ctx.tcx()).ty;

                let fresh_local = fresh_local(&mut mutant_body, lent_place_ty);

                let statement_index = curr.location.statement_index;
                let bb_index = curr.location.block;
                let bb = mutant_body.basic_blocks_mut().get_mut(bb_index)?;
                let statement_source_info = bb.statements.get(statement_index)?.source_info;

                // Statement that moves `lent_place` into a `fresh_local`
                let new_move = Statement {
                    source_info: statement_source_info,
                    kind: StatementKind::Assign(Box::new((
                        MirPlace::from(fresh_local),
                        Rvalue::Use(Operand::Move(lent_place)),
                    ))),
                };
                let info = format!("{:?} was lent, so inserted {:?}", lent_place, &new_move);
                // Insert `new_move` between `curr` and `next`
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
                    info,
                })
            })
            .collect()
    }

    fn name(&self) -> String {
        "move-from-borrowed".into()
    }
}
