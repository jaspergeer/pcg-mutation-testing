use super::utils::bogus_source_info;
use super::utils::borrowed_places;
use super::utils::is_shared;
use super::utils::has_named_local;

use std::collections::HashSet;

use super::mutator_impl::Mutant;
use super::mutator_impl::MutantLocation;
use super::mutator_impl::MutantRange;
use super::mutator_impl::Mutation;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::PlaceRef;
use crate::rustc_interface::middle::mir::Rvalue;
use crate::rustc_interface::middle::mir::Statement;
use crate::rustc_interface::middle::mir::StatementKind;

use pcg::free_pcs::PcgLocation;
use pcg::pcg::EvalStmtPhase;
use pcg::utils::CompilerCtxt;

pub struct WriteToShared;

impl Mutation for WriteToShared {
    fn generate_mutants<'mir, 'tcx>(
        &self,
        ctx: CompilerCtxt<'mir, 'tcx>,
        body: &Body<'tcx>,
        curr: &PcgLocation<'tcx>,
        _next: &PcgLocation<'tcx>,
    ) -> Vec<Mutant<'tcx>> {
        let shared_in_curr = {
            let borrows_graph = curr.states[EvalStmtPhase::PostMain].borrow_pcg().graph();
            borrowed_places(borrows_graph, is_shared)
                .map(|(place, _)| place)
                .collect::<HashSet<_>>()
        };

        let shared_in_next = {
            let borrows_graph = curr.states[EvalStmtPhase::PostOperands].borrow_pcg().graph();
            borrowed_places(borrows_graph, is_shared)
        };

        shared_in_next
            .filter(|(place, _)| shared_in_curr.contains(place))
            .filter(|(place, _)| has_named_local(*place, body))
            .flat_map(|(place, _)| {
                let shared_place = PlaceRef::from(*place).to_place(ctx.tcx());
                let mut mutant_body = body.clone();

                let statement_index = curr.location.statement_index;

                let new_assign = Statement {
                    source_info: bogus_source_info(&mutant_body),
                    kind: StatementKind::Assign(Box::new((
                        shared_place,
                        Rvalue::Len(shared_place),
                    ))),
                };
                let info = format!(
                    "{:?} was shared, so inserted {:?}",
                    shared_place, &new_assign
                );

                let bb_index = curr.location.block;
                let bb = mutant_body.basic_blocks_mut().get_mut(bb_index)?;
                bb.statements.insert(statement_index + 1, new_assign);

                // TODO also emit mutant w/ immutable reference to place

                let borrow_loc = MutantLocation {
                    basic_block: curr.location.block.index(),
                    statement_index: statement_index + 1,
                };

                let mention_loc = MutantLocation {
                    basic_block: curr.location.block.index(),
                    statement_index: statement_index + 1,
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

    fn name(&self) -> String {
        "write-to-shared".into()
    }
}
