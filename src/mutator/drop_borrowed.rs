use super::utils::borrowed_places;
use super::utils::bogus_source_info;
use super::utils::fresh_basic_block;

use std::collections::HashSet;

use super::mutator_impl::Mutant;
use super::mutator_impl::MutantLocation;
use super::mutator_impl::MutantRange;
use super::mutator_impl::PeepholeMutator;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::PlaceRef;
use crate::rustc_interface::middle::mir::UnwindAction;
use crate::rustc_interface::middle::mir::Terminator;
use crate::rustc_interface::middle::mir::TerminatorKind;

use pcg::pcg::EvalStmtPhase;
use pcg::free_pcs::PcgLocation;
use pcg::utils::CompilerCtxt;

pub struct DropBorrowed;

impl PeepholeMutator for DropBorrowed {
    fn generate_mutants<'mir, 'tcx>(
        ctx: CompilerCtxt<'mir, 'tcx>,
        body: &Body<'tcx>,
        curr: &PcgLocation<'tcx>,
        next: &PcgLocation<'tcx>,
    ) -> Vec<Mutant<'tcx>> {
        let lent_in_curr = {
            let borrows_graph = curr.states[EvalStmtPhase::PostMain].borrow_pcg().graph();
            borrowed_places(borrows_graph, |_| true)
                .map(|(place, _)| place)
                .collect::<HashSet<_>>()
        };

        let lent_in_next = {
            let borrows_graph = curr.states[EvalStmtPhase::PostOperands].borrow_pcg().graph();
            borrowed_places(borrows_graph, |_| true)
                .map(|(place, _)| place)
                .collect::<HashSet<_>>()
        };

        lent_in_curr
            .iter()
            .filter(|place| lent_in_next.contains(place))
            .flat_map(|place| {
                let mut mutant_body = body.clone();
                let bogus_source_info = bogus_source_info(&mutant_body);
                let curr_bb_index = curr.location.block;
                let bb = mutant_body
                    .basic_blocks_mut()
                    .get_mut(curr_bb_index)
                    .unwrap();
                let mut tail_statements = bb
                    .statements
                    .drain(next.location.statement_index..)
                    .collect();

                let bb_terminator = bb.terminator.take();
                let tail_bb_index = fresh_basic_block(&mut mutant_body);
                let mut tail_bb = mutant_body
                    .basic_blocks_mut()
                    .get_mut(tail_bb_index)
                    .unwrap();
                tail_bb.statements.append(&mut tail_statements);
                tail_bb.terminator = bb_terminator;

                let lent_place = PlaceRef::from(**place).to_place(ctx.tcx());

                let bb = mutant_body
                    .basic_blocks_mut()
                    .get_mut(curr_bb_index)
                    .unwrap();
                bb.terminator = Some(Terminator {
                    source_info: bogus_source_info,
                    kind: TerminatorKind::Drop {
                        place: lent_place,
                        target: tail_bb_index,
                        unwind: UnwindAction::Continue,
                        replace: false,
                    },
                });

                let info = format!("{:?} was lent, so dropped it at index {:?}",
                                   lent_place,
                                   curr.location.statement_index);

                let borrow_loc = MutantLocation {
                    basic_block: curr.location.block.index(),
                    statement_index: curr.location.statement_index,
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
        "drop-borrowed".into()
    }
}
