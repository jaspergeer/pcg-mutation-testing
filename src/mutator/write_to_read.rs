use super::utils::bogus_source_info;
use super::utils::has_named_local;

use super::mutator_impl::Mutant;
use super::mutator_impl::MutantLocation;
use super::mutator_impl::MutantRange;
use super::mutator_impl::PeepholeMutator;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::PlaceRef;
use crate::rustc_interface::middle::mir::Rvalue;
use crate::rustc_interface::middle::mir::Statement;
use crate::rustc_interface::middle::mir::StatementKind;

use pcg::free_pcs::CapabilityKind;
use pcg::free_pcs::PcgLocation;
use pcg::pcg::EvalStmtPhase;
use pcg::utils::CompilerCtxt;

pub struct WriteToReadOnly;

impl PeepholeMutator for WriteToReadOnly {
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
                let read_only_place = PlaceRef::from(**place).to_place(ctx.tcx());
                let mut mutant_body = body.clone();

                let statement_index = curr.location.statement_index;

                let new_assign = Statement {
                    source_info: bogus_source_info(&mutant_body),
                    kind: StatementKind::Assign(Box::new((
                        read_only_place,
                        Rvalue::Len(read_only_place),
                    ))),
                };
                let info = format!(
                    "{:?} was read-only, so inserted {:?}",
                    read_only_place, &new_assign
                );

                let bb_index = curr.location.block;
                let bb = mutant_body.basic_blocks_mut().get_mut(bb_index)?;
                bb.statements.insert(statement_index + 1, new_assign);

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

    fn run_ratio(&mut self) -> (u32, u32) {
        (1, 1)
    }

    fn name(&mut self) -> String {
        "write-to-read-only".into()
    }
}
