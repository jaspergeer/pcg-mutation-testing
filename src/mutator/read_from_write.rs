use super::utils::fresh_local;
use super::utils::has_named_local;

use super::mutator_impl::Mutant;
use super::mutator_impl::MutantLocation;
use super::mutator_impl::MutantRange;
use super::mutator_impl::Mutation;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::FakeReadCause;
use crate::rustc_interface::middle::mir::Place as MirPlace;
use crate::rustc_interface::middle::mir::PlaceRef;
use crate::rustc_interface::middle::mir::Statement;
use crate::rustc_interface::middle::mir::StatementKind;
use crate::rustc_interface::middle::ty::Region;
use crate::rustc_interface::middle::ty::RegionKind;
use crate::rustc_interface::middle::ty::Ty;

use pcg::pcg::EvalStmtPhase;
use pcg::free_pcs::CapabilityKind;
use pcg::free_pcs::PcgLocation;
use pcg::utils::CompilerCtxt;

pub struct ReadFromWriteOnly;

impl Mutation for ReadFromWriteOnly {
    fn generate_mutants<'mir, 'tcx>(
        &self,
        ctx: CompilerCtxt<'mir, 'tcx>,
        body: &Body<'tcx>,
        curr: &PcgLocation<'tcx>,
        next: &PcgLocation<'tcx>,
    ) -> Vec<Mutant<'tcx>> {
        let write_only_in_curr: Vec<_> =
            curr.states[EvalStmtPhase::PostMain]
            .capabilities()
            .iter()
            .filter_map(|(place, ck)|
                        match ck {
                            CapabilityKind::Write => Some(place),
                            _ => None,
                        })
            .collect();

        let write_only_in_next: Vec<_> =
            next.states[EvalStmtPhase::PostOperands]
            .capabilities()
            .iter()
            .filter_map(|(place, ck)|
                        match ck {
                            CapabilityKind::Write => Some(place),
                            _ => None,
                        })
            .collect();

        write_only_in_curr
            .iter()
            .filter(|place| write_only_in_next.contains(place))
            .filter(|place| has_named_local(**place, body))
            .flat_map(|place| {
                let lent_place = PlaceRef::from(**place).to_place(ctx.tcx());
                let mut mutant_body = body.clone();

                let erased_region = Region::new_from_kind(ctx.tcx(), RegionKind::ReErased);
                let borrow_ty =
                    Ty::new_mut_ref(ctx.tcx(), erased_region, lent_place.ty(&body.local_decls, ctx.tcx()).ty);

                let fresh_local = fresh_local(&mut mutant_body, borrow_ty);

                let statement_index = curr.location.statement_index;
                let bb_index = curr.location.block;
                let bb = mutant_body.basic_blocks_mut().get_mut(bb_index)?;
                let statement_source_info = bb.statements.get(statement_index)?.source_info;

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

    fn name(&self) -> String {
        "read-from-write-only".into()
    }
}
