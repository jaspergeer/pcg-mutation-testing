use serde::Serialize;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::ty::TyCtxt;

use pcs::free_pcs::PcgBasicBlock;
use pcs::free_pcs::PcgLocation;
use pcs::FpcsOutput;

#[derive(Serialize, Clone)]
pub struct MutantLocation {
    pub basic_block: usize,
    pub statement_index: usize,
}

#[derive(Serialize, Clone)]
pub struct MutantRange {
    pub start: MutantLocation,
    pub end: MutantLocation,
}

pub struct Mutant<'tcx> {
    pub body: Body<'tcx>,
    pub range: MutantRange,
    pub info: String,
}

pub trait Mutator {
    fn generate_mutants<'mir, 'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        analysis: &mut FpcsOutput<'mir, 'tcx>,
        body: &Body<'tcx>,
    ) -> Vec<Mutant<'tcx>>;
    fn run_ratio(&mut self) -> (u32, u32);
    fn name(&mut self) -> String;
}

pub trait PeepholeMutator {
    fn generate_mutants<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        curr: &PcgLocation<'tcx>,
        next: &PcgLocation<'tcx>,
    ) -> Vec<Mutant<'tcx>>;
    fn run_ratio(&mut self) -> (u32, u32);
    fn name(&mut self) -> String;
}

impl<T: PeepholeMutator> Mutator for T {
    fn generate_mutants<'mir, 'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        analysis: &mut FpcsOutput<'mir, 'tcx>,
        body: &Body<'tcx>,
    ) -> Vec<Mutant<'tcx>> {
        body.basic_blocks
            .indices()
            .flat_map(|bb_index| {
                analysis.get_all_for_bb(bb_index).ok()?.map(|pcg_bb| {
                    pcg_bb
                        .statements
                        .iter()
                        .zip(pcg_bb.statements.iter().skip(1))
                        .flat_map(|(curr, next)| {
                            T::generate_mutants(tcx, body, curr, next)
                        })
                        .collect::<Vec<_>>()
                })
            })
            .flatten()
            .collect()
    }

    fn run_ratio(&mut self) -> (u32, u32) {
        T::run_ratio(self)
    }

    fn name(&mut self) -> String {
        T::name(self)
    }
}
