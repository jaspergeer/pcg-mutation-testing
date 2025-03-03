use serde::Serialize;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::ty::TyCtxt;

use pcs::free_pcs::PcgBasicBlock;
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
        tcx: &TyCtxt<'tcx>,
        analysis: &mut FpcsOutput<'mir, 'tcx>,
        body: &Body<'tcx>,
    ) -> Vec<Mutant<'tcx>>;
    fn run_ratio(&mut self) -> (u32, u32);
    fn name(&mut self) -> String;
}
