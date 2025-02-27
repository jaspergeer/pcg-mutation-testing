use serde::Serialize;

use crate::rustc_interface::middle::ty::TyCtxt;
use crate::rustc_interface::middle::mir::Body;
use pcs::free_pcs::PcgBasicBlock;

#[derive(Serialize)]
pub struct MutantLocation {
    pub basic_block: usize,
    pub statement_index: usize
}

pub struct Mutant<'tcx> {
    pub body: Body<'tcx>,
    pub location: MutantLocation,
    pub info: String
}

pub trait Mutator {
    fn generate_mutants<'tcx>(&mut self, tcx: &TyCtxt<'tcx>, fpcs_bb: &PcgBasicBlock<'tcx>, body: &Body<'tcx>) -> Vec<Mutant<'tcx>>;
    fn run_ratio(&mut self) -> (u32, u32);
    fn name(&mut self) -> String;
}
