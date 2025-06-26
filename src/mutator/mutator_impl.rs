use serde::Serialize;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::BasicBlock;

use pcg::free_pcs::PcgLocation;
use pcg::utils::CompilerCtxt;
use pcg::PcgOutput;

use std::alloc::System;
use std::iter::Iterator;
use std::collections::VecDeque;

use tracing::info;

#[derive(Serialize, Clone, Debug)]
pub struct MutantLocation {
    pub basic_block: usize,
    pub statement_index: usize,
}

#[derive(Serialize, Clone, Debug)]
pub struct MutantRange {
    pub start: MutantLocation,
    pub end: MutantLocation,
}

pub struct Mutant<'tcx> {
    pub body: Body<'tcx>,
    pub range: MutantRange,
    pub info: String,
}

// A Mutation uses a MIR body and the analyses for two consecutive
// statements to produce a set of mutant MIR bodies.
pub trait Mutation {
    fn generate_mutants<'mir, 'tcx>(
        &self,
        ctx: CompilerCtxt<'mir, 'tcx>,
        body: &Body<'tcx>,
        curr: &PcgLocation<'tcx>,
        next: &PcgLocation<'tcx>,
    ) -> Vec<Mutant<'tcx>>;
    fn name(&self) -> String;
}

// A Mutator is instantiated with a Mutation, a MIR body, and a corresponding
// PCG analysis. It can be repeatedly queried for new mutants until it has finished
// traversing the entire MIR body.
pub struct Mutator<'a, 'mir, 'tcx> {
    mutation: &'a Box<dyn Mutation>,
    ctx: CompilerCtxt<'mir, 'tcx>,
    analysis: &'a mut PcgOutput<'mir, 'tcx, System>,
    body: &'a Body<'tcx>,
    mutants: VecDeque<Mutant<'tcx>>,
    basic_blocks: VecDeque<BasicBlock>,
    stmt_idx: usize,
}

impl<'a, 'mir, 'tcx> Mutator<'a, 'mir, 'tcx>{
    pub fn new(
        mutation: &'a Box<dyn Mutation>,
        ctx: CompilerCtxt<'mir, 'tcx>,
        analysis: &'a mut PcgOutput<'mir, 'tcx, System>,
        body: &'a Body<'tcx>,
    ) -> Self {
        let basic_blocks = body.basic_blocks.indices().collect();
        Self {
            mutation,
            ctx,
            analysis,
            body,
            mutants: VecDeque::new(),
            basic_blocks,
            stmt_idx: 0,
        }
    }

    pub fn name(&self) -> String {
        self.mutation.name()
    }

    // Return the next mutant that can be generated from this body
    pub fn next(&mut self) -> Option<Mutant<'tcx>> {
        let mut curr: Option<&PcgLocation<'_>>;
        let mut next: Option<&PcgLocation<'_>>;
        let mut curr_bb: BasicBlock = *self.basic_blocks.front()?;

        // Advance the cursor until we generate some mutants or finish traversing
        // the MIR body
        while !self.basic_blocks.is_empty()
            && self.mutants.is_empty() {
            // Advance until the next basic block for which we have an analysis
            while self.analysis.get_all_for_bb(curr_bb).is_err() {
                curr_bb = self.basic_blocks.pop_front()?;
                self.stmt_idx = 0;
            }
            if let Ok(Some(pcg_bb)) = self.analysis.get_all_for_bb(curr_bb) {
                curr = pcg_bb.statements.get(self.stmt_idx);
                self.stmt_idx += 1;
                next = pcg_bb.statements.get(self.stmt_idx);
                if let Some(curr) = curr && let Some(next) = next {
                    self.mutants = self.mutation.generate_mutants(self.ctx, self.body, curr, next).into();
                } else {
                    self.basic_blocks.pop_front();
                }
            }
        }
        self.mutants.pop_front()
    }
}
