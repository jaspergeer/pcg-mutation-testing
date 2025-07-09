use serde::Serialize;

use crate::rustc_interface::middle::mir::BasicBlock;
use crate::rustc_interface::middle::mir::Body;

use pcg::free_pcs::PcgLocation;
use pcg::utils::CompilerCtxt;
use pcg::PcgOutput;

use std::alloc::System;
use std::collections::VecDeque;

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

// A `Mutant` is a MIR `Body` along with a description of the mutation performed
// and a source range describing where the mutation appears
pub struct Mutant<'tcx> {
    pub body: Body<'tcx>,
    pub range: MutantRange,
    pub info: String,
}

// A `Mutation` uses a MIR `Body` and the analyses for two consecutive
// statements to produce a set of mutant MIR `Body`s.
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

// A `Mutator` generates mutants for a MIR `Body` using a `Mutation`.
// It can be repeatedly queried for new mutants until it has finished traversing
// the entire `Body`.
pub struct Mutator<'a, 'mir, 'tcx> {
    mutation: &'a Box<dyn Mutation>,
    ctx: CompilerCtxt<'mir, 'tcx>,
    analysis: &'a mut PcgOutput<'mir, 'tcx, System>,
    body: &'a Body<'tcx>,
    mutants: VecDeque<Mutant<'tcx>>,
    basic_blocks: VecDeque<BasicBlock>,
    stmt_idx: usize,
}

impl<'a, 'mir, 'tcx> Mutator<'a, 'mir, 'tcx> {
    pub fn new(
        mutation: &'a Box<dyn Mutation>,
        ctx: CompilerCtxt<'mir, 'tcx>,
        analysis: &'a mut PcgOutput<'mir, 'tcx, System>,
        body: &'a Body<'tcx>,
    ) -> Self {
        Self {
            mutation,
            ctx,
            analysis,
            body,
            mutants: VecDeque::new(),
            basic_blocks: body.basic_blocks.indices().collect(),
            stmt_idx: 0,
        }
    }

    pub fn name(&self) -> String {
        self.mutation.name()
    }

    fn curr_bb(&self) -> Option<BasicBlock> {
        Some(*self.basic_blocks.front()?)
    }

    // Return the next `Mutant` that can be generated from this body
    pub fn next(&mut self) -> Option<Mutant<'tcx>> {
        // Seek until we generate some `Mutant`s or finish traversing
        // the body
        while !self.basic_blocks.is_empty() && self.mutants.is_empty() {
            let old_num_bb = self.basic_blocks.len();
            let old_stmt_idx = self.stmt_idx;
            // Seek until the next basic block for which we have an analysis
            let mut analysis = self.analysis.get_all_for_bb(self.curr_bb()?);
            while { analysis.is_err() || analysis.unwrap().is_none() } {
                self.basic_blocks.pop_front();
                self.stmt_idx = 0;
                analysis = self.analysis.get_all_for_bb(self.curr_bb()?);
            }
            if let Ok(Some(pcg_bb)) = self.analysis.get_all_for_bb(self.curr_bb()?) {
                if let Some(curr) = pcg_bb.statements.get(self.stmt_idx)
                    && let Some(next) = pcg_bb.statements.get(self.stmt_idx + 1)
                {
                    self.mutants = self
                        .mutation
                        .generate_mutants(self.ctx, self.body, curr, next)
                        .into();
                    self.stmt_idx += 1;
                } else {
                    self.basic_blocks.pop_front();
                    self.stmt_idx = 0;
                }
            } else {
                unreachable!()
            }
            // Sanity check for termination
            assert!(self.basic_blocks.len() < old_num_bb || self.stmt_idx > old_stmt_idx);
        }
        self.mutants.pop_front()
    }
}
