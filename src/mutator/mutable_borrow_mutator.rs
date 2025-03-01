use super::mutator_impl::Mutant;
use super::mutator_impl::MutantLocation;
use super::mutator_impl::MutantRange;
use super::mutator_impl::Mutator;

use std::collections::HashSet;
use std::collections::VecDeque;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::BorrowKind;
use crate::rustc_interface::middle::mir::Local;
use crate::rustc_interface::middle::mir::LocalDecl;
use crate::rustc_interface::middle::mir::MutBorrowKind;
use crate::rustc_interface::middle::mir::Place as MirPlace;
use crate::rustc_interface::middle::mir::PlaceRef;
use crate::rustc_interface::middle::mir::Rvalue;
use crate::rustc_interface::middle::mir::Statement;
use crate::rustc_interface::middle::mir::StatementKind;
use crate::rustc_interface::middle::ty::Region;
use crate::rustc_interface::middle::ty::RegionKind;
use crate::rustc_interface::middle::ty::Ty;
use crate::rustc_interface::middle::ty::TyCtxt;

use crate::rustc_interface::data_structures::fx::FxHashSet;

use pcs::FpcsOutput;

use pcs::free_pcs::PcgBasicBlock;
use pcs::free_pcs::PcgLocation;

use pcs::combined_pcs::PCGNode;
use pcs::combined_pcs::PCGNodeLike;

use pcs::utils::maybe_old::MaybeOldPlace;
use pcs::utils::maybe_remote::MaybeRemotePlace;
use pcs::utils::PlaceRepacker;

use pcs::borrow_pcg::borrow_pcg_edge::BorrowPCGEdgeLike;
use pcs::borrow_pcg::edge::kind::BorrowPCGEdgeKind;
use pcs::borrow_pcg::edge_data::EdgeData;
use pcs::borrow_pcg::graph::BorrowsGraph;

pub struct MutableBorrowMutants;

pub struct MutableBorrowMutator;

impl Mutator for MutableBorrowMutator {
    fn generate_mutants<'mir, 'tcx>(
        &mut self,
        tcx: &TyCtxt<'tcx>,
        analysis: &mut FpcsOutput<'mir, 'tcx>,
        body: &Body<'tcx>,
    ) -> Vec<Mutant<'tcx>> {
        fn node_into_current_place<'tcx>(
            tcx: &TyCtxt<'tcx>,
            node: PCGNode<'tcx>,
        ) -> Option<MirPlace<'tcx>> {
            match node {
                PCGNode::Place(maybe_remote_place) => match maybe_remote_place {
                    MaybeRemotePlace::Local(maybe_old_place) => match maybe_old_place {
                        MaybeOldPlace::Current { place } => {
                            Some(PlaceRef::from(place).to_place(*tcx))
                        }
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            }
        }

        fn mutably_lent_places<'mir, 'tcx>(
            graph: &BorrowsGraph<'tcx>,
            repacker: &PlaceRepacker<'mir, 'tcx>,
        ) -> HashSet<MirPlace<'tcx>> {
            let leaf_edges = graph.frozen_graph().leaf_edges(*repacker);
            let mut to_visit = leaf_edges
                .iter()
                .flat_map(|edge| match edge.kind() {
                    BorrowPCGEdgeKind::Borrow(borrow_edge) => {
                        if borrow_edge.is_mut() {
                            edge.blocked_nodes(*repacker)
                        } else {
                            FxHashSet::default()
                        }
                    }
                    _ => FxHashSet::default(),
                })
                .collect::<VecDeque<_>>();
            let mut visited = HashSet::new();
            let mut mutably_lent_places = HashSet::new();

            while let Some(curr) = to_visit.pop_front() {
                if !visited.contains(&curr) {
                    if let Some(place) = node_into_current_place(&(*repacker).tcx(), curr) {
                        mutably_lent_places.insert(place);
                    }

                    if let Some(local_node) = curr.try_to_local_node() {
                        let children = graph
                            .edges_blocked_by(local_node, *repacker)
                            .flat_map(|edge| edge.blocked_nodes(*repacker));
                        for child in children {
                            to_visit.push_back(child);
                        }
                        visited.insert(curr);
                    }
                }
            }
            mutably_lent_places
        }

        fn generate_mutants_for_bb<'mir, 'tcx>(
            tcx: &TyCtxt<'tcx>,
            body: &Body<'tcx>,
            analysis: &mut FpcsOutput<'mir, 'tcx>,
            pcg_bb: &PcgBasicBlock<'tcx>,
        ) -> Vec<Mutant<'tcx>> {
            pcg_bb
                .statements
                .iter()
                .enumerate()
                .flat_map(|(i, loc)| {
                    let successors = if let Some(successor) = pcg_bb.statements.get(i + 1) {
                        vec![successor]
                    } else {
                        pcg_bb.terminator.succs.iter().collect()
                    };

                    generate_mutants_for_location(tcx, body, loc, &successors)
                })
                .collect::<Vec<_>>()
        }

        fn generate_mutants_for_location<'mir, 'tcx>(
            tcx: &TyCtxt<'tcx>,
            body: &Body<'tcx>,
            loc: &PcgLocation<'tcx>,
            successors: &Vec<&PcgLocation<'tcx>>,
        ) -> Vec<Mutant<'tcx>> {
            let repacker = PlaceRepacker::new(body, *tcx);

            let loc_mutably_lent = {
                let borrows_state = loc.borrows.post_main();
                let borrows_graph = borrows_state.graph();
                mutably_lent_places(&borrows_graph, &repacker)
            };

            let succ_mutably_lent = successors
                .iter()
                .flat_map(|loc| {
                    let borrows_state = loc.borrows.post_main();
                    let borrows_graph = borrows_state.graph();
                    mutably_lent_places(&borrows_graph, &repacker)
                })
                .collect::<HashSet<_>>();

            loc_mutably_lent
                .iter()
                .filter(|loc| succ_mutably_lent.contains(loc))
                .flat_map(|place| {
                    let mut mutant_body = body.clone();

                    let fresh_local = Local::from_usize(mutant_body.local_decls.len());
                    let erased_region = Region::new_from_kind(*tcx, RegionKind::ReErased);

                    let borrow_ty =
                        Ty::new_mut_ref(*tcx, erased_region, place.ty(&body.local_decls, *tcx).ty);

                    let bb_index = loc.location.block;
                    let statement_index = loc.location.statement_index;
                    let bb = mutant_body.basic_blocks_mut().get_mut(bb_index)?;
                    let statement_source_info = bb.statements.get(statement_index)?.source_info;

                    let default_mut_borrow = BorrowKind::Mut {
                        kind: MutBorrowKind::Default,
                    };
                    let new_borrow = Statement {
                        source_info: statement_source_info,
                        kind: StatementKind::Assign(Box::new((
                            MirPlace::from(fresh_local),
                            Rvalue::Ref(erased_region, default_mut_borrow, *place),
                        ))),
                    };

                    let info =
                        format!("{:?} was mutably lent, so inserted {:?}", place, new_borrow);

                    bb.statements.insert(statement_index + 1, new_borrow);

                    let fresh_local_decl =
                        LocalDecl::with_source_info(borrow_ty, statement_source_info);
                    mutant_body
                        .local_decls
                        .raw
                        .insert(fresh_local.index(), fresh_local_decl);
                    // TODO also emit mutant w/ immutable reference to place

                    let mutant_loc = MutantLocation {
                        basic_block: loc.location.block.index(),
                        statement_index: loc.location.statement_index,
                    };

                    Some(Mutant {
                        body: mutant_body,
                        range: MutantRange {
                            start: mutant_loc.clone(),
                            end: mutant_loc,
                        },
                        info: info,
                    })
                })
                .collect()
        }

        body.basic_blocks
            .indices()
            .flat_map(|bb_index| match analysis.get_all_for_bb(bb_index) {
                Ok(maybe_pcg_bb) => {
                    maybe_pcg_bb.map(|pcg_bb| generate_mutants_for_bb(tcx, body, analysis, &pcg_bb))
                }
                _ => None,
            })
            .flatten()
            .collect()
    }

    fn run_ratio(&mut self) -> (u32, u32) {
        (1, 1)
    }

    fn name(&mut self) -> String {
        "mutably-lent-detector".into()
    }
}
