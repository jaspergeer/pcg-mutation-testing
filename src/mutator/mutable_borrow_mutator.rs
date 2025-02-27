use super::mutator_impl::Mutator;
use super::mutator_impl::Mutant;
use super::mutator_impl::MutantLocation;

use std::collections::VecDeque;
use std::collections::HashSet;

use crate::rustc_interface::middle::ty::Ty;
use crate::rustc_interface::middle::ty::TyCtxt;
use crate::rustc_interface::middle::ty::Region;
use crate::rustc_interface::middle::ty::RegionKind;
use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::PlaceRef;
use crate::rustc_interface::middle::mir::BorrowKind;
use crate::rustc_interface::middle::mir::MutBorrowKind;
use crate::rustc_interface::middle::mir::Local;
use crate::rustc_interface::middle::mir::LocalDecl;
use crate::rustc_interface::middle::mir::Statement;
use crate::rustc_interface::middle::mir::StatementKind;
use crate::rustc_interface::middle::mir::Rvalue;
use crate::rustc_interface::middle::mir::Place as MirPlace;

use crate::rustc_interface::data_structures::fx::FxHashSet;

use pcs::free_pcs::PcgBasicBlock;
use pcs::free_pcs::PcgLocation;

use pcs::combined_pcs::PCGNode;
use pcs::combined_pcs::PCGNodeLike;

use pcs::utils::PlaceRepacker;
use pcs::utils::maybe_remote::MaybeRemotePlace;
use pcs::utils::maybe_old::MaybeOldPlace;

use pcs::borrow_pcg::borrow_pcg_edge::BorrowPCGEdgeLike;
use pcs::borrow_pcg::edge::kind::BorrowPCGEdgeKind;
use pcs::borrow_pcg::edge_data::EdgeData;

pub struct MutableBorrowMutator;

impl Mutator for MutableBorrowMutator {
    fn generate_mutants<'tcx>(&mut self, tcx: &TyCtxt<'tcx>, fpcs_bb: &PcgBasicBlock<'tcx>, body: &Body<'tcx>) -> Vec<Mutant<'tcx>> {

        fn current_place_of_node<'tcx>(tcx: &TyCtxt<'tcx>, node: PCGNode<'tcx>) -> Option<MirPlace<'tcx>> {
            match node {
                PCGNode::Place(maybe_remote_place) =>
                    match maybe_remote_place {
                        MaybeRemotePlace::Local(maybe_old_place) => {
                            match maybe_old_place {
                                MaybeOldPlace::Current { place } =>
                                    Some(PlaceRef::from(place).to_place(*tcx)),
                                _ => None
                            }
                        },
                        _ => None
                    },
                _ => None
            }
        }

        fn generate_mutants_location<'mir, 'tcx>(tcx: &TyCtxt<'tcx>, body: &Body<'tcx>, location: &PcgLocation<'tcx>) -> Vec<Mutant<'tcx>> {

            let borrows_state = location.borrows.post_main();
            let borrows_graph = borrows_state.graph();
            let repacker = PlaceRepacker::new(body, *tcx);

            let leaf_edges = borrows_graph.frozen_graph().leaf_edges(repacker);
            let mut to_visit = leaf_edges.iter()
                                         .flat_map(|edge| match edge.kind() {
                                             BorrowPCGEdgeKind::Borrow(borrow_edge) =>
                                                 if borrow_edge.is_mut() {
                                                    edge.blocked_nodes(repacker)
                                                 } else {
                                                    FxHashSet::default()
                                                 },
                                             _ => FxHashSet::default()
                                         })
                                         .collect::<VecDeque<_>>();
            let mut visited = HashSet::new();
            let mut mutably_lent_places = HashSet::new();

            while let Some(curr) = to_visit.pop_front() {
                if !visited.contains(&curr) {
                    if let Some(place) = current_place_of_node(tcx, curr) {
                        mutably_lent_places.insert(place);
                        // TODO I don't think we record places in the owned PCG...
                    }

                    if let Some(local_node) = curr.try_to_local_node() {
                        let children = borrows_graph.edges_blocked_by(local_node, repacker).flat_map(|edge| {
                            edge.blocked_nodes(repacker)
                        });
                        for child in children {
                            to_visit.push_back(child);
                        }
                        visited.insert(curr);
                    }
                }
            }

            for place in mutably_lent_places.iter() {
                println!("{:?} is mutably lent", place)
            }

            mutably_lent_places.iter().flat_map(|place| {
                let mut mutant_body = body.clone();

                let fresh_local = Local::from_usize(mutant_body.local_decls.len());
                let erased_region = Region::new_from_kind(*tcx, RegionKind::ReErased);

                let borrow_ty = Ty::new_mut_ref(*tcx, erased_region, place.ty(&body.local_decls, *tcx).ty);

                let bb_index = location.location.block;
                let statement_index = location.location.statement_index;
                let bb = mutant_body.basic_blocks_mut().get_mut(bb_index)?;
                let statement_source_info = bb.statements.get(statement_index)?.source_info;

                let default_mut_borrow = BorrowKind::Mut { kind: MutBorrowKind::Default };
                let new_borrow = Statement {
                    source_info: statement_source_info,
                    kind: StatementKind::Assign(Box::new((MirPlace::from(fresh_local), Rvalue::Ref(erased_region, default_mut_borrow, *place))))
                };
                let mention_local = Statement {
                    source_info: statement_source_info,
                    kind: StatementKind::PlaceMention(Box::new(MirPlace::from(fresh_local)))
                };

                bb.statements.insert(statement_index, new_borrow);
                bb.statements.insert(bb.statements.len(), mention_local);

                let fresh_local_decl = LocalDecl::with_source_info(borrow_ty, statement_source_info);
                mutant_body.local_decls.raw.insert(fresh_local.index(), fresh_local_decl);
                // TODO also emit mutant w/ immutable reference to place

                let mutant_loc = MutantLocation {
                    basic_block: location.location.block.index(),
                    statement_index: location.location.statement_index
                };

                Some(Mutant { body: mutant_body, location: mutant_loc, info: "TODO".into() })
            }).collect()
        }

        fpcs_bb.statements.iter().flat_map(|statement| {
            generate_mutants_location(tcx, body, statement)
        }).collect()
    }

    fn run_ratio(&mut self) -> (u32, u32) { (1, 1) }

    fn name(&mut self) -> String {
        "mutably-lent-detector".into()
    }
}
