use std::collections::HashSet;

use pcs::borrow_pcg::borrow_pcg_capabilities::BorrowPCGCapabilities;
use pcs::borrow_pcg::region_projection::MaybeRemoteRegionProjectionBase;
use pcs::borrow_pcg::region_projection::RegionProjection;

use pcs::free_pcs::CapabilityKind;
use pcs::free_pcs::CapabilityLocal;
use pcs::free_pcs::CapabilitySummary;

use pcs::utils::maybe_old::MaybeOldPlace;
use pcs::utils::maybe_remote::MaybeRemotePlace;
use pcs::utils::place::Place;
use pcs::utils::PlaceRepacker;

use pcs::combined_pcs::PCGNode;
use pcs::combined_pcs::PCGNodeLike;

use std::collections::HashMap;

use crate::rustc_interface::middle::ty::TyCtxt;
use crate::rustc_interface::middle::ty::Ty;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::Local;
use crate::rustc_interface::middle::mir::LocalDecl;
use crate::rustc_interface::middle::mir::BasicBlock;
use crate::rustc_interface::middle::mir::BasicBlockData;
use crate::rustc_interface::middle::mir::SourceInfo;

pub(crate) fn owned_place_capabilities<'mir, 'tcx>(
    owned_capabilities: &CapabilitySummary<'tcx>
) -> HashMap<Place<'tcx>, CapabilityKind> {
    owned_capabilities
        .iter()
        .flat_map(|capability_local| match capability_local {
            CapabilityLocal::Allocated(projections) => projections
                .iter()
                .map(|(place, capability)| (*place, *capability))
                .collect(),
            CapabilityLocal::Unallocated => HashMap::<_, _>::default(),
        })
        .collect()
}

pub(crate) fn filter_owned_places_by_capability<'mir, 'tcx>(
    owned_capabilities: &CapabilitySummary<'tcx>,
    p: impl Fn(CapabilityKind) -> bool,
) -> HashSet<Place<'tcx>> {
    owned_place_capabilities(owned_capabilities)
        .iter()
        .flat_map(|(place, capability)| if p(*capability) {
            Some(*place)
        } else {
            None
        }).collect()
}

pub(crate) fn borrowed_place_capabilities<'mir, 'tcx>(
    borrow_capabilities: &BorrowPCGCapabilities<'tcx>
) -> HashMap<Place<'tcx>, CapabilityKind> {
    borrow_capabilities
        .iter()
        .flat_map(|(pcg_node, node_capability)| {
            pcg_node_to_current_place(pcg_node).map(|place| (place, node_capability))
        })
        .collect()
}

pub(crate) fn filter_borrowed_places_by_capability<'mir, 'tcx>(
    borrow_capabilities: &BorrowPCGCapabilities<'tcx>,
    p: impl Fn(CapabilityKind) -> bool,
) -> HashSet<Place<'tcx>> {
    borrowed_place_capabilities(borrow_capabilities)
        .iter()
        .flat_map(|(place, capability)| if p(*capability) {
            Some(*place)
        } else {
            None
        }).collect()
}


pub(crate) fn pcg_node_to_current_place<'tcx>(pcg_node: PCGNode<'tcx>) -> Option<Place<'tcx>> {
    match pcg_node {
        PCGNode::Place(maybe_remote_place) => match maybe_remote_place {
            MaybeRemotePlace::Local(maybe_old_place) => match maybe_old_place {
                MaybeOldPlace::Current { place } => Some(place),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

// Create a fresh local with a bogus source span
pub(crate) fn fresh_local<'tcx>(body: &mut Body<'tcx>, ty: Ty<'tcx>) -> Local {
    let fresh_local_decl =
        LocalDecl::with_source_info(ty, bogus_source_info(body));
    body
        .local_decls
        .push(fresh_local_decl)
}

pub(crate) fn bogus_source_info<'tcx>(body: &Body<'tcx>) -> SourceInfo {
    body.local_decls.iter().next().unwrap().source_info
}

// fn lent_places<'mir, 'tcx>(
//     borrows_state: &BorrowsState<'tcx>,
//     owned_capabilities: &CapabilitySummary<'tcx>,
//     repacker: &PlaceRepacker<'mir, 'tcx>,
// ) -> HashSet<Place<'tcx>> {
//     let graph = borrows_state.graph();
//     let leaf_edges = graph.frozen_graph().leaf_edges(*repacker);

//     // TODO iterate over the edge set and just find places mentioned in borrow edges

//     let mut to_visit = leaf_edges
//         .iter()
//         .flat_map(|edge| match edge.kind() {
//             BorrowPCGEdgeKind::Borrow(borrow_edge) => {
//                 if borrow_edge.is_mut() {
//                     edge.blocked_nodes(*repacker)
//                 } else {
//                     FxHashSet::default()
//                 }
//             }
//             _ => FxHashSet::default(),
//         })
//         .collect::<VecDeque<_>>();

//     let mut visited = HashSet::new();
//     let mut mutably_lent_places = HashSet::new();

//     while let Some(curr) = to_visit.pop_front() {
//         if !visited.contains(&curr) {
//             if let Some(place) = pcg_node_to_current_place(curr) {
//                 if let Some(capability) = borrows_state.get_capability(curr) {
//                     if let CapabilityKind::Lent = capability {
//                         mutably_lent_places.insert(place);
//                     }
//                 } else if let Some(local_capability) = owned_capabilities.get(place.local) {
//                     if let CapabilityLocal::Allocated(projections) = local_capability {
//                         if let Some(capability) = projections.get(&place) {
//                             if let CapabilityKind::Lent = capability {
//                                 mutably_lent_places.insert(place);
//                             }
//                         }
//                     }
//                 }
//             }

//             if let Some(local_node) = curr.try_to_local_node() {
//                 let children = graph
//                     .edges_blocked_by(local_node, *repacker)
//                     .flat_map(|edge| edge.blocked_nodes(*repacker));
//                 for child in children {
//                     to_visit.push_back(child);
//                 }
//                 visited.insert(curr);
//             }
//         }
//     }
//     mutably_lent_places
// }
