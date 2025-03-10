use std::collections::HashSet;

use pcs::borrow_pcg::borrow_pcg_edge::BorrowPCGEdgeLike;
use pcs::borrow_pcg::borrow_pcg_capabilities::BorrowPCGCapabilities;
use pcs::borrow_pcg::region_projection::MaybeRemoteRegionProjectionBase;
use pcs::borrow_pcg::region_projection::RegionProjection;
use pcs::borrow_pcg::graph::BorrowsGraph;
use pcs::borrow_pcg::edge::kind::BorrowPCGEdgeKind;
use pcs::borrow_pcg::edge::borrow::BorrowEdge;

use pcs::free_pcs::CapabilityKind;
use pcs::free_pcs::CapabilitySummary;
use pcs::free_pcs::CapabilityLocal;

use pcs::utils::maybe_old::MaybeOldPlace;
use pcs::utils::maybe_remote::MaybeRemotePlace;
use pcs::utils::place::Place;
use pcs::utils::PlaceRepacker;

use pcs::combined_pcs::PCGNode;
use pcs::combined_pcs::PCGNodeLike;

use std::collections::HashMap;

use crate::rustc_interface::middle::ty::Region;
use crate::rustc_interface::middle::ty::TyCtxt;
use crate::rustc_interface::middle::ty::Ty;

use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::Local;
use crate::rustc_interface::middle::mir::LocalDecl;
use crate::rustc_interface::middle::mir::BasicBlock;
use crate::rustc_interface::middle::mir::BasicBlockData;
use crate::rustc_interface::middle::mir::SourceInfo;
use crate::rustc_interface::middle::mir::Place as MirPlace;

pub(crate) fn owned_place_capabilities<'mir, 'tcx>(
    owned_capabilities: &CapabilitySummary<'tcx>
) -> HashMap<Place<'tcx>, CapabilityKind> {
    owned_capabilities
        .iter()
        .flat_map(|capability_local| match capability_local {
            CapabilityLocal::Allocated(projections) => projections
                .place_capabilities()
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

fn maybe_old_place_to_current_place<'tcx>(maybe_old_place: MaybeOldPlace<'tcx>) -> Option<Place<'tcx>> {
    match maybe_old_place {
        MaybeOldPlace::Current { place } => Some(place),
        _ => None,
    }
}

pub(crate) fn pcg_node_to_current_place<'tcx>(pcg_node: PCGNode<'tcx>) -> Option<Place<'tcx>> {
    match pcg_node {
        PCGNode::Place(maybe_remote_place) =>
          match maybe_remote_place {
              MaybeRemotePlace::Local(maybe_old_place) =>
                  maybe_old_place_to_current_place(maybe_old_place),
              _ => None
          }
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

pub(crate) fn borrowed_places<'graph, 'tcx>(
    graph: &'graph BorrowsGraph<'tcx>,
    mutable: bool,
) -> impl Iterator<Item = (Place<'tcx>, Region<'tcx>)> + 'graph {
    graph.edges().flat_map(move |edge_ref| match edge_ref.kind() {
        BorrowPCGEdgeKind::Borrow(borrow_edge) =>
            match borrow_edge {
                BorrowEdge::Local(local_borrow) =>
                  if local_borrow.is_mut() == mutable {
                    let place = maybe_old_place_to_current_place(local_borrow.blocked_place)?;
                    let region = local_borrow.region;
                    Some((place, region))
                  } else {
                      None
                  },
                _ => None
            },
        _ => None
    })
}
