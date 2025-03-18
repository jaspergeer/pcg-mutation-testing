use std::collections::HashSet;

use pcs::borrow_pcg::borrow_pcg_capabilities::BorrowPCGCapabilities;
use pcs::borrow_pcg::borrow_pcg_edge::BorrowPCGEdgeLike;
use pcs::borrow_pcg::borrow_pcg_edge::LocalNode;
use pcs::borrow_pcg::edge::borrow::BorrowEdge;
use pcs::borrow_pcg::edge::kind::BorrowPCGEdgeKind;
use pcs::borrow_pcg::graph::BorrowsGraph;
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

use crate::rustc_interface::ast::ast::BindingMode;

use crate::rustc_interface::middle::ty::Region;
use crate::rustc_interface::middle::ty::Ty;
use crate::rustc_interface::middle::ty::TyCtxt;

use crate::rustc_interface::middle::mir::BasicBlock;
use crate::rustc_interface::middle::mir::BasicBlockData;
use crate::rustc_interface::middle::mir::BindingForm;
use crate::rustc_interface::middle::mir::Body;
use crate::rustc_interface::middle::mir::BorrowKind;
use crate::rustc_interface::middle::mir::ClearCrossCrate;
use crate::rustc_interface::middle::mir::Local;
use crate::rustc_interface::middle::mir::LocalDecl;
use crate::rustc_interface::middle::mir::LocalInfo;
use crate::rustc_interface::middle::mir::Place as MirPlace;
use crate::rustc_interface::middle::mir::SourceInfo;
use crate::rustc_interface::middle::mir::VarBindingForm;
use crate::rustc_interface::middle::mir::VarDebugInfo;
use crate::rustc_interface::middle::mir::VarDebugInfoContents;

pub(crate) fn owned_place_capabilities<'mir, 'tcx>(
    owned_capabilities: &CapabilitySummary<'tcx>,
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
        .flat_map(|(place, capability)| if p(*capability) { Some(*place) } else { None })
        .collect()
}

pub(crate) fn borrowed_place_capabilities<'mir, 'tcx>(
    borrow_capabilities: &BorrowPCGCapabilities<'tcx>,
) -> HashMap<Place<'tcx>, CapabilityKind> {
    borrow_capabilities
        .iter()
        .flat_map(|(pcg_node, node_capability)| {
            maybe_old_place_to_current_place(pcg_node).map(|place| (place, node_capability))
        })
        .collect()
}

pub(crate) fn filter_borrowed_places_by_capability<'mir, 'tcx>(
    borrow_capabilities: &BorrowPCGCapabilities<'tcx>,
    p: impl Fn(CapabilityKind) -> bool,
) -> HashSet<Place<'tcx>> {
    borrowed_place_capabilities(borrow_capabilities)
        .iter()
        .flat_map(|(place, capability)| if p(*capability) { Some(*place) } else { None })
        .collect()
}

fn maybe_old_place_to_current_place<'tcx>(
    maybe_old_place: MaybeOldPlace<'tcx>,
) -> Option<Place<'tcx>> {
    match maybe_old_place {
        MaybeOldPlace::Current { place } => Some(place),
        _ => None,
    }
}

pub(crate) fn pcg_node_to_current_place<'tcx>(pcg_node: PCGNode<'tcx>) -> Option<Place<'tcx>> {
    match pcg_node {
        PCGNode::Place(maybe_remote_place) => maybe_remote_place.as_current_place(),
        PCGNode::RegionProjection(region_projection) => {
            let maybe_old_place: MaybeOldPlace<'_> =
                region_projection
                .base()
                .try_into()
                .ok()?;
            maybe_old_place_to_current_place(maybe_old_place)
        },
    }
}

pub(crate) fn local_node_to_current_place<'tcx>(pcg_node: LocalNode<'tcx>) -> Option<Place<'tcx>> {
    match pcg_node {
        PCGNode::Place(maybe_old_place) =>
            maybe_old_place_to_current_place(maybe_old_place),
        PCGNode::RegionProjection(region_projection) =>
            maybe_old_place_to_current_place(region_projection.base()),
    }
}

// Create a fresh local with a bogus source span
pub(crate) fn fresh_local<'tcx>(body: &mut Body<'tcx>, ty: Ty<'tcx>) -> Local {
    let mut fresh_local_decl = LocalDecl::with_source_info(ty, bogus_source_info(body));
    let local_info = {
        let var_binding_form = VarBindingForm {
            binding_mode: BindingMode::NONE,
            opt_ty_info: None,
            opt_match_place: None,
            pat_span: bogus_source_info(body).span,
        };
        let binding_form = BindingForm::Var(var_binding_form);
        ClearCrossCrate::Set(Box::new(LocalInfo::User(binding_form)))
    };
    fresh_local_decl.local_info = local_info;
    body.local_decls.push(fresh_local_decl)
}

pub(crate) fn fresh_basic_block<'tcx>(body: &mut Body<'tcx>) -> BasicBlock {
    body.basic_blocks_mut().push(BasicBlockData::new(None))
}

pub(crate) fn bogus_source_info<'tcx>(body: &Body<'tcx>) -> SourceInfo {
    body.local_decls.iter().next().unwrap().source_info
}

pub(crate) fn is_mut(kind: BorrowKind) -> bool {
    match kind {
        BorrowKind::Mut { .. } => true,
        _ => false,
    }
}

pub(crate) fn is_shared(kind: BorrowKind) -> bool {
    match kind {
        BorrowKind::Shared => true,
        _ => false,
    }
}

pub(crate) fn borrowed_places<'graph, 'tcx>(
    graph: &'graph BorrowsGraph<'tcx>,
    p: fn(BorrowKind) -> bool,
) -> impl Iterator<Item = (Place<'tcx>, Region<'tcx>)> + 'graph {
    graph
        .edges()
        .flat_map(move |edge_ref| match edge_ref.kind() {
            BorrowPCGEdgeKind::Borrow(borrow_edge) => match borrow_edge {
                BorrowEdge::Local(local_borrow) => {
                    if borrow_edge.kind().iter().any(|kind| p(*kind)) {
                        let place = maybe_old_place_to_current_place(local_borrow.blocked_place)?;
                        let region = local_borrow.region;
                        Some((place, region))
                    } else {
                        None
                    }
                }
                _ => None,
            },
            _ => None,
        })
}

pub(crate) fn has_named_local<'tcx>(
    place: Place<'tcx>,
    body: &Body<'tcx>,
) -> bool {
    match body.local_decls.get(place.local) {
        Some(local_decl) => {
            local_decl.is_user_variable()
        },
        None => false,
    }
}
