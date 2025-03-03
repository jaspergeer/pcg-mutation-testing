pub mod mutable_borrow_mutator;
pub mod mutator_impl;

pub use self::mutator_impl::Mutant;
pub use self::mutator_impl::MutantLocation;
pub use self::mutator_impl::MutantRange;
pub use self::mutator_impl::Mutator;

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

use crate::rustc_interface::middle::ty::TyCtxt;

fn owned_places_with_capability_kind<'mir, 'tcx>(
    owned_capabilities: &CapabilitySummary<'tcx>,
    capability_kind: CapabilityKind,
) -> HashSet<Place<'tcx>> {
    owned_capabilities
        .iter()
        .flat_map(|capability_local| match capability_local {
            CapabilityLocal::Allocated(projections) => projections
                .iter()
                .flat_map(|(place, place_capability)| {
                    if *place_capability == capability_kind {
                        Some(*place)
                    } else {
                        None
                    }
                })
                .collect(),
            CapabilityLocal::Unallocated => HashSet::<Place<'_>>::default(),
        })
        .collect()
}

fn borrowed_places_with_capability_kind<'mir, 'tcx>(
    borrow_capabilities: &BorrowPCGCapabilities<'tcx>,
    capability_kind: CapabilityKind,
) -> HashSet<Place<'tcx>> {
    borrow_capabilities
        .iter()
        .flat_map(|(pcg_node, node_capability)| {
            if node_capability == capability_kind {
                pcg_node_to_current_place(pcg_node)
            } else {
                None
            }
        })
        .collect()
}

fn pcg_node_to_current_place<'tcx>(pcg_node: PCGNode<'tcx>) -> Option<Place<'tcx>> {
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
