#![feature(rustc_private)]

use std::borrow::BorrowMut;
use std::io::Write;
use std::{fs::File, path::PathBuf};

use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;

use std::sync::Arc;

use serde::Serialize;
use serde_json::Map as JSONMap;

use pcg_evaluation::rustc_interface::borrowck;
use pcg_evaluation::rustc_interface::borrowck::consumers;

use pcg_evaluation::rustc_interface::data_structures::fx::FxHashMap;

use pcg_evaluation::rustc_interface::errors::registry;
use pcg_evaluation::rustc_interface::errors::emitter::Emitter;

use pcg_evaluation::rustc_interface::middle::util;
use pcg_evaluation::rustc_interface::middle::mir;

use pcg_evaluation::rustc_interface::middle::ty;
use pcg_evaluation::rustc_interface::middle::ty::Ty;
use pcg_evaluation::rustc_interface::middle::ty::Region;
use pcg_evaluation::rustc_interface::middle::ty::RegionKind;

use pcg_evaluation::rustc_interface::middle::mir::Place as MirPlace;
use pcg_evaluation::rustc_interface::middle::mir::Promoted;
use pcg_evaluation::rustc_interface::middle::mir::Local;
use pcg_evaluation::rustc_interface::middle::mir::LocalDecl;
use pcg_evaluation::rustc_interface::middle::mir::BorrowCheckResult;
use pcg_evaluation::rustc_interface::middle::mir::BorrowKind;
use pcg_evaluation::rustc_interface::middle::mir::MutBorrowKind;
use pcg_evaluation::rustc_interface::middle::mir::Statement;
use pcg_evaluation::rustc_interface::middle::mir::StatementKind;
use pcg_evaluation::rustc_interface::middle::mir::Rvalue;
use pcg_evaluation::rustc_interface::middle::mir::ClearCrossCrate;

use pcg_evaluation::rustc_interface::middle::query::queries::mir_built;
use pcg_evaluation::rustc_interface::middle::query::queries::mir_borrowck::ProvidedValue;


use pcg_evaluation::rustc_interface::session;
use pcg_evaluation::rustc_interface::session::config;
use pcg_evaluation::rustc_interface::session::Session;

use pcg_evaluation::rustc_interface::index::IndexVec;


use pcg_evaluation::rustc_interface::{
    driver::{self, args, Compilation},
    errors,
    hir::{self, def_id::LocalDefId},
    interface,
    interface::{interface::Compiler, Config, Queries},
    middle::{
        mir::Body, ty::TyCtxt,
        util::Providers,
    },
    session::{
        config::{ErrorOutputType, Input},
        EarlyDiagCtxt,
    },
};
use pcs::combined_pcs::BodyWithBorrowckFacts;
use pcs::combined_pcs::PCGNode;
use pcs::run_combined_pcs;
use pcs::free_pcs::FreePcsLocation;
use pcs::free_pcs::FreePcsBasicBlock;
use pcs::free_pcs::CapabilityKind;
use pcs::FpcsOutput;

use pcs::borrows::borrow_pcg_edge::LocalNode;
use pcs::borrows::borrows_graph::BorrowsGraph;
use pcs::borrows::edge::kind::BorrowPCGEdgeKind;
use pcs::borrows::edge_data::EdgeData;
use pcs::utils::PlaceRepacker;
use pcs::utils::place::Place as PCGPlace;
use pcs::utils::maybe_remote::MaybeRemotePlace;
use pcs::utils::maybe_old::MaybeOldPlace;

use rand::rng;
use rand::Rng;

// struct DiagCaptureEmitter;

// impl Emitter for DiagCaptureEmitter {

// }

#[derive(Serialize)]
enum BorrowCheckInfo {
    Passed,
    Failed { error_codes: Vec<String> }
}

#[derive(Serialize)]
struct LogEntry {
    mutation_type: String,
    borrow_check_result: BorrowCheckInfo,
    info: String
}

struct Mutant<'tcx> {
    body: Body<'tcx>,
    info: String
}

trait Mutator {
    fn generate_mutants<'tcx>(&mut self, tcx: &TyCtxt<'tcx>, fpcs_bb: &FreePcsBasicBlock<'tcx>, body: &Body<'tcx>) -> Vec<Mutant<'tcx>>;
    fn run_ratio(&mut self) -> (u32, u32);
    fn name(&mut self) -> String;
}

// struct TestMutator;

// impl Mutator for TestMutator {
//     fn generate_mutants<'tcx>(&mut self, tcx: &TyCtxt<'tcx>, fpcs_bb: &FreePcsBasicBlock<'tcx>, body: &Body<'tcx>) -> Vec<Body<'tcx>> {
//         let mut body = body.clone();
//         for block in body.basic_blocks_mut() {
//             let mut insertions = HashMap::new();
//             for (i, statement) in block.statements.iter().enumerate() {
//                 if let mir::StatementKind::Assign(assign_box) = statement.kind.clone() {
//                     let (place, _) = *assign_box;
//                     let new_local = mir::Local::from_usize(1);
//                     insertions.insert(
//                         i,
//                         mir::Statement {
//                             source_info: statement.source_info,
//                             kind: mir::StatementKind::Assign(Box::new((
//                                 mir::Place {
//                                     local: new_local,
//                                     projection: ty::List::empty(),
//                                 },
//                                 mir::Rvalue::Use(mir::Operand::Move(place)),
//                             ))),
//                         },
//                     );
//                 }
//             }

//             let mut offset = 1;
//             for (i, statement) in insertions {
//                 block.statements.insert(i + offset, statement);
//                 offset += 1;
//             }
//         }
//         eprintln!("RUN MUTATOR");
//         vec![body]
//     }

//     fn run_ratio(&mut self) -> (u32, u32) { (1, 1) }
// }

struct MutableBorrowMutator;

impl Mutator for MutableBorrowMutator {
    fn generate_mutants<'tcx>(&mut self, tcx: &TyCtxt<'tcx>, fpcs_bb: &FreePcsBasicBlock<'tcx>, body: &Body<'tcx>) -> Vec<Mutant<'tcx>> {

        fn generate_mutants_location<'mir, 'tcx>(tcx: &TyCtxt<'tcx>, body: &Body<'tcx>, location: &FreePcsLocation<'tcx>) -> Vec<Mutant<'tcx>> {
            let borrows_state = location.borrows.post_main();
            let borrows_graph = borrows_state.graph();
            let repacker = PlaceRepacker::new(body, *tcx);

            let mut leaf_nodes = borrows_graph.leaf_nodes(repacker, None);
            let mut to_visit = leaf_nodes.drain()
                                         .filter(|node| borrows_state.get_capability((*node).into()) == Some(CapabilityKind::Exclusive))
                                         .collect::<VecDeque<_>>();
            let mut visited = HashSet::new();
            let mut mutably_lent_places = HashSet::new();

            fn current_place_of_node<'tcx>(tcx: &TyCtxt<'tcx>, node: LocalNode<'tcx>) -> Option<MirPlace<'tcx>> {
                match node {
                    PCGNode::Place(place) =>
                        match place {
                            MaybeOldPlace::Current { place } => {
                                Some(place.to_mir_place(tcx))
                            },
                            _ => None
                        },
                    _ => None
                }
            }

            while let Some(curr) = to_visit.pop_front() {
                if !visited.contains(&curr) {
                    if let Some(place) = current_place_of_node(tcx, curr) {
                        mutably_lent_places.insert(place);
                        // TODO I don't think we record places in the owned PCG...
                    }
                    let children = borrows_graph.edges_blocked_by(curr, repacker).flat_map(|edge| {
                        edge.blocked_by_nodes(repacker)
                    });
                    for child in children {
                        to_visit.push_back(child);
                    }
                    visited.insert(curr);
                }
            }

            for place in mutably_lent_places.iter() {
                println!("{:?} is mutably lent", place)
            }
            mutably_lent_places.iter().map(|place| {
                let mut mutant_body = body.clone();

                let fresh_local = Local::from_usize(mutant_body.local_decls.len());
                let erased_region = Region::new_from_kind(*tcx, RegionKind::ReErased);


                let borrow_ty = Ty::new_mut_ref(*tcx, erased_region, place.ty(&body.local_decls, *tcx).ty);

                let bb_index = location.location.block;
                let statement_index = location.location.statement_index;
                let bb = mutant_body.basic_blocks_mut().get_mut(bb_index).unwrap();
                let statement_source_info = bb.statements.get(statement_index).unwrap().source_info;

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

                Mutant { body: mutant_body, info: "TODO".into() }
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

fn run_pcs_on_all_fns<'mir, 'tcx>(body_map: &'mir HashMap<LocalDefId, BodyWithBorrowckFacts<'tcx>>, tcx: TyCtxt<'tcx>) -> HashMap<LocalDefId, FpcsOutput<'mir, 'tcx>> {
    let mut item_names = vec![];

    let vis_dir = if std::env::var("PCS_VISUALIZATION").unwrap_or_default() == "true" {
        Some("visualization/data")
    } else {
        None
    };

    if let Some(path) = &vis_dir {
        if std::path::Path::new(path).exists() {
            std::fs::remove_dir_all(path)
                .expect("Failed to delete visualization directory contents");
        }
        std::fs::create_dir_all(path).expect("Failed to create visualization directory");
    }

    let mut analysis_map = HashMap::new();

    for def_id in tcx.hir().body_owners() {
        let kind = tcx.def_kind(def_id);
        match kind {
            hir::def::DefKind::Fn | hir::def::DefKind::AssocFn => {
                let item_name = format!("{}", tcx.def_path_str(def_id.to_def_id()));
                let body = body_map.get(&def_id).unwrap();

                let safety = tcx.fn_sig(def_id).skip_binder().safety();
                if safety == hir::Safety::Unsafe {
                    eprintln!("Skipping unsafe function: {}", item_name);
                    continue;
                }
                eprintln!("Running PCG on function: {}", item_name);
                let analysis = run_combined_pcs(
                    &body,
                    tcx,
                    vis_dir.map(|dir| format!("{}/{}", dir, item_name)),
                );

                analysis_map.insert(def_id, analysis);

                println!(
                    "num analyses: {}",
                    analysis_map.len()
                );
                item_names.push(item_name);
            }
            unsupported_item_kind => {
                eprintln!("Unsupported item: {unsupported_item_kind:?}");
            }
        }
    }

    if let Some(dir_path) = &vis_dir {
        let file_path = format!("{}/functions.json", dir_path);

        let json_data = serde_json::to_string(
            &item_names
                .iter()
                .map(|name| (name.clone(), name.clone()))
                .collect::<HashMap<_, _>>(),
        )
        .expect("Failed to serialize item names to JSON");
        let mut file = File::create(file_path).expect("Failed to create JSON file");
        file.write_all(json_data.as_bytes())
            .expect("Failed to write item names to JSON file");
    }
    analysis_map
}

fn run_tests(input_file: &String, mut mutators: Vec<&mut (dyn Mutator + Send)>) {

   fn borrowck_info_of_borrowck_result<'tcx>(borrowck_result: BorrowCheckResult<'tcx>) -> BorrowCheckInfo {
       BorrowCheckInfo::Passed
   }

    let config = interface::Config {
        // Command line options
        opts: config::Options {
            unstable_opts: config::UnstableOptions {
                polonius: config::Polonius::Next,
                .. config::UnstableOptions::default()
            },
            .. config::Options::default()
        },
        crate_cfg: Vec::new(),
        crate_check_cfg: Vec::new(),
        input: config::Input::File(PathBuf::from(input_file)),
        output_dir: None,
        output_file: None,
        file_loader: None,
        locale_resources: driver::DEFAULT_LOCALE_RESOURCES,
        lint_caps: FxHashMap::default(),
        psess_created: None,
        register_lints: None,
        override_queries: None,
        registry: registry::Registry::new(errors::codes::DIAGNOSTICS),
        make_codegen_backend: None,
        expanded_args: Vec::new(),
        ice_file: None,
        hash_untracked_state: None,
        using_internal_features: Arc::default(),
    };

    interface::run_compiler(config, |compiler| {
        compiler.enter(|queries| {
            queries.global_ctxt().unwrap().enter(|tcx| {
                let hir_krate = tcx.hir();

                let promoted_map =
                    hir_krate.body_owners().map(|def_id| {
                        let (body_steal, promoted_steal) = tcx.mir_promoted(def_id);
                        let body = body_steal.borrow().clone();
                        let promoted = promoted_steal.borrow().clone();
                        (def_id, (body, promoted))
                    }).collect::<HashMap<_, _>>();

                let body_map =
                    hir_krate.body_owners().map(|def_id| {
                        let consumer_opts = consumers::ConsumerOptions::PoloniusOutputFacts;
                        let body_with_facts = consumers::get_body_with_borrowck_facts(tcx, def_id, consumer_opts);
                        (def_id, body_with_facts.into())
                    }).collect::<HashMap<_, _>>();

                let mut analysis_map = run_pcs_on_all_fns(&body_map, tcx);

                let mut mutation_log = JSONMap::new();

                for mutator in mutators.iter_mut() {
                    for (def_id, (body, promoted)) in promoted_map.iter() {
                        let analysis = analysis_map.get_mut(&def_id).unwrap();
                        for bb in body.basic_blocks.indices() {
                            let (numerator, denominator) = mutator.run_ratio();
                            if rand::rng().random_ratio(numerator, denominator) {
                                let fpcs_bb = analysis.get_all_for_bb(bb);
                                eprintln!("Running mutator for def_id: {:?}, bb: {:?}", def_id, bb);
                                let mutants = mutator.generate_mutants(&tcx, &fpcs_bb, &body);
                                for Mutant { body, info } in mutants {
                                    eprintln!("mutant body: {:?}", body);
                                    let (borrowck_result, _) = borrowck::do_mir_borrowck(tcx, &body, &promoted, None);
                                    let borrowck_info = borrowck_info_of_borrowck_result(borrowck_result);
                                    let log_entry = LogEntry {
                                        mutation_type: mutator.name(),
                                        borrow_check_result: borrowck_info,
                                        info: info
                                    };
                                    mutation_log.insert(mutation_log.len().to_string().into(),
                                                        serde_json::to_value(log_entry).unwrap());
                                }
                            }
                        }
                    }
                }
                eprintln!("LOG: {}", serde_json::to_string_pretty(&mutation_log).unwrap())
                // TODO rustc might have some stateful mechanism for limiting the number of errors shown and not showing the same error twice
            })
        });
    });
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    let mut input_file = args.get(1).unwrap();
    println!("{:?}", *input_file);
    run_tests(input_file, vec![&mut MutableBorrowMutator]);
}
