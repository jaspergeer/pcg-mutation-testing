#![feature(rustc_private)]

use std::borrow::BorrowMut;
use std::io::Write;
use std::{fs::File, path::PathBuf};

use std::cell::RefCell;
use std::collections::HashMap;

use std::sync::Arc;

use pcg_evaluation::rustc_interface::borrowck;
use pcg_evaluation::rustc_interface::borrowck::consumers;

use pcg_evaluation::rustc_interface::data_structures::fx::FxHashMap;

use pcg_evaluation::rustc_interface::errors::registry;

use pcg_evaluation::rustc_interface::middle::mir;
use pcg_evaluation::rustc_interface::middle::mir::Promoted;
use pcg_evaluation::rustc_interface::middle::query::queries::mir_built;
use pcg_evaluation::rustc_interface::middle::ty;
use pcg_evaluation::rustc_interface::middle::util;

use pcg_evaluation::rustc_interface::session;
use pcg_evaluation::rustc_interface::session::config;
use pcg_evaluation::rustc_interface::session::Session;

use pcg_evaluation::rustc_interface::index::IndexVec;

use pcg_evaluation::rustc_interface::middle::query::queries::mir_borrowck::ProvidedValue;

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
use pcs::run_combined_pcs;
use pcs::free_pcs::FreePcsLocation;
use pcs::free_pcs::FreePcsBasicBlock;
use pcs::FpcsOutput;
use pcs::borrows::borrows_graph::BorrowsGraph;

use rand::rng;
use rand::Rng;


// TODO have a cursor that iterates over statements/basic block?, call generate_mutants with each of these

trait Mutator {
    fn generate_mutants<'tcx>(&mut self, fpcs_bb: &FreePcsBasicBlock<'tcx>, body: &Body<'tcx>) -> Vec<Body<'tcx>>;
    fn run_ratio(&mut self) -> (u32, u32);
}

struct TestMutator;

impl Mutator for TestMutator {
    fn generate_mutants<'tcx>(&mut self, fpcs_bb: &FreePcsBasicBlock<'tcx>, body: &Body<'tcx>) -> Vec<Body<'tcx>> {
        let mut body = body.clone();
        for block in body.basic_blocks_mut() {
            let mut insertions = HashMap::new();
            for (i, statement) in block.statements.iter().enumerate() {
                if let mir::StatementKind::Assign(assign_box) = statement.kind.clone() {
                    let (place, _) = *assign_box;
                    let new_local = mir::Local::from_usize(1);
                    insertions.insert(
                        i,
                        mir::Statement {
                            source_info: statement.source_info,
                            kind: mir::StatementKind::Assign(Box::new((
                                mir::Place {
                                    local: new_local,
                                    projection: ty::List::empty(),
                                },
                                mir::Rvalue::Use(mir::Operand::Move(place)),
                            ))),
                        },
                    );
                }
            }

            let mut offset = 1;
            for (i, statement) in insertions {
                block.statements.insert(i + offset, statement);
                offset += 1;
            }
        }
        eprintln!("RUN MUTATOR");
        vec![body]
    }

    fn run_ratio(&mut self) -> (u32, u32) { (1, 1) }
}

struct MutablyLentDetector;

impl Mutator for MutablyLentDetector {
    fn generate_mutants<'tcx>(&mut self, fpcs_bb: &FreePcsBasicBlock<'tcx>, body: &Body<'tcx>) -> Vec<Body<'tcx>> {
        fpcs_bb.statements.iter().flat_map(|statement| {
            vec![]
        }).collect()
        // fn count_pattern_instances<'tcx>(borrows_graph: &BorrowsGraph<'tcx>) -> i64 {
        //     // let mutable_leaf_nodes =
        //     // backwards BFS from mutable leaves?
        // }
    }

    fn run_ratio(&mut self) -> (u32, u32) { (1, 1) }
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
                .collect::<std::collections::HashMap<_, _>>(),
        )
        .expect("Failed to serialize item names to JSON");
        let mut file = File::create(file_path).expect("Failed to create JSON file");
        file.write_all(json_data.as_bytes())
            .expect("Failed to write item names to JSON file");
    }
    analysis_map
}

fn run_tests(input_file: &String, mut mutators: Vec<&mut (dyn Mutator + Send)>) {
    let config = interface::Config {
        // Command line options
        opts: config::Options {
            unstable_opts: config::UnstableOptions {
                polonius: config::Polonius::Next,
                .. config::UnstableOptions::default()
            },
            .. config::Options::default()
        },
        crate_cfg: Vec::new(),       // FxHashSet<(String, Option<String>)>
        crate_check_cfg: Vec::new(), // CheckCfg
        input: config::Input::File(PathBuf::from(input_file)),
        output_dir: None,  // Option<PathBuf>
        output_file: None, // Option<PathBuf>
        file_loader: None, // Option<Box<dyn FileLoader + Send + Sync>>
        locale_resources: driver::DEFAULT_LOCALE_RESOURCES,
        lint_caps: FxHashMap::default(), // FxHashMap<lint::LintId, lint::Level>
        psess_created: None, //Option<Box<dyn FnOnce(&mut ParseSess) + Send>>
        register_lints: None, // Option<Box<dyn Fn(&Session, &mut LintStore) + Send + Sync>>
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

                mutators.iter_mut().for_each(|mutator| {
                    promoted_map.iter().for_each(|(def_id, (body, promoted))| {
                        let mut analysis = analysis_map.get_mut(&def_id).unwrap();
                        body.basic_blocks.indices().for_each(|bb| {
                            let (numerator, denominator) = mutator.run_ratio();
                            if rand::rng().random_ratio(numerator, denominator) {
                                let fpcs_bb = analysis.get_all_for_bb(bb);
                                let mutants = mutator.generate_mutants(&fpcs_bb, &body);
                                // let (borrowck_result, _) = borrowck::do_mir_borrowck(tcx, &generate_mutants, &promoted, None);
                                // TODO do something with borrowck_result
                            }
                        })
                    })
                });
                // TODO rustc might have some stateful mechanism for limiting the number of errors shown and not showing the same error twice
            })
        });
    });
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    let mut input_file = args.get(1).unwrap();
    println!("{:?}", *input_file);
    run_tests(input_file, vec![&mut MutablyLentDetector]);
}
