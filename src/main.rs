#![feature(rustc_private)]

use std::borrow::BorrowMut;
use std::io::Write;
use std::{fs::File, path::PathBuf};

use std::cell::RefCell;
use std::collections::HashMap;

use std::sync::Arc;

use pcg_evaluation::rustc_interface::borrowck;
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
    borrowck::consumers,
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
use pcs::{combined_pcs::BodyWithBorrowckFacts, run_combined_pcs, FpcsOutput};

thread_local! {
    pub static BODIES:
        RefCell<FxHashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
        RefCell::new(FxHashMap::default());

    pub static PROMOTED:
        RefCell<FxHashMap<LocalDefId, (Body<'static>, IndexVec<Promoted, Body<'static>>)>> =
        RefCell::new(FxHashMap::default());

    pub static ANALYSES:
        RefCell<FxHashMap<LocalDefId, FpcsOutput<'static, 'static>>> =
        RefCell::new(FxHashMap::default());
}

trait Mutator {
    fn next_mutant<'mir, 'tcx>(&mut self, analysis: &FpcsOutput<'mir, 'tcx>, to_mutate: Body<'tcx>) -> Option<Body<'tcx>>;
}

struct TestMutator;

impl TestMutator {
    fn construct() -> Box<dyn Mutator> {
        Box::new(TestMutator)
    }
}

impl Mutator for TestMutator {
    fn next_mutant<'mir, 'tcx>(&mut self, _analysis: &FpcsOutput<'mir, 'tcx>, mut body: Body<'tcx>) -> Option<Body<'tcx>> {
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
        Some(body)
    }
}

fn run_pcs_on_all_fns<'tcx>(tcx: TyCtxt<'tcx>) {
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

    for def_id in tcx.hir().body_owners() {
        let kind = tcx.def_kind(def_id);
        match kind {
            hir::def::DefKind::Fn | hir::def::DefKind::AssocFn => {
                let item_name = format!("{}", tcx.def_path_str(def_id.to_def_id()));
                let body: BodyWithBorrowckFacts<'_> = BODIES.with(|state| {
                    let mut map = state.borrow_mut();
                    unsafe { std::mem::transmute(map.remove(&def_id).unwrap()) }
                });

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
                ANALYSES.with(|state| {
                    let mut map = state.borrow_mut();
                    unsafe {
                        assert!(map.insert(def_id, std::mem::transmute(analysis)).is_none());
                    }
                });
                println!(
                    "num analyses: {}",
                    ANALYSES.with(|state| state.borrow_mut().len())
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
}

fn mir_borrowck<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> ProvidedValue<'tcx> {
    let consumer_opts = consumers::ConsumerOptions::PoloniusOutputFacts;
    let body_with_facts = consumers::get_body_with_borrowck_facts(tcx, def_id, consumer_opts);
    unsafe {
        let body: BodyWithBorrowckFacts<'tcx> = body_with_facts.into();
        let body: BodyWithBorrowckFacts<'static> = std::mem::transmute(body);
        BODIES.with(|state| {
            let mut map = state.borrow_mut();
            assert!(map.insert(def_id, body).is_none());
        });
    }
    let mut providers = Providers::default();
    borrowck::provide(&mut providers);
    let original_mir_borrowck = providers.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}

fn set_mir_borrowck(_session: &Session, providers: &mut Providers) {
    providers.mir_borrowck = mir_borrowck;
}

fn run_tests(input_file: &String, make_mutators: Vec<fn() -> Box<dyn Mutator>>) {
    let config = interface::Config {
        // Command line options
        opts: config::Options {
            incremental: None,
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
        override_queries: Some(set_mir_borrowck),
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
                for def_id in hir_krate.body_owners() {
                    let (body_steal, promoted_steal) = tcx.mir_promoted(def_id);
                    unsafe {
                        let body: Body<'_> = std::mem::transmute(body_steal.borrow().clone());
                        let promoted: IndexVec<Promoted, Body<'_>> = std::mem::transmute(promoted_steal.borrow().clone());
                        PROMOTED.with(|state| {
                            let mut map = state.borrow_mut();
                            map.insert(def_id, (body, promoted));
                        });
                    }
                }

                tcx.analysis(());
                run_pcs_on_all_fns(tcx);

                for make_mutator in &make_mutators {
                    let promoted_map: FxHashMap<LocalDefId, (Body<'_>, IndexVec<Promoted, Body<'_>>)> = PROMOTED.with(|state| unsafe { std::mem::transmute(state.borrow().clone()) });
                    for (def_id, (body, promoted)) in promoted_map {
                        let mut body_clone = body.clone();
                        let (_, _) = borrowck::do_mir_borrowck(tcx.clone(), &mut body_clone, &promoted, None);
                    }
                }

                // mutations
                for make_mutator in &make_mutators {
                    let promoted_map: FxHashMap<LocalDefId, (Body<'_>, IndexVec<Promoted, Body<'_>>)> = PROMOTED.with(|state| unsafe { std::mem::transmute(state.borrow().clone()) });
                    for (def_id, (mut body, promoted)) in promoted_map {
                        let mut curr_mutator = make_mutator();
                        eprintln!("before {:?}: {:?}", def_id, body);
                        ANALYSES.with(|state| {
                            let analyses_map = state.borrow();
                            unsafe {
                                let analysis: &FpcsOutput<'_, '_> = std::mem::transmute(analyses_map.get(&def_id).unwrap());
                                match curr_mutator.next_mutant(analysis, body) {
                                    Some(next_mutant) => {
                                        println!("after {:?}: {:?}", def_id, next_mutant);
                                        println!();
                                        let (borrowck_result, _) = borrowck::do_mir_borrowck(tcx, &next_mutant, &promoted, None);
                                    }
                                    _ => ()
                                }
                            }
                        });
                    }
                }
                // TODO rustc might have some stateful mechanism for limiting the number of errors shown and not showing the same error twice
            })
        });
    });
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    let mut input_file = args.get(1).unwrap();
    println!("{:?}", *input_file);
    run_tests(input_file, vec![TestMutator::construct]);
    // let mut rustc_args = Vec::new();
    // if !std::env::args().any(|arg| arg.starts_with("--edition=")) {
    //     rustc_args.push("--edition=2018".to_string());
    // }
    // rustc_args.push("-Zpolonius=next".to_string());
    // rustc_args.extend(std::env::args().skip(1));

    // eprintln!("Generate PCGs");
    // driver::RunCompiler::new(
    //     &rustc_args,
    //     &mut PcgCallbacks {
    //         mutator_make_mutators: vec![|| Box::new(TestMutator)],
    //     },
    // )
    // .run()
    // .unwrap();

    // interface::run_compiler();
}
