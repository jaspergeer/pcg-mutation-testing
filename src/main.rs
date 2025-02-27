#![feature(rustc_private)]

use pcg_evaluation::mutator::MutantLocation;
use pcg_evaluation::mutator::Mutant;
use pcg_evaluation::mutator::Mutator;

use pcg_evaluation::mutator::mutable_borrow_mutator::MutableBorrowMutator;

use pcg_evaluation::utils::env_feature_enabled;

use std::io::Write;
use std::fs::File;
use std::path::PathBuf;

use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;

use serde::Serialize;
use serde_json::Map as JSONMap;

use pcg_evaluation::rustc_interface::borrowck;
use pcg_evaluation::rustc_interface::borrowck::consumers;

use pcg_evaluation::rustc_interface::errors::fallback_fluent_bundle;

use pcg_evaluation::rustc_interface::middle::ty::TyCtxt;
use pcg_evaluation::rustc_interface::middle::util::Providers;
use pcg_evaluation::rustc_interface::middle::query::queries::mir_borrowck::ProvidedValue;

use pcg_evaluation::rustc_interface::session::Session;

use pcg_evaluation::rustc_interface::driver::DEFAULT_LOCALE_RESOURCES;
use pcg_evaluation::rustc_interface::driver::Callbacks;

use pcg_evaluation::errors::initialize_error_tracking;
use pcg_evaluation::errors::track_body_error_codes;
use pcg_evaluation::errors::get_registered_errors;

use pcg_evaluation::rustc_interface::hir::def_id::CrateNum;

use pcg_evaluation::rustc_interface::driver;
use pcg_evaluation::rustc_interface::driver::Compilation;

use pcg_evaluation::rustc_interface::hir;
use pcg_evaluation::rustc_interface::hir::def_id::LocalDefId;

use pcg_evaluation::rustc_interface::interface::interface::Compiler;
use pcg_evaluation::rustc_interface::interface::Config;
use pcg_evaluation::rustc_interface::interface::Queries;

use pcs::run_combined_pcs;
use pcs::combined_pcs::BodyWithBorrowckFacts;
use pcs::FpcsOutput;

use rand::Rng;

thread_local! {
    pub static BODIES:
        RefCell<HashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
        RefCell::new(HashMap::default());
}

#[derive(Serialize)]
struct CrateMutantsData {
    name: String,
    failed: usize,
    passed: usize
}

#[derive(Serialize)]
enum BorrowCheckInfo {
    Passed,
    Failed { error_codes: HashSet<String> }
}

#[derive(Serialize)]
struct LogEntry {
    mutation_type: String,
    borrow_check_result: BorrowCheckInfo,
    definition: String,
    location: MutantLocation,
    info: String
}

fn run_pcg_on_all_fns<'mir, 'tcx>(body_map: &'mir HashMap<LocalDefId, BodyWithBorrowckFacts<'tcx>>, tcx: TyCtxt<'tcx>) -> HashMap<LocalDefId, FpcsOutput<'mir, 'tcx>> {
    if std::env::var("CARGO_CRATE_NAME").is_ok() && std::env::var("CARGO_PRIMARY_PACKAGE").is_err()
    {
        // We're running in cargo, but the Rust file is a dependency (not part of the primary package)
        // For now we don't check dependencies, so we abort
        return HashMap::default();
    }

    let mut analysis_map = HashMap::new();

    let user_specified_vis_dir = std::env::var("PCG_VISUALIZATION_DATA_DIR");
    let vis_dir: Option<&str> = if env_feature_enabled("PCG_VISUALIZATION").unwrap_or(false) {
        Some(match user_specified_vis_dir.as_ref() {
            Ok(dir) => dir,
            Err(_) => "visualization/data",
        })
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
                let body = body_map.get(&def_id).unwrap();

                let safety = tcx.fn_sig(def_id).skip_binder().safety();
                if safety == hir::Safety::Unsafe {
                    continue;
                }
                let output = run_combined_pcs(
                    body,
                    tcx,
                    vis_dir.map(|dir| format!("{}/{}", dir, item_name)),
                );
                analysis_map.insert(def_id, output);
            }
            unsupported_item_kind => {
                eprintln!("Unsupported item: {unsupported_item_kind:?}");
            }
        }
    }

    analysis_map
}

struct MutatorCallbacks {
    mutators: Vec<Box<dyn Mutator + Send>>,
    results_dir: PathBuf
}

fn mir_borrowck<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> ProvidedValue<'tcx> {
    let consumer_opts = consumers::ConsumerOptions::PoloniusInputFacts;
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
    pcs::rustc_interface::borrowck::provide(&mut providers);
    let original_mir_borrowck = providers.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}

fn set_mir_borrowck(_session: &Session, providers: &mut Providers) {
    providers.mir_borrowck = mir_borrowck;
}

fn do_mutation_tests<'tcx>(tcx: TyCtxt<'tcx>, compiler: &Compiler, mutators: &mut Vec<Box<dyn Mutator + Send>>, results_dir: &PathBuf) {
    let body_map: HashMap<_, BodyWithBorrowckFacts<'tcx>> = unsafe { std::mem::transmute(BODIES.take()) };
    let mut analysis_map = run_pcg_on_all_fns(&body_map, tcx);

    let mut mutation_log = JSONMap::new();

    initialize_error_tracking();

    for mutator in mutators.iter_mut() {
        eprintln!("working dir {}", std::env::current_dir().unwrap().display());
        for (def_id, analysis) in analysis_map.iter_mut() {
            if let Some(body_with_borrowck_facts) = body_map.get(&def_id) {
                let body = &body_with_borrowck_facts.body;
                let promoted = &body_with_borrowck_facts.promoted;

                for bb in body.basic_blocks.indices() {
                    let (numerator, denominator) = mutator.run_ratio();
                    if rand::rng().random_ratio(numerator, denominator) {
                        if let Result::Ok(Some(fpcs_bb)) = analysis.get_all_for_bb(bb) {
                            eprintln!("Running mutator for def_id: {:?}, bb: {:?}", def_id, bb);
                            let mutants = mutator.generate_mutants(&tcx, &fpcs_bb, &body);
                            for Mutant { body, location, info } in mutants {
                                eprintln!("mutant at {} in {:?}", serde_json::to_value(&location).unwrap(), def_id);
                                track_body_error_codes(*def_id);

                                let (borrowck_result, _) = borrowck::do_mir_borrowck(tcx, &body, &promoted, None);
                                let borrowck_info = {
                                    if let Some(_) = borrowck_result.tainted_by_errors {
                                        let error_codes = get_registered_errors();
                                        BorrowCheckInfo::Failed {
                                            error_codes: error_codes.iter()
                                                                    .map(|err_code| err_code.to_string())
                                                                    .collect()
                                        }
                                    } else {
                                        BorrowCheckInfo::Passed
                                    }
                                };
                                let log_entry = LogEntry {
                                    mutation_type: mutator.name(),
                                    borrow_check_result: borrowck_info,
                                    definition: format!("{def_id:?}"),
                                    location: location,
                                    info: info
                                };
                                mutation_log.insert(mutation_log.len().to_string().into(),
                                                    serde_json::to_value(log_entry).unwrap());
                                compiler.sess.dcx().reset_err_count(); // cursed
                            }
                        }
                    }
                }
            }
        }
    }

    let crate_name = tcx.crate_name(CrateNum::from_usize(0)).to_string();
    let json_data = serde_json::to_string_pretty(&mutation_log).unwrap();
    let output_file_path = results_dir.join(crate_name).with_extension("json");
    let mut output_file = File::create(&output_file_path).expect("Failed to create output file");
    eprintln!("Writing results to {:?}", output_file_path);
    output_file.write_all(json_data.as_bytes()).expect("Failed to write results to file");
}

impl Callbacks for MutatorCallbacks {
    fn config(&mut self, config: &mut Config) {
        assert!(config.override_queries.is_none());
        config.override_queries = Some(set_mir_borrowck);
    }

    fn after_crate_root_parsing<'tcx>(
        &mut self,
        compiler: &Compiler,
        _queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let fallback_bundle = fallback_fluent_bundle(DEFAULT_LOCALE_RESOURCES.to_vec(), false);
        compiler.sess.dcx().make_silent(fallback_bundle, None, false);
        Compilation::Continue
    }

    fn after_analysis<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        // Don't run mutation testing on dependencies
        if !(std::env::var("CARGO_CRATE_NAME").is_ok() && std::env::var("CARGO_PRIMARY_PACKAGE").is_err())
        {
            queries.global_ctxt().unwrap().enter(|tcx| do_mutation_tests(tcx, compiler, &mut self.mutators, &self.results_dir));
        }
        if std::env::var("CARGO").is_ok() {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}

fn main() {
    let mut rustc_args = vec!["rustc".to_string()];

    if !std::env::args().any(|arg| arg.starts_with("--edition=")) {
        rustc_args.push("--edition=2018".to_string());
    }

    let results_dir = match std::env::var("RESULTS_DIR") {
        Ok(str) => str.into(),
        _ => std::env::current_dir().unwrap()
    };

    rustc_args.extend(std::env::args().skip(1));
    let mut callbacks = MutatorCallbacks { mutators: vec![Box::new(MutableBorrowMutator)], results_dir: results_dir };
    driver::RunCompiler::new(&rustc_args, &mut callbacks)
        .run()
        .unwrap();
}
