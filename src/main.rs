#![feature(rustc_private)]

use pcg_evaluation::MutatorData;

use pcg_evaluation::mutator::Mutant;
use pcg_evaluation::mutator::MutantRange;
use pcg_evaluation::mutator::Mutator;

use pcg_evaluation::mutator::block_mutable_borrow::BlockMutableBorrow;
use pcg_evaluation::mutator::expiry_order::BorrowExpiryOrder;
use pcg_evaluation::mutator::expiry_order::AbstractExpiryOrder;
use pcg_evaluation::mutator::move_from_borrowed::MoveFromBorrowed;
use pcg_evaluation::mutator::mutably_lend_read::MutablyLendReadOnly;
use pcg_evaluation::mutator::mutably_lend_shared::MutablyLendShared;
use pcg_evaluation::mutator::read_from_write::ReadFromWriteOnly;
use pcg_evaluation::mutator::shallow_exclusive_read::ShallowExclusiveRead;
use pcg_evaluation::mutator::write_to_read::WriteToReadOnly;
use pcg_evaluation::mutator::write_to_shared::WriteToShared;
use pcg_evaluation::mutator::drop_borrowed::DropBorrowed;

use pcg_evaluation::utils::env_feature_enabled;

use std::fs::File;
use std::io::Write;
use std::path::PathBuf;

use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;

use indexmap::map::IndexMap;

use serde::Serialize;

use pcg_evaluation::rustc_interface::borrowck;
use pcg_evaluation::rustc_interface::borrowck::consumers;

use pcg_evaluation::rustc_interface::errors::fallback_fluent_bundle;

use pcg_evaluation::rustc_interface::middle::query::queries::mir_borrowck::ProvidedValue;
use pcg_evaluation::rustc_interface::middle::ty::TyCtxt;
use pcg_evaluation::rustc_interface::middle::util::Providers;

use pcg_evaluation::rustc_interface::session::Session;

use pcg_evaluation::rustc_interface::driver::catch_fatal_errors;
use pcg_evaluation::rustc_interface::driver::Callbacks;
use pcg_evaluation::rustc_interface::driver::DEFAULT_LOCALE_RESOURCES;

use pcg_evaluation::errors::get_registered_errors;
use pcg_evaluation::errors::initialize_error_tracking;
use pcg_evaluation::errors::track_body_error_codes;

use pcg_evaluation::rustc_interface::hir::def_id::CrateNum;

use pcg_evaluation::rustc_interface::driver;
use pcg_evaluation::rustc_interface::driver::Compilation;

use pcg_evaluation::rustc_interface::hir;
use pcg_evaluation::rustc_interface::hir::def_id::LocalDefId;

use pcg_evaluation::rustc_interface::interface::interface::Compiler;
use pcg_evaluation::rustc_interface::interface::Config;

use pcg_evaluation::rustc_interface::ast::Crate;

use pcs::combined_pcs::BodyWithBorrowckFacts;
use pcs::run_combined_pcs;
use pcs::FpcsOutput;

thread_local! {
    pub static BODIES:
        RefCell<HashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
        RefCell::new(HashMap::default());
}

#[derive(Serialize)]
enum BorrowCheckInfo {
    NoRun,
    Passed,
    Failed { error_codes: HashSet<String> },
}

#[derive(Serialize)]
struct LogEntry {
    mutation_type: String,
    borrow_check_info: BorrowCheckInfo,
    definition: String,
    range: MutantRange,
    info: String,
}

struct MutatorCallbacks {
    mutators: Vec<Box<dyn Mutator + Send>>,
    results_dir: PathBuf,
}

fn mir_borrowck<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> ProvidedValue<'tcx> {
    let body_with_facts = {
        let consumer_opts = consumers::ConsumerOptions::PoloniusInputFacts;
        consumers::get_body_with_borrowck_facts(tcx, def_id, consumer_opts)
    };
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

fn run_pcg_on_all_fns<'mir, 'tcx>(
    body_map: &'mir HashMap<LocalDefId, BodyWithBorrowckFacts<'tcx>>,
    tcx: TyCtxt<'tcx>,
) {
    if std::env::var("CARGO_CRATE_NAME").is_ok() && std::env::var("CARGO_PRIMARY_PACKAGE").is_err()
    {
        // We're running in cargo, but the Rust file is a dependency (not part of the primary package)

        // For now we don't check dependencies, so we abort

        return;
    }

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

    let mut item_names = vec![];
    for def_id in tcx.hir().body_owners() {
        let kind = tcx.def_kind(def_id);

        match kind {
            hir::def::DefKind::Fn | hir::def::DefKind::AssocFn => {
                let item_name = format!("{}", tcx.def_path_str(def_id.to_def_id()));

                if let Some(body) = body_map.get(&def_id) {
                    let safety = tcx.fn_sig(def_id).skip_binder().safety();

                    if safety == hir::Safety::Unsafe {
                        continue;
                    }

                    let _ = run_combined_pcs(
                        body,
                        tcx,
                        vis_dir.map(|dir| format!("{}/{}", dir, item_name)),
                    );
                    item_names.push(item_name);
                }
            },
            _ => {},
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

fn cargo_crate_name() -> Option<String> {
    std::env::var("CARGO_CRATE_NAME").ok()
}

// TODO interleave pcg generation and mutation testing
fn run_mutation_tests<'tcx>(
    tcx: TyCtxt<'tcx>,
    compiler: &Compiler,
    mutators: &mut Vec<Box<dyn Mutator + Send>>,
    results_dir: &PathBuf,
) {
    if in_cargo_crate() && std::env::var("CARGO_PRIMARY_PACKAGE").is_err() {
        // We're running in cargo, but not compiling the primary package
        // We don't want to check dependencies, so abort
        return;
    }

    fn run_mutation_tests_for_body<'mir, 'tcx>(
        tcx: TyCtxt<'tcx>,
        compiler: &Compiler,
        mutators: &mut Vec<Box<dyn Mutator + Send>>,
        mutants_log: &mut IndexMap<String, LogEntry>,
        mutator_results: &mut HashMap<String, MutatorData>,
        passed_bodies: &mut HashMap<LocalDefId, BodyWithBorrowckFacts<'tcx>>,
        def_id: LocalDefId,
        body_with_borrowck_facts: &BodyWithBorrowckFacts<'tcx>,
        mut analysis: FpcsOutput<'mir, 'tcx>,
    ) {
        for mutator in mutators.iter_mut() {
            let mutator_data = mutator_results
                .entry(mutator.name())
                .or_insert(MutatorData {
                    instances: 0,
                    passed: 0,
                    failed: 0,
                    panicked: 0,
                    error_codes: HashSet::new(),
                });
            let body = &body_with_borrowck_facts.body;
            let promoted = &body_with_borrowck_facts.promoted;

            let (numerator, denominator) = mutator.run_ratio();
            let mutants = mutator.generate_mutants(tcx, &mut analysis, &body);

            for Mutant { body, range, info } in mutants {
                mutator_data.instances += 1;
                let do_borrowck = env_feature_enabled("DO_BORROWCK").unwrap_or(true);
                // don't do this at home, kids
                let maybe_panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let borrow_check_info = if rand::random_ratio(numerator, denominator)
                        && do_borrowck
                    {
                        track_body_error_codes(def_id);

                        let (borrowck_result, mutant_body_with_borrowck_facts) = {
                            let consumer_opts = consumers::ConsumerOptions::PoloniusInputFacts;
                            borrowck::do_mir_borrowck(tcx, &body, &promoted, Some(consumer_opts))
                        };
                        if let Some(_) = borrowck_result.tainted_by_errors {
                            mutator_data.failed += 1;
                            let error_codes = get_registered_errors();
                            for error_code in error_codes.iter() {
                                mutator_data.error_codes.insert(error_code.to_string());
                            }
                            BorrowCheckInfo::Failed {
                                error_codes: error_codes
                                    .iter()
                                    .map(|err_code| err_code.to_string())
                                    .collect(),
                            }
                        } else {
                            mutator_data.passed += 1;
                            if env_feature_enabled("PCG_VISUALIZATION").unwrap_or(false) {
                                passed_bodies
                                    .insert(def_id, (*mutant_body_with_borrowck_facts.unwrap()).into());
                            }
                            BorrowCheckInfo::Passed
                        }
                    } else {
                        BorrowCheckInfo::NoRun
                    };
                    let log_entry = LogEntry {
                        mutation_type: mutator.name(),
                        borrow_check_info: borrow_check_info,
                        definition: format!("{def_id:?}"),
                        range: range,
                        info: info,
                    };
                    if env_feature_enabled("MUTANTS_LOG").unwrap_or(false) {
                        mutants_log.insert(mutants_log.len().to_string(), log_entry);
                    }
                    compiler.sess.dcx().reset_err_count(); // cursed
                }));

                if let Err(_) = maybe_panic {
                    mutator_data.panicked += 1;
                }
            }
        }
    }

    let mut mutator_results: HashMap<String, MutatorData> = HashMap::new();
    let mut mutants_log: IndexMap<String, LogEntry> = IndexMap::new();
    let mut passed_bodies: HashMap<LocalDefId, BodyWithBorrowckFacts<'tcx>> = HashMap::new();

    let body_map: HashMap<LocalDefId, BodyWithBorrowckFacts<'tcx>> =
        unsafe { std::mem::transmute(BODIES.take()) };

    initialize_error_tracking();

    for def_id in tcx.hir().body_owners() {
        let kind = tcx.def_kind(def_id);
        let item_name = tcx.def_path_str(def_id.to_def_id()).to_string();
        if !item_name.contains("de::deserialize_map") {
            match kind {
                hir::def::DefKind::Fn | hir::def::DefKind::AssocFn => {
                    let body_with_borrowck_facts = body_map.get(&def_id).unwrap();

                    let safety = tcx.fn_sig(def_id).skip_binder().safety();
                    if safety == hir::Safety::Unsafe {
                        continue;
                    }
                    std::env::set_var("PCG_VALIDITY_CHECKS", "false");
                    let analysis = run_combined_pcs(body_with_borrowck_facts, tcx, None);

                    run_mutation_tests_for_body(
                        tcx,
                        compiler,
                        mutators,
                        &mut mutants_log,
                        &mut mutator_results,
                        &mut passed_bodies,
                        def_id,
                        body_with_borrowck_facts,
                        analysis,
                    );
                }
                _ => {},
            }
        }
    }

    if env_feature_enabled("PCG_VISUALIZATION").unwrap_or(false) {
        run_pcg_on_all_fns(&passed_bodies, tcx);
    }

    let crate_name = cargo_crate_name().unwrap_or("crate".to_string());

    let mutants_log_path = results_dir
        .join(crate_name.clone() + "-mutants")
        .with_extension("json");
    let mut mutants_log_file =
        File::create(&mutants_log_path).expect("Failed to create output file");
    let mutants_log_string = serde_json::to_string_pretty(&mutants_log).unwrap();
    mutants_log_file
        .write_all(mutants_log_string.as_bytes())
        .expect("Failed to write results to file");

    let mutator_results_path = results_dir.join(crate_name).with_extension("json");
    let mut mutator_results_file =
        File::create(&mutator_results_path).expect("Failed to create output file");
    let mutator_results_string = serde_json::to_string_pretty(&mutator_results).unwrap();
    mutator_results_file
        .write_all(mutator_results_string.as_bytes())
        .expect("Failed to write results to file");
}

impl Callbacks for MutatorCallbacks {
    fn config(&mut self, config: &mut Config) {
        assert!(config.override_queries.is_none());
        config.override_queries = Some(set_mir_borrowck);
    }

    fn after_crate_root_parsing<'tcx>(
        &mut self,
        compiler: &Compiler,
        _crate: &Crate,
    ) -> Compilation {
        let fallback_bundle = fallback_fluent_bundle(DEFAULT_LOCALE_RESOURCES.to_vec(), false);
        compiler
            .sess
            .dcx()
            .make_silent(fallback_bundle, None, false);
        Compilation::Continue
    }

    fn after_analysis(&mut self, compiler: &Compiler, tcx: TyCtxt<'_>) -> Compilation {
        run_mutation_tests(tcx, compiler, &mut self.mutators, &self.results_dir);
        if in_cargo_crate() {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}

fn in_cargo_crate() -> bool {
    // true
    std::env::var("CARGO_CRATE_NAME").is_ok()
}

fn main() {
    let mut rustc_args = vec!["rustc".to_string()];

    if !std::env::args().any(|arg| arg.starts_with("--edition=")) {
        rustc_args.push("--edition=2018".to_string());
    }
    if env_feature_enabled("PCG_POLONIUS").unwrap_or(false) {
        rustc_args.push("-Zpolonius".to_string());
    }
    if !in_cargo_crate() {
        rustc_args.push("-Zno-codegen".to_string());
    }

    rustc_args.extend(std::env::args().skip(1));

    let results_dir = match std::env::var("RESULTS_DIR") {
        Ok(str) => str.into(),
        _ => std::env::current_dir().unwrap(),
    };

    // NOTE: MutablyLendReadOnly and WriteToReadOnly are no longer valid
    let mut callbacks = MutatorCallbacks {
        mutators: vec![
            // Box::new(BorrowExpiryOrder),
            // Box::new(AbstractExpiryOrder),
            // Box::new(MutablyLendShared),
            // Box::new(ReadFromWriteOnly),
            // Box::new(WriteToShared),
            // Box::new(MoveFromBorrowed),
            // Box::new(ShallowExclusiveRead),
            // Box::new(BlockMutableBorrow),
        ],
        results_dir: results_dir,
    };
    driver::RunCompiler::new(&rustc_args, &mut callbacks).run();
}
