#![feature(rustc_private)]

use std::borrow::BorrowMut;
use std::io::Write;
use std::{fs::File, path::{Path, PathBuf}};
use std::process::Command;

use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;

use std::process::ExitCode;

use std::sync::Arc;

use serde::Serialize;
use serde::Deserialize;
use serde_json::Map as JSONMap;

use pcg_evaluation::rustc_interface::borrowck;
use pcg_evaluation::rustc_interface::borrowck::consumers;

use pcg_evaluation::rustc_interface::data_structures::fx::FxHashMap;
use pcg_evaluation::rustc_interface::data_structures::fx::FxHashSet;

use pcg_evaluation::rustc_interface::errors::registry;
use pcg_evaluation::rustc_interface::errors::fallback_fluent_bundle;
use pcg_evaluation::rustc_interface::errors::emitter::Emitter;

use pcg_evaluation::rustc_interface::middle::util;
use pcg_evaluation::rustc_interface::middle::mir;

use pcg_evaluation::rustc_interface::middle::ty;
use pcg_evaluation::rustc_interface::middle::ty::Ty;
use pcg_evaluation::rustc_interface::middle::ty::Region;
use pcg_evaluation::rustc_interface::middle::ty::RegionKind;

use pcg_evaluation::rustc_interface::middle::mir::Place as MirPlace;
use pcg_evaluation::rustc_interface::middle::mir::PlaceRef;
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

use pcg_evaluation::rustc_interface::dataflow::ResultsCursor;

use pcg_evaluation::rustc_interface::session;
use pcg_evaluation::rustc_interface::session::config;
use pcg_evaluation::rustc_interface::session::Session;

use pcg_evaluation::rustc_interface::index::IndexVec;
use pcg_evaluation::rustc_interface::driver::DEFAULT_LOCALE_RESOURCES;
use pcg_evaluation::rustc_interface::driver::Callbacks;
use pcg_evaluation::rustc_interface::driver::catch_fatal_errors;

use pcg_evaluation::errors::initialize_error_tracking;
use pcg_evaluation::errors::track_body_error_codes;
use pcg_evaluation::errors::get_registered_errors;

use pcg_evaluation::rustc_interface::hir::def_id::CrateNum;

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
use pcs::run_combined_pcs;
use pcs::combined_pcs::BodyWithBorrowckFacts;
use pcs::combined_pcs::PCGNode;
use pcs::combined_pcs::PCGNodeLike;
use pcs::free_pcs::PcgLocation;
use pcs::free_pcs::PcgBasicBlock;
use pcs::free_pcs::CapabilityKind;
use pcs::FpcsOutput;

use pcs::borrow_pcg::borrow_pcg_edge::LocalNode;
use pcs::borrow_pcg::borrow_pcg_edge::BorrowPCGEdgeLike;
use pcs::borrow_pcg::graph::BorrowsGraph;
use pcs::borrow_pcg::edge::kind::BorrowPCGEdgeKind;
use pcs::borrow_pcg::edge_data::EdgeData;
use pcs::utils::PlaceRepacker;
use pcs::utils::place::Place as PCGPlace;
use pcs::utils::maybe_remote::MaybeRemotePlace;
use pcs::utils::maybe_old::MaybeOldPlace;

use rand::rng;
use rand::Rng;

thread_local! {
    pub static BODIES:
        RefCell<HashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
        RefCell::new(HashMap::default());
}

#[derive(Serialize, Deserialize)]
struct CrateMutantsData {
    name: String,
    failed: usize,
    passed: usize
}

#[derive(Serialize, Deserialize)]
enum BorrowCheckInfo {
    Passed,
    Failed { error_codes: HashSet<String> }
}

#[derive(Serialize, Deserialize)]
struct LogEntry {
    mutation_type: String,
    borrow_check_result: BorrowCheckInfo,
    definition: String,
    location: MutantLocation,
    info: String
}

#[derive(Serialize, Deserialize)]
struct MutantLocation {
    basic_block: usize,
    statement_index: usize
}

struct Mutant<'tcx> {
    body: Body<'tcx>,
    location: MutantLocation,
    info: String
}

trait Mutator {
    fn generate_mutants<'tcx>(&mut self, tcx: &TyCtxt<'tcx>, fpcs_bb: &PcgBasicBlock<'tcx>, body: &Body<'tcx>) -> Vec<Mutant<'tcx>>;
    fn run_ratio(&mut self) -> (u32, u32);
    fn name(&mut self) -> String;
}

struct MutableBorrowMutator;

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

            let mut leaf_edges = borrows_graph.frozen_graph().leaf_edges(repacker);
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

fn run_pcg_on_all_fns<'mir, 'tcx>(body_map: &'mir HashMap<LocalDefId, BodyWithBorrowckFacts<'tcx>>, tcx: TyCtxt<'tcx>) -> HashMap<LocalDefId, FpcsOutput<'mir, 'tcx>> {
    let mut item_names = vec![];

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
                    body,
                    tcx,
                    None,
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
                // for bb in analysis.cursor.reachable_blocks.iter() {
                for bb in body.basic_blocks.indices() {
                    let (numerator, denominator) = mutator.run_ratio();
                    if rand::rng().random_ratio(numerator, denominator) {
                        if let Result::Ok(Some(fpcs_bb)) = analysis.get_all_for_bb(bb) {
                            eprintln!("Running mutator for def_id: {:?}, bb: {:?}", def_id, bb);
                            let mutants = mutator.generate_mutants(&tcx, &fpcs_bb, &body);
                            for Mutant { body, location, info } in mutants {
                                eprintln!("mutant at {} in {:?}", serde_json::to_value(&location).unwrap(), def_id);
                                track_body_error_codes(*def_id);

                                let _ = catch_fatal_errors(|| {
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
                                });
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
        queries.global_ctxt().unwrap().enter(|tcx| do_mutation_tests(tcx, compiler, &mut self.mutators, &self.results_dir));
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
