use serde_derive::{Deserialize, Serialize};

mod common;
use common::{get, run_on_crate};
use common::{RunOnCrateOptions, Target};

use std::fs::File;
use std::io::Write;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Mutex;

use rayon::iter::IndexedParallelIterator;
use rayon::iter::IntoParallelIterator;
use rayon::iter::ParallelIterator;

use chrono::Local;
use derive_more::Deref;

#[test]
pub fn test_crates() {
    run_on_crate(
        "arrayvec",
        "0.7.6",
        Some("2025-03-13"),
        RunOnCrateOptions::RunPCG {
            target: Target::Release,
            validity_checks: false,
            function: None,
            extra_env_vars: vec![],
        },
    );
}

#[derive(Serialize)]
struct TopCratesResult {
    succeeded: Vec<String>,
    failed: Vec<String>,
}

#[test]
pub fn top_crates() {
    let num_crates = std::env::var("PCG_NUM_TEST_CRATES").unwrap_or("250".to_string());
    let parallelism = std::env::var("PCG_TEST_CRATE_PARALLELISM").unwrap_or("20".to_string());
    top_crates_parallel(
        num_crates.parse().unwrap(),
        Some("2025-03-13"),
        parallelism.parse().unwrap(),
    )
}

pub fn top_crates_parallel(n: usize, date: Option<&str>, parallelism: usize) {
    let stats = Arc::new(Mutex::new(TopCratesResult {
        succeeded: vec![],
        failed: vec![],
    }));
    std::fs::create_dir_all("tmp").unwrap();
    rayon::ThreadPoolBuilder::new()
        .num_threads(parallelism)
        .build_global()
        .unwrap();
    let top_crates: Vec<_> = Crates::top(n, date).to_vec();

    // TODO: Fix the slowness
    // let mut extra_env_vars = vec![
    //     ("PCG_SKIP_FUNCTION".to_string(), "<ir::comp::CompInfo as codegen::CodeGenerator>::codegen".to_string()),
    // ];

    top_crates
        .into_par_iter()
        .panic_fuse()
        .enumerate()
        .for_each(|(i, krate)| {
            let version = krate.version();
            println!("Starting: {i} ({})", krate.name);
            if let Ok(str) = std::env::var("RESULTS_DIR") {
                let results_dir = str.to_string();
                std::env::set_var("RESULTS_DIR", results_dir);
            }
            run_on_crate(
                &krate.name,
                version,
                date,
                RunOnCrateOptions::RunPCG {
                    target: Target::Release,
                    validity_checks: false,
                    function: None,
                    extra_env_vars: vec![],
                },
            );
            let mut stats = stats.lock().unwrap();
            stats.succeeded.push(krate.name.clone());
            println!("Finished: {i} ({})", krate.name);
        });

        // let path = {
        //     let results_dir = str.to_string();
        //     Path::new(&results_dir).join("top-crates-results.txt")
        // };
        // let mut output_file = File::create(&path).unwrap();

        // let stats_string = serde_json::to_string_pretty(&stats.into_inner().unwrap()).unwrap();
        // output_file
        //     .write_all(stats_string.as_bytes())
        //     .expect("Failed to write results to file");
}

// pub fn top_crates_range(range: usize, date: &str) {
//     let mut stats = TopCratesResult { succeeded: vec![], failed: vec![] };
//     if let Ok(str) = std::env::var("RESULTS_DIR") {
//         std::fs::create_dir_all("tmp").unwrap();
//         let mut top_crates: Vec<_> = Crates::top(range, Some(date)).to_vec();
//         let mut thunks: Vec<_> = top_crates
//             .drain(..)
//             .map(|krate| {
//                 let results_dir = str.to_string();
//                 let version = krate.version.unwrap_or(krate.newest_version);
//                 let date_string = date.to_string();
//                 (krate.name.clone(),
//                  || {
//                     std::thread::spawn(move || {
//                         std::env::set_var("RESULTS_DIR", results_dir);
//                         run_on_crate(&krate.name, &version, Some(date_string.as_str()),
//                                      RunOnCrateOptions::RunPCG {
//                                          target: Target::Release,
//                                          validity_checks: false,
//                                      });
//                     })
//                  })
//             }).collect();

//         let mut handles: Vec<_> = vec![];

//         while !thunks.is_empty() || !handles.is_empty() {
//             if handles.len() < MAX_CONCURRENT_THREADS {
//                 if let Some((name, thunk)) = thunks.pop() {
//                     handles.push((name, thunk()))
//                 }
//             }
//             for i in 0..handles.len() {
//                 if let Some((_, handle)) = handles.get_mut(i) {
//                     if handle.is_finished() {
//                         let (name, handle) = handles.remove(i);
//                         match handle.join() {
//                             Err(_) => stats.failed.push(name.clone()),
//                             _ => stats.succeeded.push(name)
//                         }
//                     }
//                 }
//             }
//         }

//         let path = {
//             let results_dir = str.to_string();
//             Path::new(&results_dir).join("top-crates-results.txt")
//         };
//         let mut output_file = File::create(&path).unwrap();

//         let stats_string = serde_json::to_string_pretty(&stats).unwrap();
//         output_file
//             .write_all(stats_string.as_bytes())
//             .expect("Failed to write results to file");
//     }
// }

/// A create on crates.io.
#[derive(Debug, Deserialize, Serialize, Clone)]
struct Crate {
    #[serde(rename = "id")]
    name: String,
    #[serde(rename = "max_stable_version")]
    version: Option<String>,
    #[serde(rename = "newest_version")]
    newest_version: String,
}

impl Crate {
    fn version(&self) -> &str {
        self.version.as_ref().unwrap_or(&self.newest_version)
    }
}

/// The list of crates from crates.io
#[derive(Debug, Deref, Deserialize)]
struct Crates {
    crates: Vec<Crate>,
}

const PAGE_SIZE: usize = 100;

fn download_crates(n: usize) -> Vec<Crate> {
    let mut all_crates = Vec::new();
    let mut page = 1;

    while all_crates.len() < n {
        let url = format!(
            "https://crates.io/api/v1/crates?page={}&per_page={PAGE_SIZE}&sort=downloads",
            page,
        );
        let resp = get(&url).expect("Could not fetch top crates");
        assert!(
            resp.status().is_success(),
            "Response status: {}",
            resp.status()
        );
        let page_crates = match serde_json::from_reader::<_, Crates>(resp) {
            Ok(page_crates) => page_crates,
            Err(e) => panic!("Invalid JSON {e}"),
        };
        assert_eq!(page_crates.crates.len(), PAGE_SIZE);
        all_crates.extend(page_crates.crates);
        page += 1;
    }

    all_crates
}

fn get_cache_path(date: &str) -> PathBuf {
    PathBuf::from("pcg/tests/top-crates").join(format!("{date}.json"))
}

fn read_from_cache(cache_path: &Path) -> Option<Vec<Crate>> {
    if let Ok(file) = std::fs::File::open(cache_path) {
        return Some(serde_json::from_reader::<_, Vec<Crate>>(file).unwrap());
    }
    None
}

fn write_to_cache(cache_path: PathBuf, crates: &[Crate]) {
    let file = std::fs::File::create(&cache_path).unwrap_or_else(|err| {
        panic!(
            "Failed to create cache file {}: {}",
            cache_path.display(),
            err
        );
    });
    serde_json::to_writer(file, &crates).unwrap();
}

impl Crates {
    pub fn top(n: usize, date: Option<&str>) -> Crates {
        let today = Local::now().format("%Y-%m-%d").to_string();
        let date = date.unwrap_or(today.as_str());
        let cache_path = get_cache_path(date);
        let crates = read_from_cache(&cache_path).unwrap_or_else(|| {
            assert_eq!(
                date,
                today,
                "Cannot get crates from {} because the JSON file {} doesn't exist",
                date,
                cache_path.display()
            );
            let crates = download_crates(n);
            write_to_cache(cache_path, &crates);
            crates
        });
        assert!(
            crates.len() >= n,
            "Tried to get {} crates but only had {}",
            n,
            crates.len()
        );
        Crates {
            crates: crates[..n].to_vec(),
        }
    }
}
