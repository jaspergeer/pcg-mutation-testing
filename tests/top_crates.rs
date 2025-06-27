use serde_derive::{Deserialize, Serialize};

mod common;
use common::{get, run_on_crate};
use common::{RunOnCrateOptions, Target};

use std::path::Path;
use std::path::PathBuf;

use rayon::iter::IndexedParallelIterator;
use rayon::iter::IntoParallelIterator;
use rayon::iter::ParallelIterator;

use chrono::Local;
use derive_more::Deref;

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
    std::fs::create_dir_all("tmp").unwrap();
    rayon::ThreadPoolBuilder::new()
        .num_threads(parallelism)
        .build_global()
        .unwrap();
    let top_crates: Vec<_> = Crates::top(n, date).to_vec();

    // TODO: Fix the slowness
    let extra_env_vars = vec![
        ("PCG_SKIP_FUNCTION".to_string(), "<ir::comp::CompInfo as codegen::CodeGenerator>::codegen".to_string()),
    ];

    let results_dir: PathBuf = match std::env::var("RESULTS_DIR") {
        Ok(str) => str.into(),
        _ => "data".into(),
    };
    let results_dir = std::path::absolute(&results_dir).expect("Failed to convert to absolute path");
    if std::path::Path::new(&results_dir).exists() {
        std::fs::remove_dir_all(&results_dir)
            .expect("Failed to delete data directory contents");
    }
    std::fs::create_dir_all(&results_dir).expect("Failed to create data directory");

    top_crates
        .into_par_iter()
        .panic_fuse()
        .enumerate()
        .for_each(|(i, krate)| {
            let version = krate.version();
            println!("Starting: {i} ({})", krate.name);
            std::env::set_var("RESULTS_DIR", results_dir.clone());
            run_on_crate(
                &krate.name,
                version,
                date,
                RunOnCrateOptions::RunPCG {
                    target: Target::Release,
                    validity_checks: false,
                    function: None,
                    extra_env_vars: extra_env_vars.clone(),
                },
            );
            println!("Finished: {i} ({})", krate.name);
        });
}

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
    PathBuf::from("../pcg/tests/top-crates").join(format!("{date}.json"))
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
