#![feature(rustc_private)]

use pcg_evaluation::MutatorData;

use std::fs::read_dir;
use std::fs::File;

use std::io;
use std::io::BufReader;
use std::io::Read;
use std::io::Write;

use serde_json::from_reader;

use std::collections::HashMap;
use std::collections::HashSet;

use std::path::Path;

#[test]
fn compile_results() -> io::Result<()> {
    let results_dir = match std::env::var("RESULTS_DIR") {
        Ok(str) => str.into(),
        _ => std::env::current_dir().unwrap(),
    };

    let path = Path::new(&results_dir).join("mutation-testing-results.json");
    let mut output_file = File::create(&path)?;

    let mut mutator_results: HashMap<String, MutatorData> = HashMap::new();

    let path = Path::new(&results_dir);
    if path.is_dir() {
        for entry in std::fs::read_dir(path)? {
            println!("{:?}", path);
            let entry = entry?;
            let path = entry.path();
            if !path.is_dir() && !(*path.to_string_lossy()).ends_with("-mutants.json") {
                let input_file = File::open(path)?;
                let mut buf_reader = BufReader::new(input_file);
                if let Ok(mut file_results) = from_reader::<_, HashMap<String, MutatorData>>(buf_reader) {
                    for (mutator_name, result) in file_results.drain()  {
                        let entry = mutator_results
                          .entry(mutator_name)
                          .or_insert(MutatorData {
                              instances: 0,
                              passed: 0,
                              failed: 0,
                              panicked: 0,
                              error_codes: HashSet::new(),
                          });
                        entry.instances += result.instances;
                        entry.passed += result.passed;
                        entry.failed += result.failed;
                        entry.panicked += result.panicked;
                        entry.error_codes.extend(result.error_codes);
                    }
                }
            }
        }
    }
    let mutator_results_string = serde_json::to_string_pretty(&mutator_results)?;
    output_file
        .write_all(mutator_results_string.as_bytes())
        .expect("Failed to write results to file");
    Ok(())
}
