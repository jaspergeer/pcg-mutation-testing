#![feature(rustc_private)]
#![feature(let_chains)]

pub mod rustc_interface;
pub mod errors;
pub mod utils;
pub mod mutator;

use serde_derive::Serialize;
use serde_derive::Deserialize;

use std::collections::HashSet;

pub fn env_feature_enabled(feature: &str) -> Option<bool> {
    match std::env::var(feature) {
        Ok(val) => {
            if val.is_empty() {
                None
            } else {
                match val.as_str() {
                    "true" | "1" => Some(true),
                    "false" | "0" => Some(false),
                    other => panic!("Environment variable {} has unexpected value: '{}'. Expected one of: true, false, 1, 0, or empty string", feature, other)
                }
            }
        },
        Err(_) => None
    }
}

#[derive(Serialize, Deserialize)]
pub struct MutatorData {
    pub instances: i64,
    pub passed: i64,
    pub failed: i64,
    pub error_codes: HashSet<String>,
}
