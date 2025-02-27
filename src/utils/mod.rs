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
