#!/usr/bin/env bash

SMALLVEC_PATH="/usr/local/rustup/toolchains/nightly-2024-12-15-aarch64-unknown-linux-gnu/lib/rustlib/aarch64-unknown-linux-gnu/lib/libsmallvec-37653000af668d0c.rmeta"
echo $SMALLVEC_PATH
CARGO_HOME=/usr/local/cargo RUSTUP_HOME=/usr/local/rustup RUSTFLAGS="--extern smallvec=$SMALLVEC_PATH" cargo build
