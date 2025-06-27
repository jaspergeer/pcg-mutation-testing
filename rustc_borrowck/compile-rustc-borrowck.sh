#!/usr/bin/env bash

echo $SMALLVEC_PATH

case "$arch" in
  x86_64)
    cargo build
    ;;
  aarch64)
    SMALLVEC_PATH="/usr/local/rustup/toolchains/nightly-2024-12-15-aarch64-unknown-linux-gnu/lib/rustlib/aarch64-unknown-linux-gnu/lib/libsmallvec-37653000af668d0c.rmeta"
    RUSTFLAGS="--extern smallvec=$SMALLVEC_PATH" cargo build
    ;;
  *)
    echo "Unsupported architecture: $arch"
    exit 1
    ;;
esac

