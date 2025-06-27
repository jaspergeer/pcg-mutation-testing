#!/usr/bin/env bash

echo $SMALLVEC_PATH

case "$(uname -m)" in
  x86_64)
    SMALLVEC_PATH="/usr/local/rustup/toolchains/nightly-2024-12-15-x86_64-unknown-linux-gnu/lib/rustlib/x86_64-unknown-linux-gnu/lib/libsmallvec-a4281dd51fc18d39.rmeta"
    echo $SMALLVEC_PATH
    exit 1
    RUSTFLAGS="--extern smallvec=$SMALLVEC_PATH" cargo build
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

