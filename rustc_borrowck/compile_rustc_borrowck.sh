#!/usr/bin/env bash

SMALLVEC_PATH=$(find "$(rustc --print sysroot)/lib/rustlib/$(rustc -vV | awk '/host:/ {print $2}')/lib" -type f -name 'libsmallvec-*.rmeta')
echo $SMALLVEC_PATH
RUSTFLAGS="--extern smallvec=$SMALLVEC_PATH" cargo build
