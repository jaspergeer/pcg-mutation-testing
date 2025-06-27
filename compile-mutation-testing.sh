#!/usr/bin/env bash

RUSTFLAGS="--extern borrowck=../borrowck/target/debug/libborrowck.rlib" cargo build
