#!/usr/bin/env bash

case "$(uname -m)" in
  x86_64)
    cargo build
    ;;
  *)
    echo "Mutation testing is only supported on x86"
    exit 0
    ;;
esac
