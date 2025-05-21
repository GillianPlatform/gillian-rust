#!/usr/bin/env bash
set -e

OFFLINE="--offline"
INIT_OPAM=0

if [ $# -gt 0 ]; then
  if [ "$1" = "--init" ]; then
    OFFLINE=""
    OPAM_ARGS=1
  else
    echo "Error: Unknown argument '$1'"
    echo "Usage: $0 [--init]"
    exit 1
  fi
fi

cargo build ${OFFLINE}
cargo install --path rust_to_gil ${OFFLINE}
cargo install --path cargo-gillian ${OFFLINE}
cargo test --test ui ${OFFLINE} -- --bless

cd Gillian-Rust
if [ "${INIT_OPAM}" -eq 1 ]; then
  echo "Initializing opam dependencies..."
  opam install ./gillian-rust.opam.locked --with-test --with-doc --with-dev --deps-only -y
  opam install ocaml-lsp-server ocamformat.0.26.1 -y
fi

opam install ./gillian-rust.opam.locked -y