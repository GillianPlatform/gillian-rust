#!/usr/bin/env bash
set -exu
set -o pipefail

dir_path="${1%/*}"
file_name="${1##*/}"
file_base="${file_name%.*}"

cargo test --test ui -- --bless $1

cd Gillian-Rust

opam exec -- dune build @install
opam exec -- dune exec -- gillian-rust verify ../tests/${dir_path}/${file_base}.stdout ${@:2}