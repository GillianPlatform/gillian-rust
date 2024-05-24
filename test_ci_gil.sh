#!/bin/bash

set -e
# Runs Gillian-Rust on the generated outputs
cd Gillian-Rust

for file in ../tests/noproph/*.stdout; do
	opam exec -- dune exec gillian-rust -- verify $file -l disabled
done

for file in ../tests/proph/*.stdout; do
	opam exec -- dune exec gillian-rust -- verify $file -l disabled --prophecies
done