#!/bin/bash

set -euo pipefail
# Runs Gillian-Rust on the generated outputs
cd Gillian-Rust

for file in ../tests/noproph/*.stdout; do
	
	echo ""
	echo ""
	echo "Noproph verify: $file"
	opam exec -- dune exec gillian-rust -- verify $file -l disabled
	
done

for file in ../tests/proph/*.stdout; do
	
	echo ""
	echo ""
	echo "Proph verify: $file"
	opam exec -- dune exec gillian-rust -- verify $file -l disabled --prophecies

done