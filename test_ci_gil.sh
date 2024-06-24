#!/bin/bash

set -euo pipefail
# Runs Gillian-Rust on the generated outputs
cd Gillian-Rust

dune build @install

for file in ../tests/noproph/*.stdout; do
	
	echo ""
	echo ""
	echo "Noproph verify: ${file%.stdout}.rs"
	if ! grep -q "//?gil:ignore" "${file%.stdout}.rs"; then
		opam exec -- dune exec gillian-rust -- verify $file -l disabled
	else
		echo "Skipping ${file%.stdout}.rs"
	fi
done

for file in ../tests/proph/*.stdout; do
	
	echo ""
	echo ""
	echo "Proph verify: ${file%.stdout}.rs"
	if ! grep -q "//?gil:ignore" "${file%.stdout}.rs"; then
		opam exec -- dune exec gillian-rust -- verify $file -l disabled --prophecies
	else
		echo "Skipping ${file%.stdout}.rs"
	fi

done