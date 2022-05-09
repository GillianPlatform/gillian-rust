EXAMPLE_FILES = $(shell ls examples/*.rs)
EXAMPLE_TASKS = $(basename $(notdir ${EXAMPLE_FILES}))
RUSTC = $(shell rustup which rustc)
SYSROOT = $(shell ${RUSTC} --print sysroot)
RUSTC_ARGS =  -C panic=abort --sysroot ${SYSROOT} --out-dir output --crate-type lib
EMIT_MIR = ${RUSTC} ${RUSTC_ARGS} --emit=mir
OCAML_DIR = "Gillian-Rust"
GILLIAN_RUST = cd ${OCAML_DIR}; esy x gillian-rust exec -R ../runtime -a
RUST_TO_GIL = cargo run -- --out-dir output 

.PHONY: $(EXAMPLE_TASKS) build

all: $(EXAMPLE_TASKS)

$(EXAMPLE_TASKS): build
	@${EMIT_MIR} examples/$@.rs
	set -e;\
	FILE=$$(${RUST_TO_GIL} examples/$@.rs | grep "Writing to" | cut -d '"' -f 2);\
	echo "FILE: $${FILE}";\
	${GILLIAN_RUST} ../$${FILE};\
	echo "\n\nOUTPUT IN: Gillian-Rust/file.log"

build: build-ocaml

build-ocaml:
	cd ${OCAML_DIR}; esy
	
watch:
	cd ${OCAML_DIR}; esy watch