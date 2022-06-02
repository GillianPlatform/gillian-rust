EXAMPLE_FILES = $(shell ls examples/*.rs)
EXAMPLE_TASKS = $(basename $(notdir ${EXAMPLE_FILES}))
RUSTC = $(shell rustup which rustc)
OUT_DIR = output
SYSROOT = $(shell ${RUSTC} --print sysroot)
RUSTC_ARGS =  -C panic=abort --sysroot ${SYSROOT} --out-dir ${OUT_DIR} --crate-type lib
EMIT_MIR = ${RUSTC} ${RUSTC_ARGS} --emit=mir
OCAML_DIR = "Gillian-Rust"
GILLIAN_RUST = cd ${OCAML_DIR}; esy x gillian-rust exec -R ./runtime -a
RUST_TO_GIL = cargo run -- --out-dir output 

.PHONY: $(EXAMPLE_TASKS) build

all: $(EXAMPLE_TASKS)

$(EXAMPLE_TASKS): build
	@RUST_LOG=off cargo run -- --out-dir ${OUT_DIR} examples/$@.rs
	${GILLIAN_RUST} ../${OUT_DIR}/$@.gil
	echo "\n\nOUTPUT IN: Gillian-Rust/file.log"

build: build-ocaml

build-ocaml:
	cd ${OCAML_DIR}; esy
	
watch:
	cd ${OCAML_DIR}; esy watch