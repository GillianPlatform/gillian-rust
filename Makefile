EXAMPLE_FILES = $(shell ls examples/*.rs)
EXAMPLE_TASKS = $(basename $(notdir ${EXAMPLE_FILES}))
RUSTC = $(shell rustup which rustc)
SYSROOT = $(shell ${RUSTC} --print sysroot)
LIBDIR = lib
BACKEND = ${LIBDIR}/librtg.dylib
ARGS =  -C panic=abort --sysroot ${SYSROOT} --out-dir output --crate-type lib
RUST_TO_GIL = ${RUSTC} ${ARGS} -Z codegen-backend=${BACKEND}
EMIT_MIR = ${RUSTC} ${ARGS} --emit=mir
OCAML_DIR = "Gillian-Rust"
GILLIAN_RUST = cd ${OCAML_DIR}; esy x gillian-rust exec -R ../runtime -a

.PHONY: $(EXAMPLE_TASKS) build

all: $(EXAMPLE_TASKS)

$(EXAMPLE_TASKS): build
	@${EMIT_MIR} examples/$@.rs
	set -e;\
	FILE=$$(${RUST_TO_GIL} examples/$@.rs | grep "Writing to" | cut -d '"' -f 2);\
	echo "FILE: $${FILE}";\
	${GILLIAN_RUST} ../$${FILE};\
	echo "\n\nOUTPUT IN: Gillian-Rust/file.log"
	

build: build-rust build-ocaml
	
	
build-rust:
	cargo build --out-dir ${LIBDIR} -Z unstable-options

build-ocaml:
	cd ${OCAML_DIR}; esy
	
help:
	${RUSTC} --help