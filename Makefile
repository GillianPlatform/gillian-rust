EXAMPLE_FILES = $(shell ls examples/*.rs)
EXAMPLE_TASKS = $(basename $(notdir ${EXAMPLE_FILES}))
RUSTC = $(shell rustup which rustc)
SYSROOT = $(shell ${RUSTC} --print sysroot)
LIBDIR = "lib"
BACKEND = ${LIBDIR}/librtg.dylib
ARGS =  -C panic=abort --sysroot ${SYSROOT} --out-dir output --crate-type lib
RUST_TO_GIL = ${RUSTC} ${ARGS} -Z codegen-backend=${BACKEND}
EMIT_MIR = ${RUSTC} ${ARGS} --emit=mir

.PHONY: $(EXAMPLE_TASKS) build

all: $(EXAMPLE_TASKS)

$(EXAMPLE_TASKS): build
	@${EMIT_MIR} examples/$@.rs
	@${RUST_TO_GIL} examples/$@.rs

build:
	cargo build --out-dir ${LIBDIR} -Z unstable-options
	
help:
	${RUSTC} --help