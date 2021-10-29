EXAMPLE_FILES = $(shell ls examples/*.rs)
EXAMPLE_TASKS = $(basename $(notdir ${EXAMPLE_FILES}))
RUSTC = $(shell rustup which rustc)
SYSROOT = $(shell ${RUSTC} --print sysroot)
LIBDIR = "lib"
BACKEND = ${LIBDIR}/librtg.dylib
ARGS =  -C panic=abort --sysroot ${SYSROOT} -Z codegen-backend=${BACKEND}

.PHONY: $(EXAMPLE_TASKS) build

all: $(EXAMPLE_TASKS)

$(EXAMPLE_TASKS): build
	@${RUSTC} ${ARGS} examples/$@.rs --crate-type lib --out-dir output

build:
	cargo build --out-dir ${LIBDIR} -Z unstable-options
	
help:
	${RUSTC} --help