EXAMPLE_FILES = $(shell ls examples/*.rs)
EXAMPLE_TASKS = $(basename $(notdir ${EXAMPLE_FILES}))

BOOK_FILES = $(shell find book/src -name "*.md")

.PHONY: $(EXAMPLE_TASKS) book book-serve

all: $(EXAMPLE_TASKS) book

$(EXAMPLE_TASKS):
	cargo run -- examples/$@.rs --sysroot ~/.rustup/toolchains/nightly-2021-10-18-x86_64-apple-darwin -C panic=abort
