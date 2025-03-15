# Gillian-Rust

## Build instructions

To build this project, you need to build:
1) the Rust-to-GIL compiler (written in Rust, using directly the Rust compiler API); and
2) the Gillian-Rust backend, based on the [Gillian framework](https://github.com/GillianPlatform/Gillian)  written in OCaml.

### Building the compiler

To build the compiler, you first need to [install Rust](https://www.rust-lang.org/tools/install).
Then, you should be able to simply build and test the compiler. This will automatically install the exact version of the Rust compiler that is required:
```sh
cargo build
cargo test
cargo test --test ui -- --check
```

### Building the backend


#### Installing OCaml and dependencies

To build the Gillian-Rust backend, you first need to [install OCaml](https://ocaml.org/docs/installing-ocaml).

Then, go to the `Gillian-Rust` folder, create a local switch and install the dependencies. This will automatically install the appropriate version of the OCaml compiler.
```sh
opam switch create . --deps-only
```

#### Installing z3

To run Gillian-Rust, you need to install globally a version of `z3`. Gillian-Rust was thoroughly tested with z3 4.12.4, but other versions should work too.

You can check if you have z3 installed by running
```sh
z3 --version
# Z3 version 4.13.4 - 64 bit
```

If not, you can install it as follows:
```sh
# MacOS
brew install z3

# linux, x86_64
cd ~ && curl -L -o z3.zip "https://github.com/Z3Prover/z3/releases/download/z3-4.12.4/z3-4.12.4-x64-glibc-2.35.zip" && unzip z3.zip -d /opt/z3 && rm z3.zip && sudo ln -s /opt/z3/z3-4.12.4-x64-glibc-2.35/bin/z3 /usr/local/bin/z3

# linux, arm64
cd ~ && curl -L -o z3.zip "https://github.com/Z3Prover/z3/releases/download/z3-4.12.4/z3-4.12.4-arm64-glibc-2.34.zip" && unzip z3.zip -d /opt/z3 && rm z3.zip && sudo ln -s /opt/z3/z3-4.12.4-arm64-glibc-2.34/bin/z3 /usr/local/bin/z3
```

#### Building the Gillian-Rust backend

Still in the Gillian-Rust folder, run:
```sh
dune build @all
```

Then, in the root folder, run the following command to run all our tests and case studies:
```sh
./test_ci_gil.sh
```