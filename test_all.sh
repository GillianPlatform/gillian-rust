set -e

cd Gillian-Rust
RUST_LOG=0 opam exec -- dune exec gillian-rust -- verify ../tests/noproph/list_std.rs -l disabled
RUST_LOG=0 opam exec -- dune exec gillian-rust -- verify ../tests/noproph/wp.rs -l disabled
RUST_LOG=0 opam exec -- dune exec gillian-rust -- verify ../tests/proph/wp_proph.rs -l disabled --prophecies
