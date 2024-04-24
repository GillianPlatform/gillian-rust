set -e

cd Gillian-Rust
opam exec -- dune exec gillian-rust -- verify ../examples/verification/list_std.rs -l disabled
opam exec -- dune exec gillian-rust -- verify ../examples/verification/wp.rs -l disabled
opam exec -- dune exec gillian-rust -- verify ../examples/verification/wp_proph.rs -l disabled --prophecies