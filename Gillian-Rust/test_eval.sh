RUST_LOG=0 opam exec -- dune exec gillian-rust -- verify ../examples/verification/vec_std_proph.rs --prophecies -l disabled
RUST_LOG=0 opam exec -- dune exec gillian-rust -- verify ../examples/verification/list_std_proph.rs --prophecies -l disabled
RUST_LOG=0 opam exec -- dune exec gillian-rust -- verify ../examples/verification/list_std.rs -l disabled
RUST_LOG=0 opam exec -- dune exec gillian-rust -- verify ../examples/verification/wp.rs -l disabled
RUST_LOG=0 opam exec -- dune exec gillian-rust -- verify ../examples/verification/wp_proph.rs -l disabled --prophecies