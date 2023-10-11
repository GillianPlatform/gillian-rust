set -e

cd Gillian-Rust
esy x gillian-rust verify ../examples/verification/list_std.rs -l disabled
esy x gillian-rust verify ../examples/verification/wp.rs -l disabled
esy x gillian-rust verify ../examples/verification/wp_proph.rs -l disabled --prophecies