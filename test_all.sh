set -e

cd Gillian-Rust
esy x gillian-rust bulk-exec ../examples/concrete

esy x gillian-rust verify ../examples/verification/list_std_mono.rs -l disabled
esy x gillian-rust verify ../examples/verification/list_std_poly.rs -l disabled
esy x gillian-rust verify ../examples/verification/list_std_shallow_repr.rs -l disabled