for FILE in examples/*.rs; do
  RUST_LOG=off cargo run -- --out-dir output $FILE
done;