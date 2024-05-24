#!/bin/bash

cargo build -p rust_to_gil

metadata=$(RUSTC_WRAPPER=./target/debug/rust_to_gil cargo build --manifest-path=tests/Cargo.toml --message-format=json)
ret=$?

if [ $ret -ne 0 ]; then
  echo "Failed to build gilogic"
  RUSTC_WRAPPER=./target/debug/rust_to_gil cargo build --manifest-path=tests/Cargo.toml
  exit 1
fi

artifacts=$(echo $metadata | cargo build --manifest-path tests/Cargo.toml --message-format=json | jq 'select(.reason == "compiler-artifact") | { name: .target.name, filename: .filenames[] | select(. | contains("rmeta"))  }')
gilogic_path=$(echo $artifacts | jq -r 'select(.name == "gilogic") | .filename')
# echo ${gilogic_path%.*}
cargo run -p rust_to_gil -- $1 \
  -Ldependency=./target/debug/deps/ \
  --extern gilogic=${gilogic_path%.*}.rmeta \
  -Zcrate-attr='feature(register_tool)' \
  -Zcrate-attr='register_tool(gillian)' \
  -Zcrate-attr='feature(rustc_attrs)' \
  -Zcrate-attr='allow(internal_features)' \
  -Zcrate-attr='feature(stmt_expr_attributes)' \
  -Zpolonius=next