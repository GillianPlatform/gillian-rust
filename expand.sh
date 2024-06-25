#!/usr/bin/env bash

rustc $1 \
  -Ldependency=./target/debug/deps/ \
  --extern gilogic=target/debug/libgilogic.rlib \
  --extern creusillian=target/debug/libcreusillian.dylib \
  -Zcrate-attr='feature(register_tool)' \
  -Zcrate-attr='register_tool(gillian)' \
  -Zcrate-attr='feature(rustc_attrs)' \
  -Zcrate-attr='allow(internal_features)' \
  -Zcrate-attr='feature(stmt_expr_attributes)' \
  --cfg=gillian \
  -Zunpretty=expanded \
