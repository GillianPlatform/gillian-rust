#!/usr/bin/env bash

rustc ./examples/verification/list_std.rs \
  -Ldependency=./target/debug/deps/ \
  --extern gilogic=target/debug/libgilogic.rlib \
  --extern creusillian=target/debug/libcreusillian.rlib \
  -Zcrate-attr='feature(register_tool)' \
  -Zcrate-attr='register_tool(gillian)' \
  -Zcrate-attr='feature(rustc_attrs)' \
  -Zcrate-attr='allow(internal_features)' \
  -Zcrate-attr='feature(stmt_expr_attributes)' \
  -Zunpretty=expanded \
