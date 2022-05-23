open Gillian_rust

let check_ops =
  Alcotest.(check (list (testable Projections.pp_op Projections.equal_op)))

let check_partial_layout =
  Alcotest.(check (testable Matthew.pp_partial_layout ( = )))
(* Can't find binding equal_partial_layout? *)

module Type_names = struct
  let tA = Rust_types.Named "A"
  let tB = Rust_types.Named "B"
  let tC = Rust_types.Named "C"
  let tD = Rust_types.Named "D"
  let tE = Rust_types.Named "E"
  let tF = Rust_types.Named "F"
  let tG = Rust_types.Named "G"
  let tH = Rust_types.Named "H"
  let u8 = Rust_types.of_lit @@ Gil_syntax.Literal.String "u8"
  let u16 = Rust_types.of_lit @@ Gil_syntax.Literal.String "u16"
  let u32 = Rust_types.of_lit @@ Gil_syntax.Literal.String "u32"
  let u64 = Rust_types.of_lit @@ Gil_syntax.Literal.String "u64"
end

module Repr_C_context = struct
  open Type_names

  let genv =
    let genv = C_global_env.empty () in
    C_global_env.declare genv "A"
      (Rust_types.Struct (ReprC, [ ("x", u8); ("y", u16); ("z", u32) ]));

    C_global_env.declare genv "B"
      (Rust_types.Struct (ReprC, [ ("x", tA); ("y", tC) ]));

    C_global_env.declare genv "C"
      (Rust_types.Struct
         ( ReprC,
           [
             ("x", Rust_types.Array { ty = u8; length = 5 });
             ("y", Rust_types.Array { ty = tA; length = 5 });
           ] ));

    C_global_env.declare genv "D"
      (Rust_types.Struct (ReprC, [ ("x", u16); ("y", u8) ]));
    genv

  let context : Matthew.context = Matthew.context_from_env genv
end

module Partial_layouts_tests = struct
  open Repr_C_context
  open Type_names

  let struct_of_u8_u16_u32 () =
    check_partial_layout "struct A { u8, u16, u32 } correct layout"
      {
        fields =
          Matthew.Arbitrary
            [|
              Matthew.Bytes 0; Matthew.Bytes 2; Matthew.Bytes 4; Matthew.Bytes 8;
            |];
        variant = Matthew.Single 0;
        align = Matthew.Partial_align.ExactlyPow2 2;
        size = Matthew.Partial_size.Exactly 8;
      }
    @@ context.partial_layouts tA

  let struct_of_A_C () =
    check_partial_layout "struct B { A, C } correct layout"
      {
        fields =
          Matthew.Arbitrary
            [| Matthew.Bytes 0; Matthew.Bytes 8; Matthew.Bytes 56 |];
        variant = Matthew.Single 0;
        align = Matthew.Partial_align.ExactlyPow2 2;
        size = Matthew.Partial_size.Exactly 56;
      }
    @@ context.partial_layouts tB

  let struct_of_5_u8_5_A () =
    check_partial_layout "struct C { [u8; 5], [A; 5] } correct layout"
      {
        fields =
          Matthew.Arbitrary
            [| Matthew.Bytes 0; Matthew.Bytes 8; Matthew.Bytes 48 |];
        variant = Matthew.Single 0;
        align = Matthew.Partial_align.ExactlyPow2 2;
        size = Matthew.Partial_size.Exactly 48;
      }
    @@ context.partial_layouts tC

  let struct_of_u16_u8 () =
    check_partial_layout "struct D { u16, u8 } correct layout with end padding"
      {
        fields =
          Matthew.Arbitrary
            [| Matthew.Bytes 0; Matthew.Bytes 2; Matthew.Bytes 4 |];
        variant = Matthew.Single 0;
        align = Matthew.Partial_align.ExactlyPow2 1;
        size = Matthew.Partial_size.Exactly 4;
      }
    @@ context.partial_layouts tD

  let tests =
    [
      ("struct A { u8, u16, u32 }", `Quick, struct_of_u8_u16_u32);
      ("struct B { tA, tC }", `Quick, struct_of_A_C);
      ("struct C { [u8; 5], [A; 5] }", `Quick, struct_of_5_u8_5_A);
      ("struct D { u16, u8 }", `Quick, struct_of_u16_u8);
    ]
end

module Reduce_tests = struct
  open Repr_C_context
  open Type_names

  let get_second_field_following_padding () =
    check_ops "struct A { u8, u16, u32 }.1 has the u16 padded to align"
      [
        Projections.Cast (tA, u16); Projections.UPlus (Projections.Overflow, 2);
      ]
    @@ Matthew.reorder @@ Matthew.contextualise context [ Projections.Field (1, tA) ]

  let tests =
    [
      ( "get second field following padding",
        `Quick,
        get_second_field_following_padding );
    ]
end

let test_suites : unit Alcotest.test list =
  [
    ("Partial layout tests", Partial_layouts_tests.tests);
    ("ReduceTests", Reduce_tests.tests);
  ]

let () = Alcotest.run "Gillian Rust" test_suites
