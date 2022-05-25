open Gillian_rust

let check_ops =
  Alcotest.(check (list (testable Projections.pp_op Projections.equal_op)))

let check_partial_layout =
  Alcotest.(
    check
      (testable Partial_layout.pp_partial_layout
         Partial_layout.equal_partial_layout))

let check_accesses =
  Alcotest.(
    check (list (testable Partial_layout.pp_access Partial_layout.equal_access)))
(* Can't find binding equal_partial_layout? *)

module Type_names = struct
  let tA = Rust_types.Named "A"
  let tB = Rust_types.Named "B"
  let tC = Rust_types.Named "C"
  let tD = Rust_types.Named "D"
  let tE = Rust_types.Named "E"
  let tF = Rust_types.Named "F"
  let tG = Rust_types.Named "G"
  let tGFail = Rust_types.Named "GFail"
  let tH = Rust_types.Named "H"
  let u8 = Rust_types.of_lit @@ Gil_syntax.Literal.String "u8"
  let u16 = Rust_types.of_lit @@ Gil_syntax.Literal.String "u16"
  let u32 = Rust_types.of_lit @@ Gil_syntax.Literal.String "u32"
  let u64 = Rust_types.of_lit @@ Gil_syntax.Literal.String "u64"
  let tR8 = Rust_types.Named "R8"
  let tR64 = Rust_types.Named "R64"
  let tC8 = Rust_types.Named "C8"
  let tC16 = Rust_types.Named "C16"
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

  let context : Partial_layout.context = Partial_layout.context_from_env genv
end

module Mixed_repr_context = struct
  open Type_names

  let genv =
    let genv = C_global_env.empty () in
    C_global_env.declare genv "R8" (Rust_types.Struct (ReprRust, [ ("x", u8) ]));
    C_global_env.declare genv "R64"
      (Rust_types.Struct (ReprRust, [ ("x", u64) ]));

    C_global_env.declare genv "C8" (Rust_types.Struct (ReprC, [ ("x", u8) ]));
    C_global_env.declare genv "C16" (Rust_types.Struct (ReprC, [ ("x", u16) ]));

    C_global_env.declare genv "A"
      (Rust_types.Struct (ReprC, [ ("x", tR8); ("y", tR64) ]));

    C_global_env.declare genv "B"
      (Rust_types.Struct (ReprC, [ ("x", tA); ("y", tR64) ]));

    C_global_env.declare genv "C"
      (Rust_types.Struct
         ( ReprC,
           [
             ("x", Rust_types.Array { ty = tR8; length = 2 });
             ("y", Rust_types.Array { ty = tR8; length = 2 });
           ] ));

    C_global_env.declare genv "D"
      (Rust_types.Struct (ReprC, [ ("x", tC); ("y", tR8) ]));

    C_global_env.declare genv "E"
      (Rust_types.Struct (ReprC, [ ("x", u8); ("y", tR64) ]));

    C_global_env.declare genv "F"
      (Rust_types.Struct (ReprC, [ ("x", tE); ("y", tR64) ]));

    C_global_env.declare genv "G"
      (Rust_types.Struct (ReprC, [ ("x", tR64); ("y", u16); ("z", u8) ]));
    C_global_env.declare genv "GFail"
      (Rust_types.Struct (ReprC, [ ("x", tR64); ("y", u8); ("z", u16) ]));

    C_global_env.declare genv "H"
      (Rust_types.Struct (ReprC, [ ("x", tR64); ("y", tC16); ("z", tC8) ]));
    genv

  let context : Partial_layout.context = Partial_layout.context_from_env genv
end

module No_context_tests = struct
  let context =
    let genv = C_global_env.empty () in
    Partial_layout.context_from_env genv

  let snd_of_tuple () =
    let tpl = Rust_types.(Tuple [ Scalar (Int I32); Scalar Bool ]) in
    check_accesses "(i32, bool).1 resolves to bool at index 1"
      [ { index = 1; index_type = Scalar Bool; against = tpl } ]
    @@ Partial_layout.resolve_address context
         {
           block_type = tpl;
           route = Projections.[ Field (1, tpl) ];
           address_type = Scalar Bool;
         }

  let complex_tuple () =
    let open Rust_types in
    let i32 = Scalar (Int I32) in

    let tpl_1_2 = Tuple [ i32; i32 ] in
    let tpl_1 = Tuple [ i32; i32; tpl_1_2 ] in
    let tpl = Tuple [ Tuple [ i32; i32 ]; tpl_1 ] in
    check_accesses "((i32, i32), (i32, i32, (i32, i32))).1.2.0 resolves to i32"
      [
        { index = 0; against = tpl_1_2; index_type = i32 };
        { index = 2; against = tpl_1; index_type = tpl_1_2 };
        { index = 1; against = tpl; index_type = tpl_1 };
      ]
    @@ Partial_layout.resolve_address context
         {
           block_type = tpl;
           route =
             Projections.
               [ Field (1, tpl); Field (2, tpl_1); Field (0, tpl_1_2) ];
           address_type = i32;
         }

  let tests =
    [
      ("tuple second field via proj .1", `Quick, snd_of_tuple);
      ("Some complex tuple via proj .1.2.0", `Quick, complex_tuple);
    ]
end

module Partial_layouts_repr_C_tests = struct
  open Repr_C_context
  open Type_names

  let struct_of_u8_u16_u32 () =
    check_partial_layout "struct A { u8, u16, u32 } correct layout"
      {
        fields =
          Partial_layout.Arbitrary
            [|
              Partial_layout.Bytes 0;
              Partial_layout.Bytes 2;
              Partial_layout.Bytes 4;
              Partial_layout.Bytes 8;
            |];
        variant = Partial_layout.Single 0;
        align = Partial_layout.Partial_align.ExactlyPow2 2;
        size = Partial_layout.Partial_size.Exactly 8;
      }
    @@ context.partial_layouts tA

  let struct_of_A_C () =
    check_partial_layout "struct B { A, C } correct layout"
      {
        fields =
          Partial_layout.Arbitrary
            [|
              Partial_layout.Bytes 0;
              Partial_layout.Bytes 8;
              Partial_layout.Bytes 56;
            |];
        variant = Partial_layout.Single 0;
        align = Partial_layout.Partial_align.ExactlyPow2 2;
        size = Partial_layout.Partial_size.Exactly 56;
      }
    @@ context.partial_layouts tB

  let struct_of_5_u8_5_A () =
    check_partial_layout "struct C { [u8; 5], [A; 5] } correct layout"
      {
        fields =
          Partial_layout.Arbitrary
            [|
              Partial_layout.Bytes 0;
              Partial_layout.Bytes 8;
              Partial_layout.Bytes 48;
            |];
        variant = Partial_layout.Single 0;
        align = Partial_layout.Partial_align.ExactlyPow2 2;
        size = Partial_layout.Partial_size.Exactly 48;
      }
    @@ context.partial_layouts tC

  let struct_of_u16_u8 () =
    check_partial_layout "struct D { u16, u8 } correct layout with end padding"
      {
        fields =
          Partial_layout.Arbitrary
            [|
              Partial_layout.Bytes 0;
              Partial_layout.Bytes 2;
              Partial_layout.Bytes 4;
            |];
        variant = Partial_layout.Single 0;
        align = Partial_layout.Partial_align.ExactlyPow2 1;
        size = Partial_layout.Partial_size.Exactly 4;
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

module Partial_layouts_mixed_repr_tests = struct
  open Mixed_repr_context
  open Type_names

  let rust_struct_of_u8 () =
    check_partial_layout "struct R8 { u8 } correct layout"
      {
        fields =
          Partial_layout.Arbitrary
            [|
              Partial_layout.FromIndex (0, 0); Partial_layout.FromIndex (1, 0);
            |];
        variant = Partial_layout.Single 0;
        align = Partial_layout.Partial_align.ToType tR8;
        size = Partial_layout.Partial_size.AtLeast 0;
      }
    @@ context.partial_layouts tR8

  let rust_struct_of_u64 () =
    check_partial_layout "struct R64 { u64 } correct layout"
      {
        fields =
          Partial_layout.Arbitrary
            [|
              Partial_layout.FromIndex (0, 0); Partial_layout.FromIndex (1, 0);
            |];
        variant = Partial_layout.Single 0;
        align = Partial_layout.Partial_align.ToType tR64;
        size = Partial_layout.Partial_size.AtLeast 0;
      }
    @@ context.partial_layouts tR64

  let struct_of_R8_R64 () =
    check_partial_layout "struct A { R8, R64 } correct layout"
      {
        fields =
          Partial_layout.Arbitrary
            [|
              Partial_layout.Bytes 0;
              Partial_layout.FromIndex (1, 0);
              Partial_layout.FromIndex (2, 0);
            |];
        variant = Partial_layout.Single 0;
        align = Partial_layout.Partial_align.AtLeastPow2 0;
        size = Partial_layout.Partial_size.AtLeast 0;
      }
    @@ context.partial_layouts tA

  let struct_of_A_R64 () =
    check_partial_layout "struct B { A, R64 } correct layout"
      {
        fields =
          Partial_layout.Arbitrary
            [|
              Partial_layout.Bytes 0;
              Partial_layout.FromIndex (1, 0);
              Partial_layout.FromIndex (2, 0);
            |];
        variant = Partial_layout.Single 0;
        align = Partial_layout.Partial_align.AtLeastPow2 0;
        size = Partial_layout.Partial_size.AtLeast 0;
      }
    @@ context.partial_layouts tB

  let struct_of_2_R8_2_R8 () =
    check_partial_layout "struct C { [R8; 2], [R8; 2] } correct layout"
      {
        fields =
          Partial_layout.Arbitrary
            [|
              Partial_layout.Bytes 0;
              Partial_layout.FromCount (tR8, 2, 0);
              Partial_layout.FromCount (tR8, 4, 0);
            |];
        variant = Partial_layout.Single 0;
        align = Partial_layout.Partial_align.ToType tR8;
        size = Partial_layout.Partial_size.AtLeast 0;
      }
    @@ context.partial_layouts tC

  let struct_of_C_R8 () =
    check_partial_layout "struct D { C, R8 } correct layout"
      {
        fields =
          Partial_layout.Arbitrary
            [|
              Partial_layout.Bytes 0;
              Partial_layout.FromCount (tR8, 4, 0);
              Partial_layout.FromCount (tR8, 5, 0);
            |];
        variant = Partial_layout.Single 0;
        align = Partial_layout.Partial_align.ToType tR8;
        size = Partial_layout.Partial_size.AtLeast 0;
      }
    @@ context.partial_layouts tD

  let struct_of_u8_R64 () =
    check_partial_layout "struct E { u8, R64 } correct layout"
      {
        fields =
          Partial_layout.Arbitrary
            [|
              Partial_layout.Bytes 0;
              Partial_layout.FromCount (tR64, 1, 0);
              Partial_layout.FromCount (tR64, 2, 0);
            |];
        variant = Partial_layout.Single 0;
        align = Partial_layout.Partial_align.ToType tR64;
        size = Partial_layout.Partial_size.AtLeast 1;
      }
    @@ context.partial_layouts tE

  let struct_of_E_R64 () =
    check_partial_layout "struct F { E, R64 } correct layout"
      {
        fields =
          Partial_layout.Arbitrary
            [|
              Partial_layout.Bytes 0;
              Partial_layout.FromCount (tR64, 2, 0);
              Partial_layout.FromCount (tR64, 3, 0);
            |];
        variant = Partial_layout.Single 0;
        align = Partial_layout.Partial_align.ToType tR64;
        size = Partial_layout.Partial_size.AtLeast 1;
      }
    @@ context.partial_layouts tF

  let struct_of_R64_u16_u8 () =
    check_partial_layout "struct G { R64, u16, u8 } correct layout"
      {
        fields =
          Partial_layout.Arbitrary
            [|
              Partial_layout.Bytes 0;
              Partial_layout.FromIndex (1, 0);
              Partial_layout.FromIndex (1, 2);
              Partial_layout.FromIndex (3, 0);
            |];
        variant = Partial_layout.Single 0;
        align = Partial_layout.Partial_align.AtLeastPow2 1;
        size = Partial_layout.Partial_size.AtLeast 4;
      }
    @@ context.partial_layouts tG

  let tests =
    [
      ("struct R8 { u8 }", `Quick, rust_struct_of_u8);
      ("struct R64 { u64 }", `Quick, rust_struct_of_u64);
      ("struct A { R8, R64 }", `Quick, struct_of_R8_R64);
      ("struct B { A, R64 }", `Quick, struct_of_A_R64);
      ("struct C { [R8; 2], [R8; 2] }", `Quick, struct_of_2_R8_2_R8);
      ("struct D { C, R8 }", `Quick, struct_of_C_R8);
      ("struct E { u8, R64 }", `Quick, struct_of_u8_R64);
      ("struct F { E, R64 }", `Quick, struct_of_E_R64);
      ("struct G { R64, u16, u8 }", `Quick, struct_of_R64_u16_u8);
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
    @@ Partial_layout.reduce context [ Projections.Field (1, tA) ]

  let pointer_arithmetic_from_initial_field_matches_field_traversal () =
    check_ops "(struct A { u8, u16, u32 }.0 + 2) as u16 is A.1"
      (Partial_layout.reduce context [ Projections.Field (1, tA) ])
    @@ Partial_layout.reduce context
         [
           Projections.Field (0, tA);
           Projections.Plus (Overflow, 2, u8);
           Projections.Cast (u8, u16);
         ]

  let complicated_traversal () =
    check_ops
      "struct B { struct A { u8, u16, u32 }, struct C { [u8; 5], [A; 5] } \
       }.1.1[3].0 is C as u8 +^untyped 40 = 8 + 5 * 1 + (3 padd) + 3 * 8 + 0"
      [
        Projections.Cast (tB, u8); Projections.UPlus (Projections.Overflow, 40);
      ]
    @@ Partial_layout.reduce context
         [
           Projections.Field (1, tB);
           Projections.Field (1, tC);
           Projections.Index (3, tA, 5);
           Projections.Field (0, tA);
         ]

  let tests =
    [
      ( "get second field following padding",
        `Quick,
        get_second_field_following_padding );
      ( "pointer arithmetic from initial field matches field traversal",
        `Quick,
        pointer_arithmetic_from_initial_field_matches_field_traversal );
      ("complicated traversal", `Quick, complicated_traversal);
    ]
end

module Resolution_repr_C = struct
  open Repr_C_context
  open Type_names

  let second_field_via_add () =
    check_accesses
      "struct A { u8, u16, u32 }.0 +^U 2 resolves to the u16 at index 1"
      [ { index = 1; index_type = u16; against = tA } ]
    @@ Partial_layout.resolve_address context
         {
           block_type = tA;
           route =
             [ Projections.Field (0, tA); Projections.Plus (Overflow, 2, u8) ];
           address_type = u16;
         }

  let second_field_directly () =
    check_accesses "struct A { u8, u16, u32 }.1 resolves to the u16 at index 1"
      [ { index = 1; index_type = u16; against = tA } ]
    @@ Partial_layout.resolve_address context
         {
           block_type = tA;
           route = [ Projections.Field (1, tA) ];
           address_type = u16;
         }

  let complicated_resolution () =
    check_accesses
      "struct B { struct A { u8, u16, u32 }, struct C { [u8; 5], [A; 5] } \
       }.0.0[3].0 should resolve to a particular u8"
      [
        { index = 0; index_type = u8; against = tA };
        {
          index = 3;
          index_type = tA;
          against = Rust_types.Array { ty = tA; length = 5 };
        };
        {
          index = 1;
          index_type = Rust_types.Array { ty = tA; length = 5 };
          against = tC;
        };
        { index = 1; index_type = tC; against = tB };
      ]
    @@ Partial_layout.resolve_address context
         {
           block_type = tB;
           route =
             [
               Projections.Field (1, tB);
               Projections.Field (1, tC);
               Projections.Index (3, tA, 5);
               Projections.Field (0, tA);
             ];
           address_type = u8;
         }

  let tests =
    [
      ("second field via add", `Quick, second_field_via_add);
      ("second field directly", `Quick, second_field_directly);
      ("complicated resolution", `Quick, complicated_resolution);
    ]
end

module Resolution_mixed_repr = struct
  open Mixed_repr_context
  open Type_names

  let next_element_field () =
    check_accesses
      "[struct A { R8, R64 };2][0].0 +^A 1 resolves to the second R8"
      [
        { index = 0; index_type = tR8; against = tA };
        {
          index = 1;
          index_type = tA;
          against = Rust_types.Array { ty = tA; length = 2 };
        };
      ]
    @@ Partial_layout.resolve_address_debug_access_error context
         {
           block_type = Rust_types.Array { ty = tA; length = 2 };
           route =
             [
               Projections.Index (0, tA, 2);
               Projections.Field (0, tA);
               Projections.Cast (tR8, tA);
               Projections.Plus (Overflow, 1, tA);
               Projections.Cast (tA, tR8);
             ];
           address_type = tR8;
         }

  let cannot_add_to_next_element_given_unknown_padding () =
    Alcotest.check_raises
      "struct B { struct A { R8, R64 }, R64 }.0.1 +^R64 1 mustn't resolve to \
       the second R64"
      (Partial_layout.AccessError
         ( [ { index = 1; index_type = tR64; against = tA } ],
           [ Projections.Plus (Projections.Overflow, 1, tR64) ],
           tR64,
           None,
           "Stuck handling next op" ))
    (* Use correct error from test, we just care that it fails *)
    @@ fun () ->
    let _ =
      Partial_layout.resolve_address context
        {
          block_type = tA;
          route =
            [
              Projections.Field (1, tA);
              Projections.Plus (Projections.Overflow, 1, tR64);
            ];
          address_type = tR64;
        }
    in
    ()

  let resolve_mixed_next_field_array () =
    check_accesses
      "struct C { [R8; 2], [R8; 2] }.0[0] +^R8 2 resolves to the third R8"
      [
        {
          index = 0;
          index_type = tR8;
          against = Rust_types.Array { ty = tR8; length = 2 };
        };
        {
          index = 1;
          index_type = Rust_types.Array { ty = tR8; length = 2 };
          against = tC;
        };
      ]
    @@ Partial_layout.resolve_address_debug_access_error context
         {
           block_type = tC;
           route =
             [
               Projections.Field (0, tC);
               Projections.Index (0, tR8, 2);
               Projections.Plus (Overflow, 2, tR8);
             ];
           address_type = tR8;
         }

  let resolve_mixed_next_end_of_array_and_up () =
    check_accesses
      "struct D { struct C { [R8; 2], [R8; 2] }, R8}.0[0] +^R8 4 resolves to \
       the fifth R8"
      [ { index = 1; index_type = tR8; against = tD } ]
    @@ Partial_layout.resolve_address_debug_access_error context
         {
           block_type = tD;
           route =
             [
               Projections.Field (0, tD);
               Projections.Field (0, tC);
               Projections.Index (0, tR8, 2);
               Projections.Plus (Overflow, 4, tR8);
             ];
           address_type = tR8;
         }

  let resolve_mixed_end_of_struct_following_byte_and_up () =
    check_accesses
      "struct F { struct E { u8, R64 }, R64}).0.1 + 1 resolves to the second \
       R64"
      [ { index = 1; index_type = tR64; against = tF } ]
    @@ Partial_layout.resolve_address_debug_access_error context
         {
           block_type = tF;
           route =
             [
               Projections.Field (0, tF);
               Projections.Field (1, tE);
               Projections.Plus (Overflow, 1, tR64);
             ];
           address_type = tR64;
         }

  let resolve_mixed_move_forward_from_bigger_to_smaller () =
    check_accesses "struct G { R64, u16, u8 }).1 + 1 resolves to the u8"
      [ { index = 2; index_type = u8; against = tG } ]
    @@ Partial_layout.resolve_address_debug_access_error context
         {
           block_type = tG;
           route =
             [
               Projections.Field (1, tG);
               Projections.Plus (Overflow, 1, u16);
               Projections.Cast (u16, u8);
             ];
           address_type = u8;
         }

  let resolve_mixed_move_backward_from_smaller_to_bigger () =
    check_accesses "struct G { R64, u16, u8 }.2 - 2 resolves to the u16"
      [ { index = 1; index_type = u16; against = tG } ]
    @@ Partial_layout.resolve_address_debug_access_error context
         {
           block_type = tG;
           route =
             [
               Projections.Field (2, tG);
               Projections.Plus (Overflow, -2, u8);
               Projections.Cast (u8, u16);
             ];
           address_type = u16;
         }

  let resolve_mixed_move_forward_fails_from_smaller_to_bigger () =
    Alcotest.check_raises
      "struct GFail { R64, u8, u16 }).1 + 1 mustn't resolve to the u16"
      (Partial_layout.AccessError
         ( [ { index = 1; index_type = u8; against = tGFail } ],
           [ Projections.UPlus (Projections.Overflow, 1) ],
           u8,
           None,
           "Stuck handling next op" ))
    (* Use correct error from test, we just care that it fails *)
    @@ fun () ->
    let _ =
      Partial_layout.resolve_address context
        {
          block_type = tGFail;
          route =
            [
              Projections.Field (1, tGFail);
              Projections.Plus (Projections.Overflow, 1, u8);
              Projections.Cast (u8, u16);
            ];
          address_type = u16;
        }
    in
    ()

  let resolve_mixed_move_backward_fails_from_bigger_to_smaller () =
    Alcotest.check_raises
      "struct GFail { R64, u8, u16 }).2 > u8 - 1 mustn't resolve to the u8"
      (Invalid_argument "index out of bounds")
    (* The above seems like the wrong error, and should be looked at if backwards arithmetic doesn't work,
       but since it fails, let's not concern ourselves with how yet *)
    @@
    fun () ->
    let _ =
      Partial_layout.resolve_address_debug_access_error context
        {
          block_type = tGFail;
          route =
            [
              Projections.Field (2, tGFail);
              Projections.Cast (u16, u8);
              Projections.Plus (Projections.Overflow, -1, u8);
            ];
          address_type = u16;
        }
    in
    ()

  let resolve_mixed_move_forward_from_bigger_to_smaller_struct () =
    check_accesses "struct H { R64, C16, C8 }).1 + 1 resolves to the C8"
      [ { index = 2; index_type = tC8; against = tH } ]
    @@ Partial_layout.resolve_address_debug_access_error context
         {
           block_type = tH;
           route =
             [
               Projections.Field (1, tH);
               Projections.Plus (Overflow, 1, tC16);
               Projections.Cast (tC16, tC8);
             ];
           address_type = tC8;
         }

  let resolve_mixed_move_backward_from_smaller_to_bigger_struct () =
    check_accesses "struct H { R64, C16, C8 }.2 - 2 resolves to the C16"
      [ { index = 1; index_type = tC16; against = tH } ]
    @@ Partial_layout.resolve_address_debug_access_error context
         {
           block_type = tH;
           route =
             [
               Projections.Field (2, tH);
               Projections.Plus (Overflow, -2, tC8);
               Projections.Cast (tC8, tC16);
             ];
           address_type = tC16;
         }

  let tests =
    [
      ("next element field", `Quick, next_element_field);
      ( "cannot add to next element given unknown padding",
        `Quick,
        cannot_add_to_next_element_given_unknown_padding );
      ("resolve mixed next field array", `Quick, resolve_mixed_next_field_array);
      ( "resolve mixed next end of array and up",
        `Quick,
        resolve_mixed_next_end_of_array_and_up );
      ( "resolve mixed end of struct following byte and up",
        `Quick,
        resolve_mixed_end_of_struct_following_byte_and_up );
      ( "resolve mixed move forwards from bigger to smaller",
        `Quick,
        resolve_mixed_move_forward_from_bigger_to_smaller );
      ( "resolve mixed move backward from smaller to bigger",
        `Quick,
        resolve_mixed_move_backward_from_smaller_to_bigger );
      ( "resolve mixed move forward fails from smaller to bigger",
        `Quick,
        resolve_mixed_move_forward_fails_from_smaller_to_bigger );
      ( "resolve mixed move backward fails from bigger to smaller",
        `Quick,
        resolve_mixed_move_backward_fails_from_bigger_to_smaller );
      ( "resolve mixed move forwards from bigger to smaller struct",
        `Quick,
        resolve_mixed_move_forward_from_bigger_to_smaller_struct );
      ( "resolve mixed move backward from smaller to bigger struct",
        `Quick,
        resolve_mixed_move_backward_from_smaller_to_bigger_struct );
    ]
end

let test_suites : unit Alcotest.test list =
  [
    ("Partial layout repr C", Partial_layouts_repr_C_tests.tests);
    ("Partial layout mixed repr", Partial_layouts_mixed_repr_tests.tests);
    ("Reduce", Reduce_tests.tests);
    ("Resolution no-context", No_context_tests.tests);
    ("Resolution repr C", Resolution_repr_C.tests);
    ("Resolution mixed repr", Resolution_mixed_repr.tests);
  ]

let () = Alcotest.run "Gillian Rust" test_suites
