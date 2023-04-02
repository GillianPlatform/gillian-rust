(* Some very quick meta-programming for GIL. *)

let gen_identity_for_ty ty =
  Printf.printf {|pred "<%s as gilogic::Ownable>::own"(+self):
  emp;|} ty;
  print_newline ();
  print_newline ()

let () =
  Array.iter gen_identity_for_ty
    [|
      "u8";
      "u16";
      "u32";
      "u64";
      "u128";
      "usize";
      "i8";
      "i16";
      "i32";
      "i64";
      "i128";
      "isize";
    |]

let () =
  let file = open_in "./i__ownable.gil.incomplete" in
  try
    while true do
      input_line file |> print_endline
    done
  with End_of_file -> ()
