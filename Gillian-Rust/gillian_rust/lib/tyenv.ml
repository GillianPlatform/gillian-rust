type t = (string, Rust_types.adt_def) Hashtbl.t

let empty () = Hashtbl.create 10
let copy x = Hashtbl.copy x
let declared genv = genv

let declare_struct genv name decl =
  Hashtbl.replace genv name (Rust_types.adt_def_of_lit decl)

let adt_def ~genv name = Hashtbl.find genv name

let is_struct ~genv ty =
  match ty with
  | Rust_types.Adt name -> (
      match adt_def ~genv name with
      | Rust_types.Struct _ -> true
      | _ -> false)
  | _ -> false

let declare = Hashtbl.replace
let pp = Fmt.Dump.hashtbl Fmt.string Rust_types.pp_adt_def
