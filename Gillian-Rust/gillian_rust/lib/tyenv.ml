type t = (string, Ty.Adt_def.t) Hashtbl.t

let empty () = Hashtbl.create 10
let copy x = Hashtbl.copy x
let declared genv = genv

let declare_struct genv name decl =
  Hashtbl.replace genv name (Ty.Adt_def.of_lit decl)

let adt_def ~genv name = Hashtbl.find genv name

let is_struct ~genv ty =
  match ty with
  | Ty.Adt name -> (
      match adt_def ~genv name with
      | Ty.Adt_def.Struct _ -> true
      | _ -> false)
  | _ -> false

let declare = Hashtbl.replace
let pp = Fmt.Dump.hashtbl Fmt.string Ty.Adt_def.pp
