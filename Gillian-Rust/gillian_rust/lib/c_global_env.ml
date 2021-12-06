type t = (string, Rust_types.t) Hashtbl.t

let empty () = Hashtbl.create 10

let copy x = Hashtbl.copy x

let get_type genv ty = Hashtbl.find genv ty

let declare_struct genv name decl =
  Hashtbl.replace genv name (Rust_types.of_lit decl)

let rec type_equal ~genv ty ty' =
  match (ty, ty') with
  | Rust_types.Named x, Rust_types.Named y -> x = y
  | Named x, t | t, Named x -> type_equal ~genv (get_type genv x) t
  | ty, ty' -> ty = ty'

let rec resolve_named ~genv ty =
  match ty with
  | Rust_types.Named a -> get_type genv a |> resolve_named ~genv
  | _                  -> ty

let pp = Fmt.Dump.hashtbl Fmt.string Rust_types.pp
