type t = (string, Ty.Adt_def.t) Hashtbl.t

let of_yojson : Yojson.Safe.t -> (t, string) result = function
  | `Assoc xs ->
      let tbl = Hashtbl.create (List.length xs) in
      List.iter
        (fun (name, json) ->
          match Ty.Adt_def.of_yojson json with
          | Ok def -> Hashtbl.replace tbl name def
          | Error msg -> failwith msg)
        xs;
      Ok tbl
  | _ -> Error "expected an object"

let to_yojson : t -> Yojson.Safe.t =
 fun tbl ->
  `Assoc
    (Hashtbl.fold
       (fun name def acc -> (name, Ty.Adt_def.to_yojson def) :: acc)
       tbl [])

let adt_def ~genv name = Hashtbl.find genv name

let is_struct ~genv ty =
  match ty with
  | Ty.Adt name -> (
      match adt_def ~genv name with
      | Ty.Adt_def.Struct _ -> true
      | _ -> false)
  | _ -> false

let pp = Fmt.Dump.hashtbl Fmt.string Ty.Adt_def.pp

let of_declaration_list decls : t =
  let genv = Hashtbl.create 10 in
  List.iter (fun (name, decl) -> Hashtbl.replace genv name decl) decls;
  genv
