type t = (string, Ty.Adt_def.t) Hashtbl.t

let current_tyenv = ref (Hashtbl.create 0)
let set_current tyenv = current_tyenv := tyenv
let get_current () = !current_tyenv

let of_yojson : Yojson.Safe.t -> (t, string) result = function
  | `Assoc xs ->
      let tbl = Hashtbl.create (List.length xs) in
      List.iter
        (fun (name, json) ->
          match Ty.Adt_def.of_yojson json with
          | Ok def -> Hashtbl.replace tbl name def
          | Error msg ->
              Fmt.failwith "Couldn't parse %a: %s" Yojson.Safe.pp json msg)
        xs;
      Ok tbl
  | _ -> Error "expected an object"

let to_yojson : t -> Yojson.Safe.t =
 fun tbl ->
  `Assoc
    (Hashtbl.fold
       (fun name def acc -> (name, Ty.Adt_def.to_yojson def) :: acc)
       tbl [])

let adt_def name = Hashtbl.find !current_tyenv name

let is_struct ty =
  let res =
    match ty with
    | Ty.Adt (name, _) -> (
        match adt_def name with
        | Ty.Adt_def.Struct _ -> true
        | _ -> false)
    | _ -> false
  in
  Logging.verbose (fun m -> m "Is struct? %a : %b" Ty.pp ty res);
  res

let pp = Fmt.Dump.hashtbl Fmt.string Ty.Adt_def.pp

let of_declaration_list decls : t =
  let tyenv = Hashtbl.create 10 in
  List.iter (fun (name, decl) -> Hashtbl.replace tyenv name decl) decls;
  tyenv

let leak t = t
