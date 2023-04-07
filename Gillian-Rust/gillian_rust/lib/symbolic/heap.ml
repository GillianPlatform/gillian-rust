open Gillian.Gil_syntax
open List_utils.Infix
open Gillian.Monadic
open Err
module DR = Delayed_result
open DR.Syntax
open Delayed.Syntax
module Tyenv = Common.Tyenv
module Actions = Common.Actions
open Delayed_utils

exception NotConcrete of string

module TypePreds = struct
  let ( .%[] ) e idx = Expr.list_nth e idx

  let ( >- ) e ty =
    let open Formula.Infix in
    (Expr.typeof e) #== (Expr.type_ ty)

  let valid_thin_ptr e =
    let open Formula.Infix in
    (Expr.list_length e) #== (Expr.int 2)
    #&& (e.%[0] >- ObjectType)
    #&& (e.%[1] >- ListType)

  let valid_fat_ptr e =
    let open Formula.Infix in
    (Expr.list_length e) #== (Expr.int 2)
    #&& (valid_thin_ptr e.%[0])
    #&& (e.%[1] >- IntType)

  let valid_thin_ref e =
    let open Formula.Infix in
    (Expr.list_length e) #== (Expr.int 2) #&& (valid_thin_ptr e.%[0])

  let valid_fat_ref e =
    let open Formula.Infix in
    (Expr.list_length e) #== (Expr.int 2) #&& (valid_fat_ptr e.%[0])

  let valid scalar_ty e =
    match scalar_ty with
    | Ty.Scalar (Uint _ | Int _) -> e >- IntType
    | Scalar Bool -> e >- BooleanType
    | Ref { ty = Slice _; _ } -> valid_fat_ref e
    | Ref _ -> valid_thin_ref e
    | Ptr { ty = Slice _; _ } -> valid_fat_ptr e
    | Ptr _ -> valid_thin_ptr e
    | Scalar Char -> True
    | _ -> failwith "Not a leaf type, can't express validity"
end

let too_symbolic e =
  Delayed.map (Delayed.reduce e) (fun e -> Error (Too_symbolic e))

let not_concrete msgf = Fmt.kstr (fun s -> raise (NotConcrete s)) msgf

let rec lift_lit = function
  | Literal.LList l -> Expr.EList (List.map lift_lit l)
  | x -> Lit x

let rec concretize_expr expr =
  match expr with
  | Expr.Lit lit -> lit
  | EList l -> LList (List.map concretize_expr l)
  | BinOp (((EList _ | Lit (LList _)) as l), LstNth, Lit (Int i)) ->
      let i = Z.to_int i in
      concretize_expr (Expr.list_nth l i)
  | _ -> not_concrete "concretize: %a" Expr.pp expr

let concretize_proj expr =
  let lit_list =
    match concretize_expr expr with
    | LList l -> l
    | _ -> not_concrete "concretize_proj, not a list: %a" Expr.pp expr
  in
  Projections.of_lit_list lit_list

let concretiz_proj_opt e =
  try Some (concretize_proj e) with NotConcrete _ -> None

exception MemoryError of string

let mem_error p = Fmt.kstr (fun s -> raise (MemoryError s)) p

module TreeBlock = struct
  type t = { ty : Ty.t; content : tree_content }

  and tree_content =
    | Symbolic of Expr.t
    | Leaf of Expr.t
    | Fields of t list
    | Array of t list
    | Enum of { discr : int; fields : t list }
    | Uninit
    | Missing

  type outer = { offset : Expr.t option; root : t }

  let rec is_empty block =
    match block.content with
    | Missing -> true
    | Fields fields | Array fields -> List.for_all is_empty fields
    | _ -> false

  let outer_is_empty outer = is_empty outer.root

  let rec pp fmt { ty; content } =
    Fmt.pf fmt "%a :@ %a" pp_content content Ty.pp ty

  and pp_content ft =
    let open Fmt in
    function
    | Leaf e -> Expr.pp ft e
    | Fields v -> (parens (Fmt.list ~sep:Fmt.comma pp)) ft v
    | Enum { discr; fields } ->
        pf ft "%a[%a]" int discr (Fmt.list ~sep:comma pp) fields
    | Array v -> (brackets (Fmt.list ~sep:comma pp)) ft v
    | Symbolic s -> Expr.pp ft s
    | Uninit -> Fmt.string ft "UNINIT"
    | Missing -> Fmt.string ft "MISSING"

  let pp_outer ft t =
    let open Fmt in
    pf ft "@[<v 2>AFTER OFFSET: %a %a @]" (Fmt.Dump.option Expr.pp) t.offset pp
      t.root

  let rec to_rust_value ({ content; ty } as t) =
    match content with
    | Leaf s -> (
        match ty with
        | Scalar (Uint _ | Int _ | Char | Bool) | Ptr _ | Ref _ -> s
        | _ -> Fmt.failwith "Malformed tree: %a" pp t)
    | Fields v | Array v ->
        let tuple = List.map to_rust_value v in
        EList tuple
    | Enum { discr; fields } ->
        let fields = List.map to_rust_value fields in
        Expr.EList [ Expr.int discr; EList fields ]
    | Symbolic s -> s
    | Uninit -> mem_error "Attempting to read uninitialized value"
    | Missing -> mem_error "Attempting to read missing value"

  let outer_assertion ~loc block =
    let offset =
      match block.offset with
      | None -> Expr.EList []
      | Some o -> o
    in
    let cp = Actions.cp_to_name Value in
    let ty = Ty.to_expr block.root.ty in
    let value = to_rust_value block.root in
    Asrt.GA (cp, [ loc; offset; ty ], [ value ])

  let rec of_rust_struct_value
      ~tyenv
      ~ty
      ~subst
      ~fields_tys
      (fields : Expr.t list) =
    let++ content =
      DR_list.map2
        (fun (_, t) v -> of_rust_value ~tyenv ~ty:(Ty.subst_params ~subst t) v)
        fields_tys fields
    in
    let content = Fields content in
    { ty; content }

  and of_rust_enum_value ~tyenv ~ty ~subst ~variants_tys (data : Expr.t list) =
    match data with
    | [ Lit (Int variant_idx); EList fields ] ->
        let vidx = Z.to_int variant_idx in
        let _, tys = List.nth variants_tys vidx in
        let++ fields =
          DR_list.map2
            (fun t v -> of_rust_value ~tyenv ~ty:(Ty.subst_params ~subst t) v)
            tys fields
        in
        let content = Enum { discr = vidx; fields } in
        { ty; content }
    | _ ->
        Fmt.failwith "Invalid enum value for type %a: %a" Ty.pp ty
          (Fmt.list Expr.pp) data

  and of_rust_value ~tyenv ~ty (e : Expr.t) : (t, Err.t) DR.t =
    match (ty, e) with
    | (Ty.Scalar (Uint _ | Int _ | Bool) | Ptr _ | Ref _), e ->
        Logging.tmi (fun m -> m "valid: %a for %a" Expr.pp e Ty.pp ty);
        if%sat TypePreds.valid ty e then DR.ok { ty; content = Leaf e }
        else DR.error (Err.Invalid_value (ty, e))
    | Tuple _, Lit (LList data) ->
        let content = List.map lift_lit data in
        of_rust_value ~tyenv ~ty (EList content)
    | Tuple ts, EList tup ->
        let++ content =
          DR_list.map2 (fun t v -> of_rust_value ~tyenv ~ty:t v) ts tup
        in
        let content = Fields content in
        { ty; content }
    | Adt _, Lit (LList content) ->
        let content = List.map lift_lit content in
        of_rust_value ~tyenv ~ty (EList content)
    | Adt (name, subst), EList data -> (
        match Tyenv.adt_def ~tyenv name with
        | Struct (_repr, fields_tys) ->
            of_rust_struct_value ~tyenv ~ty ~subst ~fields_tys data
        | Enum variants_tys ->
            of_rust_enum_value ~tyenv ~ty ~subst ~variants_tys data)
    | Array { length; ty = ty' }, EList l
      when List.compare_length_with l length == 0 ->
        let++ mem_array = DR_list.map (of_rust_value ~tyenv ~ty:ty') l in
        { ty; content = Array mem_array }
    | _, s -> DR.ok { ty; content = Symbolic s }

  let outer_missing ~offset ~tyenv ty =
    let root = { ty; content = Missing } in
    { offset; root }

  let outer_symbolic ~offset ~tyenv ty e =
    let root = { ty; content = Symbolic e } in
    { offset; root }

  let rec uninitialized ~tyenv ty =
    match ty with
    | Ty.Tuple v ->
        let tuple = List.map (uninitialized ~tyenv) v in
        { ty; content = Fields tuple }
    | Adt (name, subst) -> (
        match Tyenv.adt_def ~tyenv name with
        | Struct (_repr, fields) ->
            let tuple =
              List.map
                (fun (_, t) -> uninitialized ~tyenv (Ty.subst_params ~subst t))
                fields
            in

            { ty; content = Fields tuple }
        | Enum _ -> { ty; content = Uninit })
    | Array { length; ty = ty' } ->
        let uninit_field _ = uninitialized ~tyenv ty' in
        let content = List.init length uninit_field in
        { ty; content = Array content }
    | Scalar _ | Ref _ | Ptr _ | Unresolved _ -> { ty; content = Uninit }
    | Slice _ -> Fmt.failwith "Cannot initialize unsized type"

  let uninitialized_outer ~tyenv ty =
    let root = uninitialized ~tyenv ty in
    { offset = None; root }

  let semi_concretize ~tyenv ~variant ty expr =
    (* FIXME: this assumes the values are initialized? Not entirely sure...
       I think we `Symbolic` means "initialized and symbolic!" *)
    Logging.tmi (fun m ->
        m "semi_concretize %a with ty %a and variant: %a" Expr.pp expr Ty.pp ty
          (Fmt.Dump.option Fmt.int) variant);
    let open Formula.Infix in
    let is_list v = (Expr.typeof v) #== (Expr.type_ ListType) in
    let has_length i l = (Expr.list_length l) #== (Expr.int i) in
    match ty with
    | Ty.Tuple v ->
        if%sat (is_list expr) #&& (has_length (List.length v) expr) then
          let values =
            List.init (List.length v) (fun i -> Expr.list_nth expr i)
          in
          let fields =
            List.map2 (fun ty e -> { content = Symbolic e; ty }) v values
          in
          DR.ok { ty; content = Fields fields }
        else too_symbolic expr
          (* FIXME: This is probably not the right error? *)
    | Array { length; ty = ty' } ->
        if%sat (is_list expr) #&& (has_length length expr) then
          let values = List.init length (fun i -> Expr.list_nth expr i) in
          let fields =
            List.map (fun e -> { content = Symbolic e; ty = ty' }) values
          in
          DR.ok { ty; content = Array fields }
        else too_symbolic expr
    | Adt (name, subst) -> (
        match Tyenv.adt_def ~tyenv name with
        | Struct (_repr, fields) ->
            if%sat (is_list expr) #&& (has_length (List.length fields) expr)
            then
              let values =
                List.init (List.length fields) (fun i -> Expr.list_nth expr i)
              in
              let fields =
                List.map2
                  (fun (_, ty) e ->
                    { content = Symbolic e; ty = Ty.subst_params ~subst ty })
                  fields values
              in
              DR.ok { ty; content = Fields fields }
            else too_symbolic expr
        | Enum variants ->
            (* This should only be called with a variant context *)
            let variant_idx = Option.get variant in
            let variant = List.nth variants variant_idx in
            let th_variant_idx = Expr.list_nth expr 0 in
            let th_fields = Expr.list_nth expr 1 in
            let number_fields = List.length (snd variant) in
            if%sat
              (* Value should have shape:
                 [ idx, [field_0, ..., field_n] ] *)
              (is_list expr) #&& (has_length 2 expr)
              #&& (th_variant_idx #== (Expr.int variant_idx))
              #&& (is_list th_fields)
              #&& (has_length number_fields th_fields)
            then
              let values =
                List.init number_fields (fun i -> Expr.list_nth th_fields i)
              in
              let fields =
                List.map2
                  (fun ty e ->
                    { content = Symbolic e; ty = Ty.subst_params ~subst ty })
                  (snd variant) values
              in
              DR.ok { ty; content = Enum { discr = variant_idx; fields } }
            else too_symbolic expr)
    | Scalar _ | Ref _ | Ptr _ ->
        failwith
          "I shouldn't ever need to concretize a scalar or something opaque"
    | Slice _ -> Fmt.failwith "Cannot initialize unsized type"
    | Unresolved e ->
        Fmt.failwith
          "Unresolved should have been resolved before getting to \
           `semi_concretize`: %a"
          Expr.pp e

  let rec partially_missing t =
    match t.content with
    | Missing -> true
    | Array fields | Fields fields -> List.exists partially_missing fields
    | Symbolic _ | Uninit | Enum _ | Leaf _ -> false

  let structural_missing ~tyenv (ty : Ty.t) =
    match ty with
    | Array { length; ty = cty } ->
        let missing_child = { ty = cty; content = Missing } in
        { ty; content = Array (List.init length (fun _ -> missing_child)) }
    | Tuple fields ->
        {
          ty;
          content =
            Fields (List.map (fun ty -> { content = Missing; ty }) fields);
        }
    | Adt _ -> failwith "not handled yet: Adt structural missing"
    | Scalar _ | Ref _ | Ptr _ | Unresolved _ | Slice _ ->
        Fmt.failwith "structural missing called on a leaf or unsized: %a" Ty.pp
          ty

  let rec find_path
      ~tyenv
      ~return_and_update
      t
      (path : Partial_layout.access list) : ('a * t, Err.t) DR.t =
    let rec_call = find_path ~tyenv ~return_and_update in
    let replace_vec c v =
      match c with
      | Fields _ -> Fields v
      | Array _ -> Array v
      | Enum { discr; _ } -> Enum { discr; fields = v }
      | _ -> failwith "impossible"
    in
    match (path, t) with
    | [], block ->
        let++ ret_value, new_block = return_and_update block in
        (ret_value, new_block)
    | { index; index_type = _; against; variant } :: r, { ty; content }
      when Ty.equal against ty -> (
        match (content, variant) with
        | (Fields vec | Array vec), None ->
            let e = Result.ok_or vec.%[index] "Index out of bounds" in
            let** v, sub_block = rec_call e r in
            let++ new_block = Delayed.return (vec.%[index] <- sub_block) in
            (v, { ty; content = replace_vec content new_block })
        | Enum { fields = vec; discr }, Some discr' when discr = discr' ->
            let** e = Delayed.return vec.%[index] in
            let** v, sub_block = rec_call e r in
            let++ new_block = Delayed.return (vec.%[index] <- sub_block) in
            (v, { ty; content = replace_vec content new_block })
        | Symbolic s, _ ->
            let** this_block = semi_concretize ~tyenv ~variant ty s in
            rec_call this_block path
        | Missing, None ->
            Logging.tmi (fun m ->
                m "strutural missing: %a "
                  (Fmt.Dump.list Partial_layout.pp_access)
                  path);
            let this_block = structural_missing ~tyenv ty in
            rec_call this_block path
        | _ -> Fmt.failwith "Invalid node")
    | _ -> failwith "Type mismatch"

  let get_forest ~tyenv outer (proj : Projections.t) size ty copy =
    let open Partial_layout in
    let base_equals =
      match (proj.base, outer.offset) with
      | None, None -> true
      | Some x, Some y -> Expr.equal x y
      | _ -> false
    in
    if not base_equals then failwith "Tree needs to be extended?";
    let t = outer.root in
    let start_address =
      {
        block_type = t.ty;
        route = proj.from_base;
        address_type = Ty.slice_elements ty;
      }
    in
    let context = context_from_env tyenv in
    let start_accesses = resolve_address ~tyenv ~context start_address in
    let start, array_accesses =
      match start_accesses with
      | { index; _ } :: r -> (index, List.rev r)
      | _ -> failwith "wrong slice pointer"
    in
    let update block =
      if copy then block
      else
        match block.content with
        | Array vec ->
            {
              content =
                Array
                  (Result.ok_or
                     (List_utils.override_range vec ~start ~size (fun _ ->
                          uninitialized ~tyenv ty))
                     "Invalid slice range");
              ty;
            }
        | _ -> failwith "Not an array"
    in
    let return_and_update block =
      let update = update block in
      match block.content with
      | Array vec ->
          let ret = List_utils.sublist_map ~start ~size ~f:to_rust_value vec in
          DR.ok (ret, update)
      | _ -> DR.error (Invalid_type (block.ty, ty))
    in
    let++ ret, root = find_path ~tyenv ~return_and_update t array_accesses in
    (ret, { outer with root })

  let set_forest ~tyenv outer (proj : Projections.t) size ty values =
    let open Partial_layout in
    let base_equals =
      match (proj.base, outer.offset) with
      | None, None -> true
      | Some x, Some y -> Expr.equal x y
      | _ -> false
    in
    if not base_equals then failwith "Tree needs to be extended?";
    let t = outer.root in
    assert (List.length values = size);
    let start_address =
      {
        block_type = t.ty;
        route = proj.from_base;
        address_type = Ty.slice_elements ty;
      }
    in
    let context = context_from_env tyenv in
    let start_accesses = resolve_address ~tyenv ~context start_address in
    let start, array_accesses =
      match start_accesses with
      | { index; _ } :: r -> (index, List.rev r)
      | _ -> failwith "wrong slice pointer"
    in
    let return_and_update block =
      match (block.content, block.ty) with
      | Array vec, Ty.Array { ty = ty'; _ } ->
          assert (Ty.equal ty ty');
          let++ overriden =
            DR_list.override_range_with_list vec ~start
              ~f:(of_rust_value ~tyenv ~ty) values
          in
          ((), { content = Array overriden; ty })
      | _ -> failwith "Not an array"
    in
    let++ _, new_block = find_path ~tyenv ~return_and_update t array_accesses in
    { outer with root = new_block }

  let find_proj
      ~tyenv
      ~return_and_update
      ~ty
      (outer : outer)
      (proj : Projections.t) =
    let open Partial_layout in
    let base_equals =
      match (proj.base, outer.offset) with
      | None, None -> true
      | Some x, Some y -> Expr.equal x y
      | _ -> false
    in
    if not base_equals then failwith "Tree needs to be extended?";
    let t = outer.root in
    let proj = proj.from_base in
    let address = { block_type = t.ty; route = proj; address_type = ty } in
    let context = context_from_env tyenv in
    Logging.normal (fun m ->
        m "Finding address: %a" (Fmt.Dump.list Projections.pp_elem) proj);
    Logging.normal (fun m ->
        m "PL for %a: %a" Ty.pp t.ty pp_partial_layout
          (context.partial_layouts t.ty));
    let accesses = resolve_address ~tyenv ~context address |> List.rev in
    Logging.normal (fun m ->
        m "Accessess: %a" (Fmt.Dump.list pp_access) accesses);
    let++ ret, root = find_path ~tyenv ~return_and_update t accesses in
    (ret, { outer with root })

  let get_proj ~tyenv t proj ty copy =
    let update block = if copy then block else uninitialized ~tyenv ty in
    let return_and_update t = DR.ok (to_rust_value t, update t) in
    find_proj ~tyenv ~return_and_update ~ty t proj

  let set_proj ~tyenv t proj ty value =
    let return_and_update block =
      let++ value = of_rust_value ~tyenv ~ty value in
      ((), value)
    in
    let++ _, new_block = find_proj ~tyenv ~ty ~return_and_update t proj in
    new_block

  let store_proj ~tyenv t proj ty value =
    let return_and_update block =
      if partially_missing block then DR.error (Err.Missing_proj proj)
      else
        let++ value = of_rust_value ~tyenv ~ty value in
        ((), value)
    in
    let++ _, new_block = find_proj ~tyenv ~ty ~return_and_update t proj in
    new_block

  let rem_proj ~tyenv t proj ty =
    let return_and_update _ = DR.ok ((), { ty; content = Missing }) in
    let++ _, new_block = find_proj ~tyenv ~ty ~return_and_update t proj in
    new_block

  let get_discr ~tyenv t proj enum_typ =
    let return_and_update block =
      match block.content with
      | Enum t -> DR.ok (Expr.int t.discr, block)
      | Symbolic expr ->
          let open Formula.Infix in
          if%sat
            (Expr.typeof expr) #== (Expr.type_ ListType)
            #&& ((Expr.list_length expr) #== (Expr.int 2))
          then DR.ok (Expr.list_nth expr 0, block)
          else too_symbolic expr
      | _ -> DR.error (Invalid_type (block.ty, enum_typ))
    in
    let++ discr, _ = find_proj ~tyenv ~return_and_update ~ty:enum_typ t proj in
    discr

  let deinit ~tyenv t proj ty =
    let return_and_update _block = DR.ok ((), uninitialized ~tyenv ty) in
    let++ _, new_block = find_proj ~tyenv ~ty ~return_and_update t proj in
    new_block

  let rec equality_constraints t1 t2 =
    let ( #== ) = Formula.Infix.( #== ) in
    match (t1.content, t2.content) with
    | Missing, _ | _, Missing -> []
    | (Symbolic e1 | Leaf e1), (Symbolic e2 | Leaf e2) -> [ e1 #== e2 ]
    | Fields f1, Fields f2 -> List_utils.concat_map_2 equality_constraints f1 f2
    | Array f1, Array f2 -> List_utils.concat_map_2 equality_constraints f1 f2
    | Enum e1, Enum e2 ->
        (* Sub parts of enum cannot be missing *)
        [ (to_rust_value t1) #== (to_rust_value t2) ]
    | Symbolic e, content | content, Symbolic e -> (
        try [ (to_rust_value { ty = t1.ty; content }) #== e ]
        with MemoryError _ ->
          failwith "Need to semi-concretize things to learn")
    | _ -> Fmt.failwith "cannot learn equality of %a and %a" pp t1 pp t2

  let substitution ~tyenv ~subst_expr t =
    let rec substitute_content ~ty t =
      match t with
      | Leaf e ->
          let e = subst_expr e in
          DR.ok ~learned:[ TypePreds.valid ty e ] (Leaf e)
      | Array lst ->
          let++ lst = DR_list.map substitution lst in
          Array lst
      | Fields lst ->
          let++ lst = DR_list.map substitution lst in
          Fields lst
      | Enum { fields; discr } ->
          let++ fields = DR_list.map substitution fields in
          Enum { fields; discr }
      | Symbolic s ->
          let new_s = subst_expr s in
          if new_s == s then DR.ok t
          else
            let++ value = of_rust_value ~tyenv ~ty new_s in
            value.content
      | Uninit | Missing -> DR.ok t
    and substitution t =
      let++ content = substitute_content ~ty:t.ty t.content in
      { t with content }
    in
    substitution t

  let outer_substitution ~tyenv ~subst_expr t =
    let** root = substitution ~tyenv ~subst_expr t.root in
    match t.offset with
    | None -> DR.ok { t with root }
    | Some offset ->
        let+ offset = Delayed.reduce (subst_expr offset) in
        Ok { offset = Some offset; root }

  let outer_equality_constraint (o1 : outer) (o2 : outer) =
    if not ((Option.equal Expr.equal) o1.offset o2.offset) then
      failwith "Cannot learn equality of two blocks of different offsets";
    if not (Ty.equal o1.root.ty o2.root.ty) then
      failwith "Cannot learn equality of two blocks of different types";
    equality_constraints o1.root o2.root
end

module MemMap = Map.Make (String)

type block = T of TreeBlock.outer | Freed
type t = block MemMap.t

let find_not_freed loc mem =
  let block = MemMap.find loc mem in
  match block with
  | T t -> DR.ok t
  | Freed -> DR.error (Use_after_free loc)

let to_yojson _ = `Null
let of_yojson _ = Error "Heap.of_yojson: Not implemented"

let alloc ~tyenv (heap : t) ty =
  let loc = ALoc.alloc () in
  let new_block = TreeBlock.uninitialized_outer ~tyenv ty in
  let new_heap = MemMap.add loc (T new_block) heap in
  (loc, new_heap)

let load ~tyenv (mem : t) loc proj ty copy =
  Logging.tmi (fun m -> m "Found block: %s" loc);
  let** block = find_not_freed loc mem in
  let++ v, new_block = TreeBlock.get_proj ~tyenv block proj ty copy in
  let new_mem = MemMap.add loc (T new_block) mem in
  (v, new_mem)

let load_slice ~tyenv (mem : t) loc proj size ty copy =
  let** block = find_not_freed loc mem in
  let++ vs, new_block = TreeBlock.get_forest ~tyenv block proj size ty copy in
  let new_mem = MemMap.add loc (T new_block) mem in
  (vs, new_mem)

let store_slice ~tyenv (mem : t) loc proj size ty values =
  let** block = find_not_freed loc mem in
  let++ new_block = TreeBlock.set_forest ~tyenv block proj size ty values in
  let new_mem = MemMap.add loc (T new_block) mem in
  new_mem

let store ~tyenv (mem : t) loc proj ty value =
  let** block = find_not_freed loc mem in
  let++ new_block = TreeBlock.store_proj ~tyenv block proj ty value in
  MemMap.add loc (T new_block) mem

let get_value ~tyenv (mem : t) loc proj ty =
  let** block = find_not_freed loc mem in
  let++ value, _ = TreeBlock.get_proj ~tyenv block proj ty false in
  value

let set_value ~tyenv (mem : t) loc (proj : Projections.t) ty value =
  let root =
    match MemMap.find_opt loc mem with
    | Some (T root) -> root
    | Some Freed -> failwith "use after free"
    | None ->
        TreeBlock.outer_missing ~offset:proj.base ~tyenv
          (Projections.base_ty ~leaf_ty:ty proj)
  in
  let++ new_block = TreeBlock.set_proj ~tyenv root proj ty value in
  MemMap.add loc (T new_block) mem

let rem_value (mem : t) loc =
  (* We assume that rem is *always* called after get.
     Therefore we don't need to check anything, we just remove. *)
  MemMap.remove loc mem

let deinit ~tyenv (mem : t) loc proj ty =
  let** block = find_not_freed loc mem in
  let++ new_block = TreeBlock.deinit ~tyenv block proj ty in
  MemMap.add loc (T new_block) mem

let free (mem : t) loc ty =
  let** block = find_not_freed loc mem in
  if Option.is_some block.offset then DR.error (MissingBlock loc)
  else if not (Ty.equal block.root.ty ty) then
    DR.error (Invalid_type (ty, block.root.ty))
  else DR.ok (MemMap.add loc Freed mem)

let load_discr ~tyenv (mem : t) loc proj enum_typ =
  let** block = find_not_freed loc mem in
  TreeBlock.get_discr ~tyenv block proj enum_typ

let assertions ~tyenv (mem : t) =
  let value (loc, block) =
    let loc = Expr.loc_from_loc_name loc in
    match block with
    | T block -> TreeBlock.outer_assertion ~loc block
    | Freed ->
        let cp = Actions.cp_to_name Freed in
        Asrt.GA (cp, [ loc ], [])
  in
  MemMap.to_seq mem |> Seq.map value |> List.of_seq

let empty : t = MemMap.empty

let pp : t Fmt.t =
  let open Fmt in
  let pp_block ft = function
    | Freed -> pf ft "FREED"
    | T t -> TreeBlock.pp_outer ft t
  in
  iter_bindings ~sep:(any "@\n") MemMap.iter
    (parens (pair ~sep:(any "-> ") string pp_block))

let substitution ~tyenv heap subst =
  let open Gillian.Symbolic in
  let non_loc = function
    | Expr.ALoc _ | Lit (Loc _) -> false
    | _ -> true
  in
  let () =
    if not (Expr.Set.is_empty (Subst.domain subst (Some non_loc))) then
      Fmt.pr "WARNING: SUBSTITUTION WITH LOCATIONS NO HANDLED\n@?"
  in
  let subst_expr = Subst.subst_in_expr subst ~partial:true in
  let++ new_mapping =
    MemMap.to_seq heap |> List.of_seq
    |> DR_list.map (fun (loc, block) ->
           let++ block =
             match block with
             | Freed -> DR.ok Freed
             | T block ->
                 let++ block =
                   TreeBlock.outer_substitution ~tyenv ~subst_expr block
                 in
                 T block
           in
           (loc, block))
  in
  List.to_seq new_mapping |> MemMap.of_seq
