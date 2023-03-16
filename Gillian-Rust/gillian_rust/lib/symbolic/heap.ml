open Gillian.Gil_syntax
open List_utils.Infix
open Gillian.Monadic
open Err
module DR = Delayed_result
module Tyenv = Common.Tyenv
module Actions = Common.Actions

exception NotConcrete of string

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
    | Scalar of Expr.t
    | Fields of t list
    | Array of t list
    | Enum of { discr : int; fields : t list }
    | ThinPtr of Expr.t * Projections.t
    | FatPtr of Expr.t * Projections.t * int
    | Uninit

  let rec pp fmt { ty; content } =
    Fmt.pf fmt "%a :@ %a" pp_content content Ty.pp ty

  and pp_content ft =
    let open Fmt in
    function
    | Scalar e -> Expr.pp ft e
    | Fields v -> (parens (Fmt.list ~sep:Fmt.comma pp)) ft v
    | Enum { discr; fields } ->
        pf ft "%a[%a]" int discr (Fmt.list ~sep:comma pp) fields
    | ThinPtr (loc, proj) -> pf ft "Ptr(%a, %a)" Expr.pp loc Projections.pp proj
    | FatPtr (loc, proj, meta) ->
        pf ft "FatPtr(%a, %a | %d)" Expr.pp loc Projections.pp proj meta
    | Array v -> (brackets (Fmt.list ~sep:comma pp)) ft v
    | Symbolic s -> Expr.pp ft s
    | Uninit -> Fmt.string ft "UNINIT"

  let rec to_rust_value ~tyenv ({ content; ty } as t) =
    match content with
    | Scalar s -> (
        match (ty, s) with
        | Scalar (Uint _ | Int _ | Char), _ -> s
        | Scalar Bool, e -> e
        | _ -> Fmt.failwith "Malformed tree: %a" pp t)
    | Fields v | Array v ->
        let tuple = List.map (to_rust_value ~tyenv) v in
        EList tuple
    | Enum { discr; fields } ->
        let fields = List.map (to_rust_value ~tyenv) fields in
        Expr.EList [ Expr.int discr; EList fields ]
    | ThinPtr (loc, proj) -> EList [ loc; Projections.to_expr proj ]
    | FatPtr (loc, proj, meta) ->
        EList
          [
            EList [ loc; EList (Projections.to_expr_list proj) ]; Expr.int meta;
          ]
    | Symbolic s -> s
    | Uninit -> mem_error "Attempting to read uninitialized value"

  let rec of_rust_struct_value
      ~tyenv
      ~ty
      ~subst
      ~fields_tys
      (fields : Expr.t list) =
    let content =
      List.map2
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
        let fields =
          List.map2
            (fun t v -> of_rust_value ~tyenv ~ty:(Ty.subst_params ~subst t) v)
            tys fields
        in
        let content = Enum { discr = vidx; fields } in
        { ty; content }
    | _ ->
        Fmt.failwith "Invalid enum value for type %a: %a" Ty.pp ty
          (Fmt.list Expr.pp) data

  and of_rust_value ~tyenv ~ty (e : Expr.t) =
    match (ty, e) with
    | Ty.Scalar (Uint _ | Int _), e -> { ty; content = Scalar e }
    | Ty.Scalar Bool, e -> { ty; content = Scalar e }
    | Tuple _, Lit (LList data) ->
        let content = List.map lift_lit data in
        of_rust_value ~tyenv ~ty (EList content)
    | Tuple ts, EList tup ->
        let content =
          List.map2 (fun t v -> of_rust_value ~tyenv ~ty:t v) ts tup
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
    | Ref { ty = Slice _; _ }, EList [ EList [ loc; proj ]; Lit (Int i) ] ->
        let proj = concretize_proj proj in
        let content = FatPtr (loc, proj, Z.to_int i) in
        { ty; content }
    | Ref _, e ->
        let loc = Expr.list_nth e 0 in
        let proj = Expr.list_nth e 1 in
        let proj = Projections.of_expr proj in
        let content = ThinPtr (loc, proj) in
        { ty; content }
    | Array { length; ty = ty' }, EList l
      when List.compare_length_with l length == 0 ->
        let mem_array = List.map (of_rust_value ~tyenv ~ty:ty') l in
        { ty; content = Array mem_array }
    | _, s -> { ty; content = Symbolic s }

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
    | Scalar _ | Ref _ | Unresolved _ -> { ty; content = Uninit }
    | Slice _ -> Fmt.failwith "Cannot initialize unsized type"

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
        else DR.error (Too_symbolic expr)
          (* FIXME: This is probably not the right error? *)
    | Array { length; ty = ty' } ->
        if%sat (is_list expr) #&& (has_length length expr) then
          let values = List.init length (fun i -> Expr.list_nth expr i) in
          let fields =
            List.map (fun e -> { content = Symbolic e; ty = ty' }) values
          in
          DR.ok { ty; content = Array fields }
        else DR.error (Too_symbolic expr)
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
            else DR.error (Too_symbolic expr)
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
            else DR.error (Too_symbolic expr))
    | Scalar _ | Ref _ ->
        failwith
          "I shouldn't ever need to concretize a scalar or something opaque"
    | Slice _ -> Fmt.failwith "Cannot initialize unsized type"
    | Unresolved e ->
        Fmt.failwith
          "Unresolved should have been resolved before getting to \
           `semi_concretize`: %a"
          Expr.pp e

  let rec find_path
      ~tyenv
      ~return_and_update
      t
      (path : Partial_layout.access list) : ('a * t, Err.t) DR.t =
    let open DR.Syntax in
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
        | _ -> Fmt.failwith "Invalid node")
    | _ -> failwith "Type mismatch"

  let get_forest ~tyenv t proj size ty copy =
    let open Partial_layout in
    let start_address =
      { block_type = t.ty; route = proj; address_type = Ty.slice_elements ty }
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
          let ret =
            List_utils.sublist_map ~start ~size ~f:(to_rust_value ~tyenv) vec
          in
          DR.ok (ret, update)
      | _ -> DR.error (Invalid_type (block.ty, ty))
    in
    find_path ~tyenv ~return_and_update t array_accesses

  let set_forest ~tyenv t proj size ty values =
    let open DR.Syntax in
    assert (List.length values = size);
    let open Partial_layout in
    let start_address =
      { block_type = t.ty; route = proj; address_type = Ty.slice_elements ty }
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
          DR.ok
            ( (),
              {
                content =
                  Array
                    (Result.ok_or
                       (List_utils.override_range_with_list vec ~start
                          ~f:(of_rust_value ~tyenv ~ty) values)
                       "Invalid slice range");
                ty;
              } )
      | _ -> failwith "Not an array"
    in
    let++ _, new_block = find_path ~tyenv ~return_and_update t array_accesses in
    ((), new_block)

  let find_proj ~tyenv ~return_and_update ~ty t proj =
    let open Partial_layout in
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
    find_path ~tyenv ~return_and_update t accesses

  let get_proj ~tyenv t proj ty copy =
    let update block = if copy then block else uninitialized ~tyenv ty in
    let return_and_update t = DR.ok (to_rust_value ~tyenv t, update t) in
    find_proj ~tyenv ~return_and_update ~ty t proj

  let set_proj ~tyenv t proj ty value =
    let open DR.Syntax in
    let return_and_update _ = DR.ok ((), of_rust_value ~tyenv ~ty value) in
    let++ _, new_block = find_proj ~tyenv ~ty ~return_and_update t proj in
    ((), new_block)

  let get_discr ~tyenv t proj enum_typ =
    let open DR.Syntax in
    let return_and_update block =
      match block.content with
      | Enum t -> DR.ok (Expr.int t.discr, block)
      | Symbolic expr ->
          let open Formula.Infix in
          if%sat
            (Expr.typeof expr) #== (Expr.type_ ListType)
            #&& ((Expr.list_length expr) #== (Expr.int 2))
          then DR.ok (Expr.list_nth expr 0, block)
          else DR.error (Too_symbolic expr)
      | _ -> DR.error (Invalid_type (block.ty, enum_typ))
    in
    let++ discr, _ = find_proj ~tyenv ~return_and_update ~ty:enum_typ t proj in
    discr

  let deinit ~tyenv t proj ty =
    let open DR.Syntax in
    let return_and_update _block = DR.ok ((), uninitialized ~tyenv ty) in
    let++ _, new_block = find_proj ~tyenv ~ty ~return_and_update t proj in
    new_block

  let substitution ~tyenv ~subst_expr t =
    let rec substitute_content ~ty t =
      match t with
      | Scalar e ->
          let new_e = subst_expr e in
          if new_e == e then t else Scalar new_e
      | Array lst ->
          let changed, new_list = substitute_list lst in
          if changed then Array new_list else t
      | Fields lst ->
          let changed, new_list = substitute_list lst in
          if changed then Fields new_list else t
      | Enum { fields; discr } ->
          let changed, new_fields = substitute_list fields in
          if changed then Enum { fields = new_fields; discr } else t
      | ThinPtr (e, proj) ->
          let new_e = subst_expr e in
          let new_proj = Projections.substitution ~subst_expr proj in
          if new_e == e && new_proj == proj then t else ThinPtr (new_e, proj)
      | FatPtr (e, proj, i) ->
          let new_e = subst_expr e in
          let new_proj = Projections.substitution ~subst_expr proj in
          if new_e == e && new_proj == proj then t else FatPtr (new_e, proj, i)
      | Symbolic s ->
          let new_s = subst_expr s in
          if new_s == s then t else (of_rust_value ~tyenv ~ty new_s).content
      | Uninit -> t
    and substitution t =
      let new_content = substitute_content ~ty:t.ty t.content in
      if new_content == t.content then t else { t with content = new_content }
    and substitute_list lst =
      List.fold_left_map
        (fun changed t ->
          let new_t = substitution t in
          (changed || new_t != t, new_t))
        false lst
    in
    substitution t
end

module HeapMap = Map.Make (String)

module TimedTree = struct
  type t =
    | Owned of { tree : TreeBlock.t; dead_until : Lft.t option }
    | Borrowed of {
        current : TreeBlock.t;
        prophecy : TreeBlock.t;
        alive_while : Lft.t;
        dead_until : Lft.t option;
      }

  let pp ft t =
    let pp_dead_until =
      Fmt.option (fun ft lft -> Fmt.pf ft "[†%a] " Lft.pp lft)
    in
    match t with
    | Owned { tree; dead_until } ->
        Fmt.pf ft "%a%a" pp_dead_until dead_until TreeBlock.pp tree
    | Borrowed { current; prophecy; alive_while; dead_until } ->
        Fmt.pf ft "%a<%a> { %a ==> %a }" pp_dead_until dead_until Lft.pp
          alive_while TreeBlock.pp current TreeBlock.pp prophecy

  let owned_uninitialize ~tyenv ty =
    Owned { tree = TreeBlock.uninitialized ~tyenv ty; dead_until = None }

  let accessible ~lfts t =
    match t with
    | Owned { dead_until; _ } -> Option.is_none dead_until
    | Borrowed { alive_while; dead_until; _ } ->
        let is_alive = Lft_ctx.check_alive lfts alive_while |> Result.is_ok in
        let is_not_dead = Option.is_none dead_until in
        is_alive && is_not_dead

  let update_current ~f t =
    let open DR.Syntax in
    match t with
    | Owned { tree; dead_until } ->
        let++ v, new_tree = f tree in
        (v, Owned { tree = new_tree; dead_until })
    | Borrowed { current; prophecy; alive_while; dead_until } ->
        let++ v, new_tree = f current in
        (v, Borrowed { current = new_tree; prophecy; alive_while; dead_until })

  let read_current ~f t =
    match t with
    | Owned { tree; _ } -> f tree
    | Borrowed { current; _ } -> f current

  (* This function will either drop a borrow, learning equality, or free if its owned and it can *)
  let free_or_learn ~tyenv ~ty t =
    match t with
    | Borrowed _ -> failwith "free_or_learn.borrow Not handled for now"
    | Owned { tree; dead_until } ->
        if Option.is_none dead_until then
          if Ty.equal tree.ty ty then DR.ok ()
          else DR.error (Invalid_type (ty, tree.ty))
        else DR.error (Cannot_access "aaaaa")

  let substitution ~tyenv ~subst_expr t =
    match t with
    | Owned { tree; dead_until } ->
        Owned
          {
            tree = TreeBlock.substitution ~tyenv ~subst_expr tree;
            dead_until = Option.map (Lft.substitution ~subst_expr) dead_until;
          }
    | Borrowed { current; prophecy; dead_until; alive_while } ->
        Borrowed
          {
            current = TreeBlock.substitution ~tyenv ~subst_expr current;
            prophecy = TreeBlock.substitution ~tyenv ~subst_expr prophecy;
            dead_until = Option.map (Lft.substitution ~subst_expr) dead_until;
            alive_while = Lft.substitution ~subst_expr alive_while;
          }
end

type block = T of TimedTree.t list | Freed
type t = block HeapMap.t

let update_not_freed ~lfts loc heap f =
  let open DR.Syntax in
  let block = HeapMap.find loc heap in
  match block with
  | T (t :: ts) ->
      if TimedTree.accessible ~lfts t then
        let++ v, new_t = TimedTree.update_current ~f t in
        let new_heap = HeapMap.add loc (T (new_t :: ts)) heap in
        (v, new_heap)
      else DR.error (Cannot_access loc)
  | T [] -> failwith "empty blocks, cannot happen"
  | Freed -> DR.error (Use_after_free loc)

let read_not_freed ~lfts loc heap f =
  let block = HeapMap.find loc heap in
  match block with
  | T (t :: ts) ->
      if TimedTree.accessible ~lfts t then TimedTree.read_current ~f t
      else DR.error (Cannot_access loc)
  | T [] -> failwith "empty blocks, cannot happen"
  | Freed -> DR.error (Use_after_free loc)

let to_yojson _ = `Null
let of_yojson _ = Error "Heap.of_yojson: Not implemented"

let alloc ~tyenv (heap : t) ty =
  let loc = ALoc.alloc () in
  let new_block = [ TimedTree.owned_uninitialize ~tyenv ty ] in
  let new_heap = HeapMap.add loc (T new_block) heap in
  (loc, new_heap)

let load ~tyenv ~lfts (heap : t) loc proj ty copy =
  update_not_freed ~lfts loc heap (fun block ->
      TreeBlock.get_proj ~tyenv block proj ty copy)

let store ~tyenv ~lfts (heap : t) loc proj ty value =
  let open DR.Syntax in
  let++ (), new_heap =
    update_not_freed ~lfts loc heap (fun block ->
        TreeBlock.set_proj ~tyenv block proj ty value)
  in
  new_heap

let load_slice ~tyenv ~lfts (heap : t) loc proj size ty copy =
  update_not_freed ~lfts loc heap (fun block ->
      TreeBlock.get_forest ~tyenv block proj size ty copy)

let store_slice ~tyenv ~lfts (heap : t) loc proj size ty values =
  let open DR.Syntax in
  let++ (), new_heap =
    update_not_freed ~lfts loc heap (fun block ->
        TreeBlock.set_forest ~tyenv block proj size ty values)
  in
  new_heap

(* let borrow ~tyenv ~lfts (heap: t) loc proj lft =
   let open DR.Syntax in
   let block = HeapMap.find loc heap in
   match block with
   | T (t::ts) ->
     if TimedTree.accessible ~lfts t then
       let++ new_borrow, frozen = TimedTree.borrow ~tyenv ~lfts t proj lft in *)

let get_value ~tyenv (heap : t) loc proj ty =
  failwith "consumers and producers are not working"
(* let open DR.Syntax in
   let** () =
     match proj with
     | [] -> DR.ok ()
     | _ -> DR.error (Unhandled "can't handle projections on cps yet")
   in
   let** block = find_not_freed loc heap in
   let++ value, _ = TreeBlock.get_proj ~tyenv block [] ty false in
   value *)

let set_value ~tyenv (heap : t) loc proj ty value =
  failwith "consumers and producers are not working"
(* let open DR.Syntax in
   let++ () =
     match (proj, HeapMap.find_opt loc heap) with
     | [], None -> DR.ok ()
     | _ ->
         DR.error
           (Unhandled "can't handle projections or setting with frame yet")
   in
   let new_block = T (TreeBlock.of_rust_value ~tyenv ~ty value) in
   HeapMap.add loc new_block heap *)

let rem_value (heap : t) loc =
  (* We assume that rem is *always* called after get.
     Therefore we don't need to check anything, we just remove. *)
  HeapMap.remove loc heap

let deinit ~tyenv ~lfts (heap : t) loc proj ty =
  let open DR.Syntax in
  let++ (), new_heap =
    update_not_freed ~lfts loc heap (fun block ->
        let++ new_block = TreeBlock.deinit ~tyenv block proj ty in
        ((), new_block))
  in
  new_heap

let free ~tyenv ~lfts:_ (heap : t) loc ty =
  let open DR.Syntax in
  match HeapMap.find_opt loc heap with
  | Some Freed -> DR.error (Use_after_free loc)
  | Some (T block_infos) ->
      let++ () =
        List.fold_left
          (fun acc block ->
            let** () = acc in
            TimedTree.free_or_learn ~tyenv ~ty block)
          (DR.ok ()) block_infos
      in
      HeapMap.add loc Freed heap
  | None -> DR.error (Missing_block loc)

let load_discr ~tyenv ~lfts (heap : t) loc proj enum_typ =
  let open DR.Syntax in
  read_not_freed ~lfts loc heap (fun block ->
      TreeBlock.get_discr ~tyenv block proj enum_typ)

let assertions ~tyenv (heap : t) = failwith "to_assertion is not working"
(* let value (loc, block) =
     match block with
     | T block ->
         let cp = Actions.cp_to_name Value in
         let ty = Ty.to_expr block.TreeBlock.ty in
         let value = TreeBlock.to_rust_value ~tyenv block in
         Asrt.GA
           (cp, [ Expr.loc_from_loc_name loc; Expr.EList []; ty ], [ value ])
     | Freed ->
         let cp = Actions.cp_to_name Freed in
         Asrt.GA (cp, [ Expr.loc_from_loc_name loc ], [])
   in
   HeapMap.to_seq heap |> Seq.map value |> List.of_seq *)

let empty : t = HeapMap.empty

let pp : t Fmt.t =
  let open Fmt in
  let pp_block ft = function
    | Freed -> pf ft "FREED"
    | T t -> (Fmt.list ~sep:(any " |@ ") TimedTree.pp) ft t
  in
  iter_bindings ~sep:(any "@\n") HeapMap.iter
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
  HeapMap.map
    (function
      | Freed -> Freed
      | T block ->
          T (List.map (TimedTree.substitution ~tyenv ~subst_expr) block))
    heap
