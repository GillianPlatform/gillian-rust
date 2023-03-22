module Tyenv = Common.Tyenv
module Adt_def = Common.Ty.Adt_def
open Projections

type variant_idx = int [@@deriving eq, show]
type size = int [@@deriving eq, show]

let align pow offset =
  let modulus = Int.shift_left 1 pow in
  let r = offset mod modulus in
  match r with
  | 0 -> offset
  | _ -> offset - r + modulus

module Partial_align = struct
  type t = ExactlyPow2 of int | AtLeastPow2 of int | ToType of Ty.t
  [@@deriving eq, show]

  let max a a' =
    match (a, a') with
    | ExactlyPow2 a, ExactlyPow2 a' -> ExactlyPow2 (max a a')
    | AtLeastPow2 a, AtLeastPow2 a'
    | ExactlyPow2 a, AtLeastPow2 a'
    | AtLeastPow2 a, ExactlyPow2 a' -> AtLeastPow2 (max a a')
    | ExactlyPow2 0, ToType t | ToType t, ExactlyPow2 0 -> ToType t
    | ExactlyPow2 a, ToType _
    | AtLeastPow2 a, ToType _
    | ToType _, ExactlyPow2 a
    | ToType _, AtLeastPow2 a -> AtLeastPow2 a
    | ToType t, ToType t' when Ty.equal t t' -> ToType t
    | ToType _, ToType _ -> AtLeastPow2 0

  let strictly_le (a : t) (a' : t) =
    match (a, a') with
    | ExactlyPow2 a, ExactlyPow2 a' -> a <= a'
    | ToType t, ToType t' -> Ty.equal t t'
    | ExactlyPow2 a, AtLeastPow2 a' -> a <= a'
    | _, _ -> false

  let maximum = Seq.fold_left max (ExactlyPow2 0)
end

module Partial_size = struct
  type t = Exactly of size | AtLeast of size [@@deriving eq, show]

  let map f = function
    | Exactly size -> Exactly (f size)
    | AtLeast size -> AtLeast (f size)

  let from_alignment : Partial_align.t -> t = function
    | ExactlyPow2 n -> Exactly (Int.shift_left 1 n)
    | AtLeastPow2 n -> AtLeast (Int.shift_left 1 n)
    | ToType _ -> AtLeast 0

  let add sz sz' =
    match (sz, sz') with
    | Exactly sz, Exactly sz' -> Exactly (sz + sz')
    | AtLeast sz, AtLeast sz'
    | Exactly sz, AtLeast sz'
    | AtLeast sz, Exactly sz' -> AtLeast (sz + sz')

  let sum = Seq.fold_left add (Exactly 0)

  let align_to (alignment : Partial_align.t) (size : t) =
    match alignment with
    (* Add as much information as is known to the size, so we can work out the known minimum possible size *)
    | ToType _ -> size
    | ExactlyPow2 s -> map (align s) size
    | AtLeastPow2 s -> map (align s) size
end

type align = { pow2 : int } [@@deriving eq, show]
type wrapping_range = { start : int; finish : int } [@@deriving eq, show]
type base_integer = I8 | I16 | I32 | I64 | I128 [@@deriving eq, show]

type primitive = Int of base_integer * bool | F32 | F64 | Pointer
[@@deriving eq, show]

type scalar = { primitive : primitive; valid_range : wrapping_range }
[@@deriving eq, show]

type offset =
  | Bytes of size
  | FromIndex of int * size
  | FromCount of Ty.t * int * size
[@@deriving eq, show]

type fields_shape =
  | Primitive
  | Union of int
  | Array of Partial_size.t * int
  (* offset array includes the offset of the end *)
  | Arbitrary of offset array
[@@deriving eq, show]

type variants =
  | Single of variant_idx
  | Multiple of { tag : scalar option; variants : partial_layout array }
[@@deriving eq, show]

and partial_layout = {
  fields : fields_shape;
  variant : variants;
  align : Partial_align.t;
  size : Partial_size.t;
}
[@@deriving eq, show]

type context = {
  partial_layouts : Ty.t -> partial_layout;
  members : Ty.t -> Ty.t array;
  variant_members : Ty.t -> variant_idx -> Ty.t array;
}

let rec contextualise (context : context) (route : op list) : op list =
  match route with
  | Plus (w, i, t) :: rs -> (
      match (context.partial_layouts t).size with
      | Exactly sz -> UPlus (w, sz * i) :: contextualise context rs
      | _ -> Plus (w, i, t) :: contextualise context rs)
  | Index (i, t, n) :: rs when i < n ->
      Cast (Ty.Array { length = n; ty = t }, t)
      :: contextualise context (Plus (Overflow, i, t) :: rs)
  | Field (i, t) :: rs -> (
      let t' = (context.members t).(i) and rs' = contextualise context rs in
      match (context.partial_layouts t).fields with
      | Arbitrary os -> (
          match os.(i) with
          | Bytes n -> Cast (t, t') :: UPlus (Overflow, n) :: rs'
          | FromIndex (i', n) ->
              Field (i', t)
              :: Cast ((context.members t).(i'), t')
              :: UPlus (Overflow, n)
              :: rs'
          | FromCount (t'', n, n') ->
              Cast (t, t'')
              :: Plus (Overflow, n, t'')
              :: Cast (t'', t')
              :: UPlus (Overflow, n')
              :: rs')
      | _ -> Field (i, t) :: contextualise context rs)
  | r :: rs -> r :: contextualise context rs
  | [] -> []

let reorder : op list -> op list =
  let rec reorder' upluss rs =
    match rs with
    | (UPlus (_, _) as r) :: rs -> reorder' (r :: upluss) rs
    | (Cast (_, _) as r) :: rs -> r :: reorder' upluss rs
    | r :: rs -> List.rev_append upluss (r :: reorder' upluss rs)
    | [] -> List.rev upluss
  in
  reorder' []

let rec simplify : op list -> op list = function
  (* We have to handle 0s/Identity casts removed from the next element, since they could lead to two elements being next to each other and simplifying *)
  | r :: Plus (_, 0, _) :: rs -> simplify (r :: rs)
  | r :: UPlus (_, 0) :: rs -> simplify (r :: rs)
  | r :: Cast (t, t') :: rs when t = t' -> simplify (r :: rs)
  | Plus (Wrap, i, t) :: Plus (Wrap, i', t') :: rs when t = t' ->
      simplify (Plus (Wrap, i + i', t) :: rs)
  | UPlus (Wrap, i) :: UPlus (Wrap, i') :: rs ->
      simplify (UPlus (Wrap, i + i') :: rs)
  | Plus (Overflow, i, t) :: Plus (Overflow, i', t') :: rs
    when i * i' > 0 && t = t' -> simplify (Plus (Overflow, i + i', t) :: rs)
  | UPlus (Overflow, i) :: UPlus (Overflow, i') :: rs when i * i' > 0 ->
      simplify (UPlus (Overflow, i + i') :: rs)
  | Cast (t, t'') :: Cast (t''', t') :: rs when t'' = t''' ->
      simplify (Cast (t, t') :: rs)
  (* We also have to handle 0s if they're at the front, from other rules or as the last element *)
  | Plus (_, 0, _) :: rs -> simplify rs
  | UPlus (_, 0) :: rs -> simplify rs
  | Cast (t, t') :: rs when t = t' -> simplify rs
  | r :: rs -> r :: simplify rs
  | [] -> []

let reduce context rs = simplify @@ reorder @@ contextualise context rs

type address = { block_type : Ty.t; route : op list; address_type : Ty.t }

type access = {
  index : int;
  index_type : Ty.t;
  against : Ty.t;
  variant : variant_idx option;
}
[@@deriving eq, show]

let distance_to_next_field (partial_layout : partial_layout) (a : int) =
  match partial_layout.fields with
  | Arbitrary offsets when a >= 0 && a + 1 < Array.length offsets -> (
      (* Format.printf "offsets.(a)=%a, offsets.(a+1)=%a 179;\n" pp_offset
         offsets.(a) pp_offset
         offsets.(a + 1); *)
      match (offsets.(a), offsets.(a + 1)) with
      | Bytes n, Bytes n' -> Some (Bytes (n' - n))
      | FromIndex (n, b), FromIndex (n', b') when n = n' ->
          Some (Bytes (b' - b))
      | FromCount (t, n, b), FromCount (t', n', b') when t = t' ->
          let b'' = b' - b in
          Some (if n' == n then Bytes b'' else FromCount (t, n' - n, b''))
      | Bytes b, FromCount (t, n, b') -> Some (FromCount (t, n, b + b'))
      | Bytes b, FromIndex (i, b') -> Some (FromIndex (i, b + b'))
      | _, _ -> None)
  | _ -> None

exception AccessError of access list * op list * Ty.t * int option * string

let () =
  Printexc.register_printer (function
    | AccessError (accesses, ops, ty, idx, msg) ->
        let open Fmt in
        Some
          (str "AccessError(%a, %a, %a, %a, %s)" (Dump.list pp_access) accesses
             Projections.pp_from_base ops Ty.pp ty (Dump.option int) idx msg)
    | _ -> None)

module UpTreeDirection = struct
  type t = Curr | Fwd

  let magnitude = function
    | Curr -> 0
    | Fwd -> 1
end

module DownTreeDirection = struct
  type t = Bkwd | Curr

  let from_int i = if i < 0 then Bkwd else Curr

  let magnitude = function
    | Bkwd -> -1
    | Curr -> 0
end

(* Divide rounding towards -signum(m) * inf *)
let div' (n : int) (m : int) = (n / m) - if n * m < 0 then 1 else 0

let mod' (n : int) (m : int) =
  let res = n mod m in
  if res < 0 then res + m else res

let signum (n : int) = if n < 0 then -1 else if n = 0 then 0 else 1

let rec resolve
    ~tyenv
    ~(context : context)
    (accesses : access list)
    (ty : Ty.t)
    (rs : op list)
    (index : int option) : access list =
  let resolve = resolve ~tyenv ~context in
  (* let dump_state () =
          (* FOR DEBUG PURPOSES, TODO REMOVE *)
          Format.printf "\nDUMP\n\tty=%a\n\tindex=%s\n\trs=[" Ty.pp ty
          @@ Option.fold ~none:"- (None)" ~some:Int.to_string index;
          List.iter (Format.printf "%a;\n" Projections.pp_op) rs;
          Format.print_string "]\n\taccesses=[";
          List.iter (Format.printf "%a;\n" pp_access) accesses;
          Format.print_string "]\nEND\n"
        in
     Format.printf "RESOLVE <--new";
        dump_state (); *)
  let ix =
    if Option.is_some index then index
    else
      match (context.partial_layouts ty).fields with
      | Arbitrary [||] -> None
      | Arbitrary offsets
        when (* print_string "offsets.(0) 210;\n"; *)
             offsets.(0) = Bytes 0 -> Some 0
      | Array (_, _) -> Some 0
      | _ -> None
  and accesses' ?variant index index_type =
    { index; index_type; against = ty; variant } :: accesses
  in
  let access_error message =
    raise (AccessError (accesses, rs, ty, ix, message))
  in
  (* Both `tree_cast`s are currently invalid, not checking if moving forwards/backwards is allowed with respect to padding*)
  let down_tree_cast (dir : DownTreeDirection.t) =
    match ix with
    | Some ix ->
        let ix' = ix + DownTreeDirection.magnitude dir in
        (* Format.printf "(context.members ty).(ix') 219 : %d\n" ix'; *)
        let ix'_type = (context.members ty).(ix') in
        let casted_ix =
          match dir with
          | DownTreeDirection.Bkwd ->
              Some (Array.length (context.members ix'_type))
              (* We can't guarantee we should be using indices for the previous index *)
          | DownTreeDirection.Curr -> None
        in
        resolve (accesses' ix' ix'_type) ix'_type rs casted_ix
    | None -> access_error "Can't down-tree cast from no known index"
  in
  let rec up_tree_cast dir accesses' rs' =
    match accesses' with
    (* We're not checking whether the type cast to is meant to have indices, but this should be fine as it won't be able to progress once there *)
    | { index; index_type = _; against; variant = _ } :: as' ->
        let max_ix = Array.length (context.members against) - 1
        and ix' = index + UpTreeDirection.magnitude dir in
        if ix' <= max_ix then resolve as' against rs' (Some ix')
        else up_tree_cast dir as' rs'
    | [] ->
        access_error "Could not up tree cast from beyond top of access stack"
  in

  match (rs, ix) with
  | Field (i, t) :: rs', None when t = ty ->
      (* print_string "(context.members t).(i) 243;\n"; *)
      let t' = (context.members t).(i) in
      resolve (accesses' i t') t' rs' None
  (* TODO handle invalid indices etc. *)
  | Field (i, t) :: rs', Some 0 when Ty.equal t ty ->
      resolve accesses ty rs' (Some i)
  | Index (i, t, n) :: rs', Some ix
    when i < n && Ty.equal (Array { length = n; ty = t }) ty ->
      resolve accesses ty rs' (Some (i + ix))
  | VField (j, t, idx) :: rs', None when Ty.equal t ty ->
      (* print_string "(context.members t).(i) 253;\n"; *)
      let t' = (context.variant_members t idx).(j) in
      resolve (accesses' ~variant:idx j t') t rs' None
  | Cast (_, _) :: rs', ix -> resolve accesses ty rs' ix
  | Plus (_, 0, _) :: _, _ ->
      access_error "Invalid +^t 0 should not exist at resolution stage"
  | Plus (w, i, t) :: rs', Some ix -> (
      let i' = i + ix
      and modify_plus_eliminating_zero new_i =
        if new_i = 0 then rs' else Plus (w, new_i, t) :: rs'
      and partial_layout = context.partial_layouts ty in
      match ty with
      | Ty.Array { ty = tElem; length = n } when tElem = t ->
          if i' < 0 then
            up_tree_cast UpTreeDirection.Curr accesses
              (modify_plus_eliminating_zero i')
          else if i' < n then resolve accesses ty rs' @@ Some i'
          else
            up_tree_cast UpTreeDirection.Fwd accesses
              (modify_plus_eliminating_zero @@ (i' - n))
      | Adt (name, _args) -> (
          match Tyenv.adt_def ~tyenv name with
          | Struct _ -> (
              let moving_over_field, next_i, next_ix =
                if i < 0 then (ix - 1, ( + ) i, ix - 1)
                else (ix, ( - ) i, ix + 1)
              and members = context.members ty in
              if i < 0 && ix = 0 then
                (* We can up-tree cast directly since we're at field ix 0 *)
                up_tree_cast UpTreeDirection.Curr accesses rs
              else
                (* (match distance_to_next_field partial_layout moving_over_field with
                   | Some offset -> Format.printf "%a 313;\n" pp_offset offset
                   | None        -> print_string "NO OFFSET 313;\n"); *)
                match
                  distance_to_next_field partial_layout moving_over_field
                with
                | Some (FromCount (t', n, 0)) when t' = t ->
                    (if next_ix = Array.length members then
                     up_tree_cast UpTreeDirection.Fwd accesses
                    else fun rs'' -> resolve accesses ty rs'' @@ Some next_ix)
                      (modify_plus_eliminating_zero (next_i n))
                | _ -> down_tree_cast (DownTreeDirection.from_int i))
          | _ -> down_tree_cast (DownTreeDirection.from_int i))
      | _ -> down_tree_cast (DownTreeDirection.from_int i))
  | UPlus (_, 0) :: _, _ ->
      access_error "Invalid +^U 0 should not exist at resolution stage"
  | UPlus (w, i) :: rs', Some ix -> (
      let modify_uplus_eliminating_zero new_i =
        if new_i = 0 then rs' else UPlus (w, new_i) :: rs'
      and partial_layout = context.partial_layouts ty in
      match ty with
      | Ty.Array { ty = tElem; length = n } -> (
          match (context.partial_layouts tElem).size with
          | Exactly size ->
              let ix' = ix + div' i size and rem = mod' i size in
              if ix' < 0 then
                up_tree_cast UpTreeDirection.Curr accesses
                @@ modify_uplus_eliminating_zero
                @@ ((ix * size) + i)
                (* We must only handle cases where we can make progress at this level, otherwise down_tree_cast *)
              else if ix' = ix then
                down_tree_cast (DownTreeDirection.from_int i)
              else if ix' < n then
                resolve accesses ty
                  (modify_uplus_eliminating_zero rem)
                  (Some ix')
              else
                up_tree_cast UpTreeDirection.Fwd accesses
                @@ modify_uplus_eliminating_zero
                @@ (i - ((n - ix) * size))
          | _ -> down_tree_cast (DownTreeDirection.from_int i))
      | Adt (name, _args) -> (
          match Tyenv.adt_def ~tyenv name with
          | Struct _ -> (
              let moving_over_field, next_ix =
                if i < 0 then (ix - 1, ix - 1) else (ix, ix + 1)
              in
              if next_ix < 0 then
                (* We can up-tree cast directly since we're at field ix 0 *)
                up_tree_cast UpTreeDirection.Curr accesses rs
              else
                match
                  distance_to_next_field partial_layout moving_over_field
                with
                | Some (Bytes size)
                  when (* Format.printf "Bytes %d `cmp` %d 336;\n" size i; *)
                       size <= abs i ->
                    (if next_ix = Array.length (context.members ty) then
                     up_tree_cast UpTreeDirection.Fwd accesses
                    else fun rs'' -> resolve accesses ty rs'' @@ Some next_ix)
                      (modify_uplus_eliminating_zero (i - (signum i * size)))
                | _ -> down_tree_cast (DownTreeDirection.from_int i))
          | _ -> down_tree_cast (DownTreeDirection.from_int i))
      | _ -> down_tree_cast (DownTreeDirection.from_int i))
  | _ :: _, Some _ -> down_tree_cast DownTreeDirection.Curr
  | _ :: _, _ -> access_error "Stuck handling next op"
  | [], Some ix when ix > 0 ->
      (* print_string "(context.members ty).(ix) 347;\n"; *)
      accesses' ix (context.members ty).(ix)
      (* There's a lot of "crash" cases instead of nicely handled errors, context.members here should instead fail nicely if it's not a struct *)
  | [], _ -> accesses

let rec zero_offset_types (context : context) (ty : Ty.t) : Ty.t list =
  let sub_tree_types () =
    (* print_string "(context.members ty).(0) 355;\n"; *)
    ty :: zero_offset_types context (context.members ty).(0)
  in
  match (context.partial_layouts ty).fields with
  | Arbitrary offsets
    when (* print_string "offsets.(0) 360;\n"; *)
         offsets.(0) = Bytes 0 -> sub_tree_types ()
  | Array (_, _) -> sub_tree_types ()
  | _ -> [ ty ]

let resolve_address ~tyenv ~(context : context) (address : address) :
    access list =
  let reduced = reduce context address.route in
  let accesses = resolve ~tyenv ~context [] address.block_type reduced None in
  let result_type = function
    | a :: _ -> a.index_type
    | _ -> address.block_type
  in
  let r_t_accesses = result_type accesses in
  if Ty.equal r_t_accesses address.address_type then accesses
  else
    let z_o_types = zero_offset_types context r_t_accesses in
    let rec make_pairs_until_fst pred = function
      | x :: (x' :: _ as xs) when not @@ pred x ->
          (x, x') :: make_pairs_until_fst pred xs
      | _ -> []
    in
    let z_o_conversions =
      make_pairs_until_fst (Ty.equal address.address_type) z_o_types
    in
    let as_z_o =
      List.map
        (function
          | against, index_type ->
              { index = 0; index_type; against; variant = None })
        z_o_conversions
    in
    let as' = List.rev_append as_z_o accesses in
    if Ty.equal (result_type as') address.address_type then as'
    else
      raise
        (AccessError
           ( as',
             [],
             result_type as',
             Some 0,
             Format.sprintf "Could not resolve to correct address type" ))

let resolve_address_debug_access_error
    ~tyenv
    ~(context : context)
    (address : address) : access list =
  try resolve_address ~tyenv ~context address
  with AccessError (accesses, rs, ty, ix, message) ->
    Format.eprintf "%s: \n" message;
    Format.eprintf "\tty=%a\n\tix=%s\n\trs=[" Ty.pp ty
    @@ Option.fold ~none:"- (None)" ~some:Int.to_string ix;
    List.iter (Format.eprintf "%a;\n" Projections.pp_op) rs;
    Format.eprintf "]\n\taccesses=[";
    List.iter (Format.eprintf "%a;\n" pp_access) accesses;
    Format.eprintf "]\n";
    []

(* We return align not size as it's easier to convert this to a size than the reverse *)
let align_scalar_ty : Ty.scalar_ty -> Partial_align.t = function
  | Ty.Bool -> ExactlyPow2 0
  | Ty.Char -> ExactlyPow2 2
  | Ty.Int Ty.Isize -> AtLeastPow2 0
  | Ty.Int Ty.I8 -> ExactlyPow2 0
  | Ty.Int Ty.I16 -> ExactlyPow2 1
  | Ty.Int Ty.I32 -> ExactlyPow2 2
  | Ty.Int Ty.I64 -> ExactlyPow2 3
  | Ty.Int Ty.I128 -> ExactlyPow2 4
  | Ty.Uint Ty.Usize -> AtLeastPow2 0
  | Ty.Uint Ty.U8 -> ExactlyPow2 0
  | Ty.Uint Ty.U16 -> ExactlyPow2 1
  | Ty.Uint Ty.U32 -> ExactlyPow2 2
  | Ty.Uint Ty.U64 -> ExactlyPow2 3
  | Ty.Uint Ty.U128 -> ExactlyPow2 4

(* Easy way of forcing a correct alignment when a type is required *)
let aligned_zst (align : Partial_align.t) =
  ( Ty.Tuple [],
    { fields = Arbitrary [||]; variant = Single 0; align; size = Exactly 0 } )

let rec end_offset
    (partial_layouts : Ty.t -> partial_layout)
    (ty : Ty.t)
    (pl : partial_layout) =
  match (pl.fields, ty) with
  | Arbitrary offsets, _ -> offsets.(Array.length offsets - 1)
  | Array (_, _), Ty.Array { ty = ty_elem; length } -> (
      match end_offset partial_layouts ty_elem (partial_layouts ty_elem) with
      | Bytes n -> Bytes (n * length)
      | FromCount (ty', n, 0) -> FromCount (ty', n * length, 0)
      | _ -> FromCount (ty_elem, length, 0))
  | Primitive, Ty.Scalar s -> (
      match Partial_size.from_alignment @@ align_scalar_ty s with
      | Partial_size.Exactly n -> Bytes n
      | Partial_size.AtLeast _ -> FromCount (ty, 1, 0))
  | _, _ -> FromCount (ty, 1, 0)

let next_offset
    (partial_layouts : Ty.t -> partial_layout)
    (ix, curr_offset)
    ((ty, pl), (ty_next, pl_next)) =
  (* Format.printf
     "ty=%a ty_next=%a curr_offset=%a end_offset=%a pl_next.align=%a 482;\n"
     Ty.pp ty Ty.pp ty_next pp_offset curr_offset pp_offset
     (end_offset partial_layouts ty pl)
     Partial_align.pp pl_next.align; *)
  let ix' = ix + 1 in
  ( ix',
    match (curr_offset, end_offset partial_layouts ty pl, pl_next.align) with
    | Bytes b, Bytes b', ExactlyPow2 pow -> Bytes (align pow @@ (b + b'))
    | Bytes 0, FromCount (ty', n, b'), ExactlyPow2 0 -> FromCount (ty', n, b')
    | Bytes 0, _, ExactlyPow2 0 -> FromCount (ty, 1, 0)
    | Bytes 0, FromCount (ty', n, 0), ToType ty'' when Ty.equal ty' ty'' ->
        FromCount (ty', n, 0)
    | Bytes 0, _, _ when ty = ty_next -> FromCount (ty, 1, 0)
    | Bytes 0, Bytes 1, ToType ty' -> FromCount (ty', 1, 0)
    | FromCount (ty', n, b), Bytes sz, ExactlyPow2 0 ->
        FromCount (ty', n, b + sz)
    | FromCount (ty', n, 0), FromCount (ty'', n', b), ExactlyPow2 0
      when Ty.equal ty' ty'' -> FromCount (ty', n + n', b)
    | FromCount (ty', n, 0), FromCount (ty'', n', 0), ToType ty'''
      when Ty.equal ty' ty'' && Ty.equal ty' ty''' -> FromCount (ty', n + n', 0)
    | FromCount (ty', n, 0), _, ExactlyPow2 0 when Ty.equal ty ty' ->
        FromCount (ty', n + 1, 0)
    | FromCount (ty', n, 0), _, ToType ty''
      when Ty.equal ty ty' && Ty.equal ty'' ty' -> FromCount (ty', n + 1, 0)
    | FromCount (ty', n, 0), _, _ when Ty.equal ty ty' && Ty.equal ty_next ty'
      -> FromCount (ty', n + 1, 0)
    | FromIndex (ix_from, b), Bytes sz, (ExactlyPow2 pow as a)
      when Partial_align.strictly_le a pl.align ->
        FromIndex (ix_from, align pow @@ (b + sz))
    | _ -> FromIndex (ix', 0) )

let offsets_from_tys_and_pls
    (partial_layouts : Ty.t -> partial_layout)
    (tys : Ty.t Seq.t)
    (pls : partial_layout Seq.t) : offset array =
  let end_offset =
    aligned_zst @@ Partial_align.maximum @@ Seq.map (fun pl -> pl.align) pls
  in
  let tys_pls = Seq.zip tys pls in
  Array.of_seq
  @@ Seq.map (fun (_, o) -> o)
  @@ Seq.scan (next_offset partial_layouts) (0, Bytes 0)
  @@ Seq.zip tys_pls
       (Seq.append (Seq.drop 1 tys_pls) @@ List.to_seq [ end_offset ])

let rec partial_layout_of
    (tyenv : Tyenv.t)
    (known : (string * Ty.t list, partial_layout) Hashtbl.t) :
    Ty.t -> partial_layout = function
  | Ty.Array { length; ty } ->
      let pl_ty = partial_layout_of tyenv known ty in
      {
        fields = Array (pl_ty.size, length);
        variant = Single 0;
        align = pl_ty.align;
        size = Partial_size.map (fun x -> x * length) pl_ty.size;
      }
  | Ty.Scalar scalar_ty ->
      let align = align_scalar_ty scalar_ty in
      {
        fields = Primitive;
        variant = Single 0;
        align;
        size = Partial_size.from_alignment align;
      }
  | Ty.Tuple [] ->
      let offsets = [| Bytes 0 |] in
      {
        fields = Arbitrary offsets;
        variant = Single 0;
        align = ExactlyPow2 0;
        size = Exactly 0;
      }
  | Ty.Tuple ts as ty ->
      let offsets =
        Array.init (List.length ts + 1) (fun i -> FromIndex (i, 0))
      in
      {
        fields = Arbitrary offsets;
        variant = Single 0;
        align = ToType ty;
        (* This is suboptimal, but comes around from the model error. Structs/enums are not types *)
        size = AtLeast 0;
      }
  | Ty.Adt (name, subst) as this_ty -> (
      match Hashtbl.find_opt known (name, subst) with
      | Some layout -> layout
      | None ->
          let partial_layout =
            match Tyenv.adt_def ~tyenv name with
            | Adt_def.Struct (ReprC, fs) ->
                let ts =
                  Seq.map (fun (_, t) -> Ty.subst_params ~subst t)
                  @@ List.to_seq fs
                in
                let pls = Seq.map (partial_layout_of tyenv known) ts in
                let align =
                  Partial_align.maximum @@ Seq.map (fun pl -> pl.align) pls
                in
                let offsets =
                  offsets_from_tys_and_pls
                    (partial_layout_of tyenv known)
                    ts pls
                in
                let size =
                  (* print_string "offsets.(Array.length offsets - 1) 521;\n"; *)
                  match offsets.(Array.length offsets - 1) with
                  | Bytes n -> Partial_size.Exactly n
                  | _ ->
                      Partial_size.align_to align
                      @@ Partial_size.sum
                      @@ Seq.map (fun pl -> pl.size) pls
                in
                { fields = Arbitrary offsets; variant = Single 0; align; size }
            | Struct (ReprRust, fs) ->
                let offsets =
                  Array.init (List.length fs + 1) (fun i -> FromIndex (i, 0))
                in
                {
                  fields = Arbitrary offsets;
                  variant = Single 0;
                  align = ToType this_ty;
                  size = AtLeast 0;
                }
            | Enum variants ->
                (* Check how RustC actually uses Enum offsets (not variant offsets). We're not using this so it's fine *)
                let offsets = [||] in
                {
                  fields = Arbitrary offsets;
                  variant =
                    Multiple
                      {
                        tag = None;
                        (* No tag type since we're not handling ReprC enums yet *)
                        variants =
                          Array.of_seq
                          @@ Seq.map (fun (_, fs) ->
                                 let fs =
                                   List.map (Ty.subst_params ~subst) fs
                                 in
                                 partial_layout_of tyenv known @@ Ty.Tuple fs)
                          @@ List.to_seq variants;
                      };
                  align = AtLeastPow2 0;
                  size = AtLeast 0;
                }
          in
          Hashtbl.add known (name, subst) partial_layout;
          partial_layout)
  | Ty.Ref { mut = _; ty = _ } ->
      (* We could gain more information if we deduced it was an unsized type, however, this is fine without it since we use bounds not exact sizes *)
      {
        fields = Primitive;
        variant = Single 0;
        align = AtLeastPow2 0;
        size = AtLeast 1;
      }
  | Ty.Slice _ ->
      (* FIXME: Is this a slice or slice reference; assumed slice reference (Matthew) *)
      (* This is an actual slice. We have them in memory because our memories are partial,
         and therefore can contain slices of arrays.
         I'm suspecting that it therefore shouldn't really be a slice, it's still an array *)
      {
        fields = Primitive;
        variant = Single 0;
        align = AtLeastPow2 0;
        size = AtLeast 2;
      }
  | Ty.Unresolved _ ->
      (* FIXME: This should really be attempting to resolve the type.
         As of right now, it is NOT unsound, but it IS over-approximating *)
      {
        fields = Primitive;
        variant = Single 0;
        align = AtLeastPow2 0;
        size = AtLeast 0;
      }

let partial_layouts_from_env (tyenv : Tyenv.t) : Ty.t -> partial_layout =
  let partial_layouts = Hashtbl.create 1024 in
  partial_layout_of tyenv partial_layouts

let enum_variant_members_from_env (tyenv : Tyenv.t) (ty : Ty.t) (vidx : int) =
  match ty with
  | Adt (name, subst) -> (
      match Tyenv.adt_def ~tyenv name with
      | Enum variants ->
          List.nth variants vidx |> snd
          |> List.map (Ty.subst_params ~subst)
          |> Array.of_list
      | _ -> failwith "enum_variant_members for non-enum")
  | _ -> failwith "enum_variant_members for non-enum"

let members_from_env (tyenv : Tyenv.t) (ty : Ty.t) : Ty.t array =
  match ty with
  | Array { ty; length } -> Array.make length ty
  | Tuple tys -> Array.of_list tys
  | Adt (name, subst) -> (
      match Tyenv.adt_def ~tyenv name with
      | Struct (_, fs) ->
          List.to_seq fs
          |> Seq.map (fun (_, t) -> Ty.subst_params ~subst t)
          |> Array.of_seq
      | _ -> [||])
  | _ -> [||]
(* Consider making 1 t for internal navigation, especially primitives *)

let context_from_env (tyenv : Tyenv.t) : context =
  {
    partial_layouts = partial_layouts_from_env tyenv;
    members = members_from_env tyenv;
    variant_members = enum_variant_members_from_env tyenv;
  }
