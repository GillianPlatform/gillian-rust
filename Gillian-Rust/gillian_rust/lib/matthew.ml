open Projections

type variant_idx = int
type size = { size : int }
type partial_size = Exactly of size | AtLeast of size
type partial_align = ExactlyPow2 of int | AtLeastPow2 of int
type align = { pow2 : int }
type wrapping_range = { start : int; finish : int }
type base_integer = I8 | I16 | I32 | I64 | I128
type primative = Int of base_integer * bool | F32 | F64 | Pointer
type scalar = { primative : primative; valid_range : wrapping_range }

type offset =
  | Bytes     of size
  | FromIndex of int * size
  | FromCount of Rust_types.t * int * size

type fields_shape =
  | Primative
  | Union     of int
  | Array     of size option * int
  (* offset array includes the offset of the end *)
  | Arbitrary of offset array

type variants =
  | Single   of variant_idx
  | Multiple of scalar option * partial_layout array

and partial_layout = {
  fields : fields_shape;
  variant : variants;
  align : partial_align;
  size : partial_size;
}

type context = {
  partial_layouts : Rust_types.t -> partial_layout;
  members : Rust_types.t -> Rust_types.t array;
}

let rec contextualise (context : context) (route : op list) : op list =
  match route with
  | Plus (w, i, t) :: rs -> (
      match (context.partial_layouts t).size with
      | Exactly sz -> UPlus (w, sz.size * i) :: contextualise context rs
      | _          -> Plus (w, i, t) :: contextualise context rs)
  | Index (i, t, n) :: rs when i < n ->
      Cast (Rust_types.Array { length = n; ty = t }, t)
      :: contextualise context rs
  | Field (i, t) :: rs -> (
      let t' = (context.members t).(i) and rs' = contextualise context rs in
      match (context.partial_layouts t).fields with
      | Arbitrary os -> (
          match os.(i) with
          | Bytes n                -> Cast (t, t')
                                      :: UPlus (Overflow, n.size)
                                      :: rs'
          | FromIndex (i', n)      ->
              Field (i', t)
              :: Cast ((context.members t).(i'), t')
              :: UPlus (Overflow, n.size)
              :: rs'
          | FromCount (t'', n, n') ->
              Cast (t, t'')
              :: Plus (Overflow, n, t'')
              :: Cast (t'', t')
              :: UPlus (Overflow, n'.size)
              :: rs')
      | _            -> Field (i, t) :: contextualise context rs)
  | r :: rs -> r :: contextualise context rs
  | [] -> []

let rec cons_all ys xs =
  match ys with y :: ys' -> cons_all ys' (y :: xs) | [] -> xs

let reorder : op list -> op list =
  let rec reorder' upluss rs =
    match rs with
    | (UPlus (_, _) as r) :: rs -> reorder' (r :: upluss) rs
    | (Cast (_, _) as r) :: rs  -> r :: reorder' upluss rs
    | r :: rs                   -> cons_all upluss (r :: reorder' upluss rs)
    | []                        -> []
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
    when i * i' > 0 && t = t' ->
      simplify (Plus (Overflow, i + i, t) :: rs)
  | UPlus (Overflow, i) :: UPlus (Overflow, i') :: rs when i * i' > 0 ->
      simplify (UPlus (Overflow, i + i) :: rs)
  | Cast (t, t'') :: Cast (t''', t') :: rs when t'' = t''' ->
      simplify (Cast (t, t') :: rs)
  (* We also have to handle 0s if they're at the front, from other rules or as the last element *)
  | Plus (_, 0, _) :: rs -> simplify rs
  | UPlus (_, 0) :: rs -> simplify rs
  | Cast (t, t') :: rs when t = t' -> simplify rs
  | r :: rs -> r :: simplify rs
  | [] -> []

let reduce context rs = simplify @@ reorder @@ contextualise context rs

type address = {
  block : int;
  block_type : Rust_types.t;
  route : op list;
  address_type : Rust_types.t;
}

type access = { index : int; index_type : Rust_types.t; against : Rust_types.t }

let distance_to_next_field (partial_layout : partial_layout) (a : int) =
  match partial_layout.fields with
  | Arbitrary offsets when a >= 0 && a + 1 < Array.length offsets -> (
      match (offsets.(a), offsets.(a + 1)) with
      | Bytes n, Bytes n' -> Some (Bytes { size = n'.size - n.size })
      | FromIndex (n, b), FromIndex (n', b') when n = n' ->
          Some (Bytes { size = b'.size - b.size })
      | FromCount (t, n, b), FromCount (t', n', b') when t = t' ->
          let b'' = { size = b'.size - b.size } in
          Some (if n' == n then Bytes b'' else FromCount (t, n' - n, b''))
      | _, _ -> None)
  | _ -> None

exception
  AccessError of access list * op list * Rust_types.t * int option * string

let resolve_address (_context : context) (_address : address) : access list = []

module UpTreeDirection = struct
  type t = Curr | Fwd

  let magnitude = function Curr -> 0 | Fwd -> 1
end

module DownTreeDirection = struct
  type t = Bkwd | Curr

  let from_int i = if i < 0 then Bkwd else Curr
  let magnitude = function Bkwd -> -1 | Curr -> 0
end

(* Divide rounding towards -signum(m) * inf *)
let div' (n : int) (m : int) = (n / m) - if n * m < 0 then 1 else 0

let mod' (n : int) (m : int) =
  let res = n mod m in
  if res < 0 then res + m else res

let signum (n : int) = if n < 0 then -1 else if n = 0 then 0 else 1

let rec resolve (context : context) (accesses : access list) (ty : Rust_types.t)
    (rs : op list) (index : int option) : access list =
  let access_error message =
    raise (AccessError (accesses, rs, ty, index, message))
  and ix =
    if Option.is_some index then index
    else
      match (context.partial_layouts ty).fields with
      | Arbitrary offsets when offsets.(0) = Bytes { size = 0 } -> Some 0
      | _ -> None
  and accesses' index index_type =
    { index; index_type; against = ty } :: accesses
  in
  let down_tree_cast (dir : DownTreeDirection.t) =
    match ix with
    | Some ix ->
        let ix' = ix + DownTreeDirection.magnitude dir in
        let ix'_type = (context.members ty).(ix') in
        let casted_ix =
          match dir with
          | DownTreeDirection.Bkwd -> Array.length (context.members ix'_type)
          | DownTreeDirection.Curr -> 0
        in
        resolve context (accesses' ix' ix'_type) ix'_type rs (Some casted_ix)
    | None    -> access_error "Can't down-tree cast from no known index"
  in
  let rec up_tree_cast dir accesses' rs' =
    match accesses' with
    (* We're not checking whether the type cast to is meant to have indices, but this should be fine as it won't be able to progress once there *)
    | { index; index_type = _; against } :: as' ->
        let max_ix = Array.length (context.members against)
        and ix' = index + UpTreeDirection.magnitude dir in
        if ix' <= max_ix then resolve context as' against rs' (Some ix')
        else up_tree_cast dir as' rs'
    | [] ->
        access_error "Could not up tree cast from beyond top of access stack"
  in

  match (rs, ix) with
  | Field (i, t) :: rs', None when t = ty ->
      let t' = (context.members t).(i) in
      resolve context (accesses' i t') t rs' None
  (* TODO handle invalid indices etc. *)
  | Field (i, t) :: rs', Some 0 when t = ty ->
      resolve context accesses ty rs' (Some i)
  | Index (i, t, n) :: rs', Some ix
    when i < n && Rust_types.Array { length = n; ty = t } = ty ->
      resolve context accesses ty rs' (Some (i + ix))
  | Downcast (i, t) :: rs', None when t = ty ->
      let t' = (context.members t).(i) in
      resolve context (accesses' i t') t rs' None
  | Cast (_, _) :: rs', ix -> resolve context accesses ty rs' ix
  | Plus (_, 0, _) :: _, _ ->
      access_error "Invalid +^t 0 should not exist at resolution stage"
  | Plus (w, i, t) :: rs', Some ix -> (
      let i' = i + ix
      and modify_plus_eliminating_zero new_i =
        if new_i = 0 then rs' else Plus (w, new_i, t) :: rs'
      and partial_layout = context.partial_layouts ty in
      match ty with
      | Rust_types.Array { ty = tElem; length = n } when tElem = t ->
          if i' < 0 then
            up_tree_cast UpTreeDirection.Curr accesses
              (modify_plus_eliminating_zero i')
          else if i' < n then resolve context accesses ty rs' (Some (i' - n))
          else
            up_tree_cast UpTreeDirection.Fwd accesses
              (modify_plus_eliminating_zero i')
      | Rust_types.Named _ -> (
          let moving_over_field, next_i, next_ix =
            if i < 0 then (ix - 1, i + 1, ix - 1) else (ix, i - 1, ix + 1)
          and members = context.members ty in
          if i < 0 && ix = 0 then
            (* We can up-tree cast directly since we're at field ix 0 *)
            up_tree_cast UpTreeDirection.Curr accesses rs
          else
            match distance_to_next_field partial_layout moving_over_field with
            | Some (FromCount (t', _, { size = 0 })) when t' = t ->
                (if next_ix = Array.length members then
                 up_tree_cast UpTreeDirection.Fwd accesses
                else fun rs'' ->
                  resolve context accesses ty rs'' @@ Some next_ix)
                  (modify_plus_eliminating_zero next_i)
            | _ -> down_tree_cast (DownTreeDirection.from_int i))
      | _ -> down_tree_cast (DownTreeDirection.from_int i))
  | UPlus (_, 0) :: _, _ ->
      access_error "Invalid +^U 0 should not exist at resolution stage"
  | UPlus (w, i) :: rs', Some ix -> (
      let modify_uplus_eliminating_zero new_i =
        if new_i = 0 then rs' else UPlus (w, new_i) :: rs'
      and partial_layout = context.partial_layouts ty in
      match ty with
      | Rust_types.Array { ty = tElem; length = n } -> (
          match (context.partial_layouts tElem).size with
          | Exactly { size } ->
              let ix' = ix + div' i size and rem = mod' i size in
              if ix' < 0 then
                up_tree_cast UpTreeDirection.Curr accesses
                @@ modify_uplus_eliminating_zero
                @@ ((ix * size) + i)
                (* We must only handle cases where we can make progress at this level, otherwise down_tree_cast *)
              else if ix' = ix then
                down_tree_cast (DownTreeDirection.from_int i)
              else if ix' < n then
                resolve context accesses ty
                  (modify_uplus_eliminating_zero rem)
                  (Some ix')
              else
                up_tree_cast UpTreeDirection.Fwd accesses
                @@ modify_uplus_eliminating_zero
                @@ (i - ((n - ix) * size))
          | _                -> down_tree_cast (DownTreeDirection.from_int i))
      | Rust_types.Named _ -> (
          let moving_over_field, next_ix =
            if i < 0 then (ix - 1, ix - 1) else (ix, ix + 1)
          and members = context.members ty in
          if i < 0 && ix = 0 then
            (* We can up-tree cast directly since we're at field ix 0 *)
            up_tree_cast UpTreeDirection.Curr accesses rs
          else
            match distance_to_next_field partial_layout moving_over_field with
            | Some (Bytes { size }) when size >= abs i ->
                (if next_ix = Array.length members then
                 up_tree_cast UpTreeDirection.Fwd accesses
                else fun rs'' ->
                  resolve context accesses ty rs'' @@ Some next_ix)
                  (modify_uplus_eliminating_zero (i - (signum i * size)))
            | _ -> down_tree_cast (DownTreeDirection.from_int i))
      | _ -> down_tree_cast (DownTreeDirection.from_int i))
  | _ :: _, Some _ -> down_tree_cast DownTreeDirection.Curr
  | _ :: _, _ -> access_error "Stuck handling next op"
  | [], Some ix when ix > 0 ->
      accesses' ix (context.members ty).(ix)
      (* There's a lot of "crash" cases instead of nicely handled errors, context.members here should instead fail nicely if it's not a struct *)
  | [], _ -> accesses