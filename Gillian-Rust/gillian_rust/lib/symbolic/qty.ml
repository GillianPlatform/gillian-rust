type t = Partially | Totally [@@deriving yojson, show]

let pp ft =
  let open Fmt in
  function
  | Totally -> string ft "Totally"
  | Partially -> string ft "Partially"
