open Gillian
open Gil_syntax

module Outcome =
  Bulk.Outcome.Make_Concrete (C_memory) (Parser_and_compiler)
    (General.External.Dummy)

module Suite = struct
  include Bulk.Suite.ByFolder (struct
    let max_depth = 0
    let cmd_name = "bulk-exec"
    let exec_mode = Gillian.Utils.ExecMode.Concrete
  end)

  let filter_source s = String.equal (Filename.extension s) ".rs"
  let beforeEach () = beforeEach ()
end

module Expectations = struct
  type matcher = Alcotest_runner.AlcotestCheckers.Make(Outcome).matcher
  type outcome = Outcome.t
  type category = Suite.category
  type info = Suite.info

  let rec concretize e =
    let open Expr in
    match e with
    | Lit l -> l
    | EList l -> LList (List.map concretize l)
    | _ ->
        failwith (Format.asprintf "%a should be concrete but isn't" Expr.pp e)

  let expected_outcome filename =
    let o = open_in filename in
    let find line =
      let to_find = Str.regexp_string "ENDSWITH: " in
      try Some (Str.search_forward to_find line 0) with Not_found -> None
    in
    let str =
      Fun.protect
        ~finally:(fun () -> close_in o)
        (fun () ->
          let continue = ref true in
          let ret = ref "" in
          while !continue do
            try
              let line = input_line o in
              match find line with
              | Some i ->
                  let () = continue := false in
                  ret := String.sub line (i + 10) (String.length line - i - 10)
              | None -> ()
            with End_of_file ->
              failwith "Expected outcome not written in file"
          done;
          !ret)
    in
    Printf.printf "The string: %s" str;
    Gil_parsing.parse_expression (Lexing.from_string (String.trim str))
    |> concretize

  let has_expected_return filename ret _ =
    let exp = expected_outcome filename in
    Format.printf "Expected: %a, Got: %a" Literal.pp exp Literal.pp ret;
    Literal.equal exp ret

  let expectation (expect : matcher) (test : ('a, 'b) Bulk.Test.t) outcome =
    expect.finish_in_normal_mode_with ExactlyOne
      ~constraint_name:"Returning expected value"
      (has_expected_return test.path)
      outcome
end

include Alcotest_runner.AlcotestRunner.Make (Outcome) (Suite) (Expectations)
