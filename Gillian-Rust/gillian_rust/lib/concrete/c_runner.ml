open Gillian
open Gil_syntax
module Gil_parsing = Gil_parsing.Make (Parser_and_compiler.Annot)

module Outcome =
  Bulk.Outcome.Make_Concrete (C_memory) (Parser_and_compiler)
    (General.External.Dummy (Parser_and_compiler.Annot))

module Suite = struct
  include Bulk.Suite.ByFolder (struct
    let max_depth = 5
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

  type expected_outcome = Ends_with of Literal.t | Fails

  let expected_outcome filename =
    let o = open_in filename in
    let find line =
      let to_find_succ = Str.regexp_string "ENDSWITH: " in
      let to_find_fail = Str.regexp_string "SHOULDBEFAILING" in
      try Some (Either.Left (Str.search_forward to_find_succ line 0))
      with Not_found -> (
        try Some (Right (Str.search_forward to_find_fail line 0))
        with Not_found -> None)
    in
    Fun.protect
      ~finally:(fun () -> close_in o)
      (fun () ->
        let continue = ref true in
        let ret = ref Fails in
        while !continue do
          try
            let line = input_line o in
            match find line with
            | Some (Left i) ->
                let to_parse =
                  String.sub line (i + 10) (String.length line - i - 10)
                in
                let expr =
                  Gil_parsing.parse_expression
                    (Lexing.from_string (String.trim to_parse))
                in
                let () = ret := Ends_with (concretize expr) in
                continue := false
            | Some (Right _) -> continue := false
            | None -> ()
          with End_of_file -> failwith "Expected outcome not written in file"
        done;
        !ret)

  let expectation (expect : matcher) (test : ('a, 'b) Bulk.Test.t) outcome =
    match expected_outcome test.path with
    | Fails -> failwith "unhandled failing tests for now"
    | Ends_with l ->
        expect.finish_in_normal_mode_with ExactlyOne
          ~constraint_name:"Returning expected value"
          (fun ret _ -> Literal.equal ret l)
          outcome
end

include Alcotest_runner.AlcotestRunner.Make (Outcome) (Suite) (Expectations)
