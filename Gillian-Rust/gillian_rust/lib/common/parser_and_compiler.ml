open Gillian
open IncrementalAnalysis
open ParserAndCompiler
module Annot = Gil_syntax.Annot.Basic

module TargetLangOptions = struct
  open Cmdliner

  type t = {
    compiler_root : string option;
    expand_and_stop : bool;
    prophecies : bool;
  }

  let term =
    let docs = Manpage.s_common_options in

    let docv = "DIR" in
    let doc = "Invoke command $(docv)" in
    let compiler_root =
      Arg.(value & opt (some string) None & info [ "c" ] ~docs ~docv ~doc)
    in

    let doc = "Expand macros and stop" in
    let expand_and_stop =
      Arg.(value & flag & info [ "expand-and-stop" ] ~docs ~doc)
    in

    let doc = "Use Gillian-Rust in prophecy mode (RustHornBelt style)" in
    let prophecies = Arg.(value & flag & info [ "prophecies" ] ~docs ~doc) in
    let opt compiler_root expand_and_stop prophecies =
      { compiler_root; expand_and_stop; prophecies }
    in
    Term.(const opt $ compiler_root $ expand_and_stop $ prophecies)

  let apply { compiler_root; expand_and_stop; prophecies } =
    Option.iter (fun c -> R_config.compiler_root := c) compiler_root;
    R_config.expand_and_stop := expand_and_stop;
    R_config.prophecy_mode := prophecies
end

type init_data = Tyenv.t
type err = unit
type tl_ast = unit (* We unfortunately don't have access to the tl ast *)

let pp_err = Fmt.nop
let other_imports = []
let default_import_paths = Some Runtime.Sites.runtime

let initialize exec_mode =
  R_config.exec_mode := exec_mode;
  Gillian.Utils.Config.lemma_proof := false

let resolve_gilogic () = "target/debug/libgilogic.rlib"
let resolve_creusillian () = "target/debug/libcreusillian.dylib"

let options ~out_dir () =
  [
    "--out-dir";
    out_dir;
    "-L";
    "dependency=" ^ R_config.deps;
    "--extern";
    "gilogic=" ^ resolve_gilogic ();
    "--extern";
    "creusillian=" ^ resolve_creusillian ();
    "-Zcrate-attr='feature(register_tool)'";
    "-Zcrate-attr='register_tool(gillian)'";
    "-Zcrate-attr='feature(rustc_attrs)'";
    "-Zcrate-attr='allow(internal_features)'";
    "-Zcrate-attr='feature(stmt_expr_attributes)'";
  ]

let env () = [ R_config.exec_mode_arg (); R_config.prophecy_mode_arg () ]

module Parsing = Gil_parsing.Make (Annot)

let compile ~out_dir file =
  let ( let* ) = Result.bind in
  let no_ext = Filename.chop_extension (Filename.basename file) in
  let pp_opts = Fmt.(list ~sep:(any " ") string) in
  let options = options ~out_dir () in
  let out_file = Filename.concat out_dir (no_ext ^ ".gil") in

  let* () =
    if String.equal (Filename.extension file) ".stdout" then
      let exit_code = Sys.command (Fmt.str "cp %s %s" file out_file) in
      match exit_code with
      | 0 -> Ok ()
      | _ -> Error ()
    else
      let command =
        Fmt.str "%a cargo run -- %s %a" pp_opts (env ()) file pp_opts options
      in
      Logging.normal (fun m -> m "%s" command);
      let exit_code =
        R_config.in_compiler_root (fun () -> Sys.command command)
      in
      match exit_code with
      | 0 -> Ok ()
      | _ -> Error ()
  in
  Ok out_file

let expand_and_stop ~out_dir file =
  let pp_opts = Fmt.(list ~sep:(any " ") string) in
  let command =
    Fmt.str "cargo run -- %s %a -Zunpretty=expanded" file pp_opts
      (options ~out_dir ())
  in
  ignore @@ R_config.in_compiler_root (fun () -> Sys.command command);
  exit 0

let parse_and_compile_files files =
  let ( let* ) = Result.bind in
  let file =
    match files with
    | [ f ] -> Unix.realpath f
    | _ -> failwith "More than one file for Gillian-Rust"
  in
  let source_files = SourceFiles.make () in
  let () = SourceFiles.add_source_file source_files ~path:file in
  let temp_dir = Filename.get_temp_dir_name () in
  if !R_config.expand_and_stop then expand_and_stop ~out_dir:temp_dir file;
  let* out_file = compile ~out_dir:temp_dir file in
  let gil_prog = Parsing.parse_eprog_from_file out_file in
  let init_data = Tyenv.of_yojson gil_prog.init_data |> Result.get_ok in
  let gil_file = Filename.chop_extension file ^ ".gil" in
  Ok
    {
      gil_progs = [ (gil_file, gil_prog.labeled_prog) ];
      source_files;
      tl_ast = ();
      init_data;
    }
