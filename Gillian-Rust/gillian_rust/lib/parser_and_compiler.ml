open Gillian
open IncrementalAnalysis
open ParserAndCompiler

module TargetLangOptions = struct
  open Cmdliner

  type t = { compiler_root : string option }

  let term =
    let docs = Manpage.s_common_options in
    let docv = "DIR" in
    let doc = "Invoke command $(docv)" in
    let compiler_root =
      Arg.(value & opt (some string) None & info [ "-c" ] ~docs ~docv ~doc)
    in
    let opt compiler_root = { compiler_root } in
    Term.(const opt $ compiler_root)

  let apply { compiler_root } =
    Option.iter (fun c -> R_config.compiler_root := c) compiler_root
end

type init_data = Tyenv.t
type err = unit
type tl_ast = unit (* We unfortunately don't have access to the tl ast *)

let pp_err = Fmt.nop
let other_imports = []
let env_var_import_path = Some "GILLIAN_RUST_RUNTIME_PATH"
let initialize _ = ()
let resolve_gilogic () = "target/debug/libgilogic.rlib"

let options ~out_dir () =
  [
    "--out-dir";
    out_dir;
    "-L";
    "dependency=" ^ R_config.deps;
    "--extern";
    "gilogic=" ^ resolve_gilogic ();
    "-Zcrate-attr='feature(register_tool)'";
    "-Zcrate-attr='register_tool(gillian)'";
    "-Zcrate-attr='feature(rustc_attrs)'";
  ]

let compile ~out_dir file =
  let ( let* ) = Result.bind in
  let gilogic = resolve_gilogic () in
  let () = Fmt.pr "\n\nRESOLVED GILOGIC AT: %s\n@?" gilogic in
  let no_ext = Filename.chop_extension (Filename.basename file) in
  let pp_opts = Fmt.(list ~sep:(any " ") string) in
  let options = options ~out_dir () in
  let command = Fmt.str "cargo run -- %s %a" file pp_opts options in
  Logging.normal (fun m -> m "%s" command);
  let exit_code = R_config.in_compiler_root (fun () -> Sys.command command) in
  let* () =
    match exit_code with
    | 0 -> Ok ()
    | _ -> Error ()
  in
  let out_file = Filename.concat out_dir (no_ext ^ ".gil") in
  Ok out_file

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
  let* out_file = compile ~out_dir:temp_dir file in
  let gil_prog = Gillian.Gil_parsing.parse_eprog_from_file out_file in
  let init_data = Tyenv.of_yojson gil_prog.init_data |> Result.get_ok in
  Ok
    {
      gil_progs = [ (file, gil_prog.labeled_prog) ];
      source_files;
      tl_ast = ();
      init_data;
    }
