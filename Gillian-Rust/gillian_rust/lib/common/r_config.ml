let compiler_root = ref ".."
let deps = "target/debug/deps"

let in_compiler_root (work : unit -> 'a) : 'a =
  let dir_before = Sys.getcwd () in
  let () = Sys.chdir !compiler_root in
  Fun.protect ~finally:(fun () -> Sys.chdir dir_before) work

let expand_and_stop = ref false
let exec_mode = ref Gillian.Utils.Exec_mode.Verification

let exec_mode_arg () =
  let arg_header = "--gillian-exec-mode=" in
  let mode =
    match !exec_mode with
    | Concrete -> "concrete"
    | Symbolic -> "symbolic"
    | Verification -> "verification"
    | BiAbduction -> "act"
  in
  arg_header ^ mode

let prophecy_mode = ref false
let prophecy_mode_arg () = if !prophecy_mode then "--gillian-prophecies" else ""
