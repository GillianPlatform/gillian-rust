let compiler_root = ref ".."
let deps = "target/debug/deps"

let in_compiler_root (work : unit -> 'a) : 'a =
  let dir_before = Sys.getcwd () in
  let () = Sys.chdir !compiler_root in
  Fun.protect ~finally:(fun () -> Sys.chdir dir_before) work
