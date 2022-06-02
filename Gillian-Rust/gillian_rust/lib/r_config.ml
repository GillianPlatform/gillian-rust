let compiler_root = ref ".."

let in_compiler_root (work : unit -> 'a) : 'a =
  let dir_before = Sys.getcwd () in
  let () = Sys.chdir !compiler_root in
  Fun.protect ~finally:(fun () -> Sys.chdir dir_before) work
