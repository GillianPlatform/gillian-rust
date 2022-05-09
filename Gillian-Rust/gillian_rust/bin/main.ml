open Gillian_rust

module CLI =
  Gillian.CommandLine.Make (C_memory) (S_memory)
    (Gillian.General.External.Dummy)
    (Gillian.CommandLine.ParserAndCompiler.Dummy)
    (struct
      let runners = []
    end)
    (Gillian.Debugger.Gil_to_tl_lifter.Default
       (S_memory)
       (Gillian.CommandLine.ParserAndCompiler.Dummy))

let () = CLI.main ()
