open Gillian_rust

module CLI =
  Gillian.CommandLine.Make (C_memory) (S_memory)
    (Gillian.General.External.Dummy)
    (Gillian.CommandLine.ParserAndCompiler.Dummy)
    (struct
      let runners = []
    end)

let () = CLI.main ()
