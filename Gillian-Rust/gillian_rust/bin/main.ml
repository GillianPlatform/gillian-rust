open Gillian_rust

module CLI =
  Gillian.CommandLine.Make (Gillian.General.Init_data.Dummy) (C_memory)
    (S_memory)
    (Gillian.General.External.Dummy)
    (Parser_and_compiler)
    (struct
      let runners : Gillian.Bulk.Runner.t list = [ (module C_runner) ]
    end)
    (Gillian.Debugger.Gil_to_tl_lifter.Default (S_memory) (Parser_and_compiler))

let () = CLI.main ()
