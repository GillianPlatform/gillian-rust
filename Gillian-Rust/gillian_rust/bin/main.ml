open Gillian_rust
module S_memory = Gillian.Monadic.MonadicSMemory.Lift (S_memory)

module Gil_to_rust_lifter
    (Verification : Gillian.Abstraction.Verifier.S
                      with type annot = Parser_and_compiler.Annot.t) =
struct
  include
    Gillian.Debugger.Lifter.GilLifter.Make (Parser_and_compiler) (Verification)
      (S_memory)
end

module CLI =
  Gillian.CommandLine.Make (Tyenv) (C_memory) (S_memory) (Parser_and_compiler)
    (Gillian.General.External.Dummy (Parser_and_compiler.Annot))
    (struct
      let runners : Gillian.Bulk.Runner.t list = [ (module C_runner) ]
    end)
    (Gil_to_rust_lifter)

let () = CLI.main ()
