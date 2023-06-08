open Gillian_rust
module Legacy = Gillian.Monadic.MonadicSMemory.Lift (Symbolic.Memory)
module S_memory = Gillian.Symbolic.Legacy_s_memory.Modernize (Legacy)

module Gil_to_rust_lifter
    (Verification : Gillian.Abstraction.Verifier.S
                      with type annot = Parser_and_compiler.Annot.t) =
struct
  include
    Gillian.Debugger.Lifter.Gil_lifter.Make (Parser_and_compiler) (Verification)
      (S_memory)
end

module CLI =
  Gillian.Command_line.Make (Tyenv) (Concrete.Memory) (S_memory)
    (Parser_and_compiler)
    (Gillian.General.External.Dummy (Parser_and_compiler.Annot))
    (struct
      let runners : Gillian.Bulk.Runner.t list = [ (module Concrete.Runner) ]
    end)
    (Gil_to_rust_lifter)

let () = CLI.main ()
