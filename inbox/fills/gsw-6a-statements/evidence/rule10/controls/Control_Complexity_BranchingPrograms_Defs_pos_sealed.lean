import TCSlib.Complexity.BranchingPrograms.Defs
set_option autoImplicit false
attribute [local irreducible] BranchingProgram.yield
-- pos_sealed: reads `BranchingProgram.yield` through its reader
example (B : BranchingProgram 3 2) (x : Fin 2 → Bool) : B.yield x = B.instrs.foldl (fun f ι => ι.eval x ∘ f) id :=
  BranchingProgram.yield_eq B x
