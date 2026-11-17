import TCSlib.Complexity.BranchingPrograms.Defs
set_option autoImplicit false
-- neg_unsealed: reads `BranchingProgram.yield` through its body
example (B : BranchingProgram 3 2) (x : Fin 2 → Bool) : B.yield x = B.instrs.foldl (fun f ι => ι.eval x ∘ f) id :=
  rfl
