import TCSlib.Complexity.BranchingPrograms.Eval
set_option autoImplicit false
attribute [local irreducible] BranchingProgram.evalWith
-- neg_sealed: reads `BranchingProgram.evalWith` through its body
example (B : BranchingProgram 3 2) (x : Fin 2 → Bool) (V : Fin 3 → ℕ) : B.evalWith (fun b (u v : ℕ) => if b then v else u) x V = B.instrs.foldl (fun U ι => ι.stepWith (fun b (u v : ℕ) => if b then v else u) x U) V :=
  rfl
