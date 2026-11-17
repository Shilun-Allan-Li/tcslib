import TCSlib.Complexity.BranchingPrograms.BarringtonConverse
set_option autoImplicit false
-- neg_unsealed: reads `BranchingProgram.topDepth` through its body
example (w : ℕ) : BranchingProgram.topDepth w = w * Nat.clog 2 w + Nat.clog 2 w + 3 :=
  rfl
