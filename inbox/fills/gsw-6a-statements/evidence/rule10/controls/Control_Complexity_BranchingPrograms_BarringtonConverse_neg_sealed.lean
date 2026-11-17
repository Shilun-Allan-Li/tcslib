import TCSlib.Complexity.BranchingPrograms.BarringtonConverse
set_option autoImplicit false
attribute [local irreducible] BranchingProgram.topDepth
-- neg_sealed: reads `BranchingProgram.topDepth` through its body
example (w : ℕ) : BranchingProgram.topDepth w = w * Nat.clog 2 w + Nat.clog 2 w + 3 :=
  rfl
