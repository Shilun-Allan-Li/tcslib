import TCSlib.Complexity.BranchingPrograms.BarringtonConverse
set_option autoImplicit false
attribute [local irreducible] BranchingProgram.topDepth
-- pos_sealed: reads `BranchingProgram.topDepth` through its reader
example (w : ℕ) : BranchingProgram.topDepth w = w * Nat.clog 2 w + Nat.clog 2 w + 3 :=
  BranchingProgram.topDepth_eq w
