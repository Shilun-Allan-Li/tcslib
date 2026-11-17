import TCSlib.Complexity.BranchingPrograms.Barrington
set_option autoImplicit false
-- neg_unsealed: reads `BranchingProgram.sigma1` through its body
example : BranchingProgram.sigma1 = List.formPerm [0, 1, 2, 3, 4] :=
  rfl
