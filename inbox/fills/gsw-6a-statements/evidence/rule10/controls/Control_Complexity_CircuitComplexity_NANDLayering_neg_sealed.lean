import TCSlib.Complexity.CircuitComplexity.NANDLayering
set_option autoImplicit false
attribute [local irreducible] BoolCircuit.litInput
-- neg_sealed: reads `BoolCircuit.litInput` through its body
example (x : Fin 2 → Bool) : BoolCircuit.litInput x = Fin.append x fun i => !x i :=
  rfl
