import TCSlib.Complexity.CircuitComplexity.NANDLayering
set_option autoImplicit false
-- neg_unsealed: reads `BoolCircuit.litInput` through its body
example (x : Fin 2 → Bool) : BoolCircuit.litInput x = Fin.append x fun i => !x i :=
  rfl
