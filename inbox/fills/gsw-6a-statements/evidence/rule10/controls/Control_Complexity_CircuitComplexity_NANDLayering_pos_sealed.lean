import TCSlib.Complexity.CircuitComplexity.NANDLayering
set_option autoImplicit false
attribute [local irreducible] BoolCircuit.litInput
-- pos_sealed: reads `BoolCircuit.litInput` through its reader
example (x : Fin 2 → Bool) : BoolCircuit.litInput x = Fin.append x fun i => !x i :=
  BoolCircuit.litInput_eq x
