import TCSlib.Complexity.CircuitComplexity.FormulaArith.ModSum
set_option autoImplicit false
attribute [local irreducible] BoolCircuit.FormulaArith.modSumDepth
-- pos_sealed: reads `BoolCircuit.FormulaArith.modSumDepth` through its reader
example (M q : ℕ) : BoolCircuit.FormulaArith.modSumDepth M q = 4 * BoolCircuit.FormulaArith.csaLevels M + Nat.clog 2 M + 2 * Nat.clog 2 (Nat.clog 2 M + Nat.clog 2 q + 1) + 10 :=
  BoolCircuit.FormulaArith.modSumDepth_eq M q
