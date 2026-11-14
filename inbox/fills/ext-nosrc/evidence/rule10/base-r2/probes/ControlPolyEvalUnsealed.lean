import TCSlib.Complexity.Randomized.PolyExpr
open Complexity
example (n : Nat) : PolyExpr.eval .var n = n := by rfl
