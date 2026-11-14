import TCSlib.Complexity.Randomized.PPT
open Complexity Turing
example (A : NUPPT) (n : Nat) (y r : List Bool) :
    A.runAtL n y r = A.output (pairEncode (pairEncode (NUPPT.advInput n y) (A.advice n)) r) := by rfl
