import TCSlib.Cryptography.Candidates.Rabin

/-! Seal controls, unsealed: three definitional readings of foreign definitions that close. -/
open TCSlib.Cryptography TCSlib.Cryptography.Candidates TCSlib.Cryptography.NumberTheory Complexity

example : listToNat [true] = 1 := rfl
example (n : ℕ) (y : List Bool) : NUPPT.advInput n y = Turing.pairEncode (List.replicate n true) y := rfl
example (z : DistinctPrimes 3) : z.p = ((z.1.1 : Fin (2 ^ 3)) : ℕ) := rfl
