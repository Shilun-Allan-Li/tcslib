import TCSlib.Cryptography.Candidates.PrimesInP
attribute [local irreducible] TCSlib.Cryptography.Candidates.modExpModulus TCSlib.Cryptography.Candidates.xgcdState TCSlib.Cryptography.Candidates.PrimesInP TCSlib.Cryptography.Candidates.mulStr
open Complexity Turing TCSlib.Cryptography.NumberTheory TCSlib.Cryptography.Candidates
open TCSlib.Cryptography.Encoding.BinaryArith

-- owner ArithmeticDischarge: modExpModulus
example (N : List Bool) : modExpModulus N =
    if decide (LogProg.bitsVal (toLE N) = 0) then Nat.bits (2 ^ N.length) else toLE N := rfl  -- NEG1
example (N : List Bool) : modExpModulus N =
    if decide (LogProg.bitsVal (toLE N) = 0) then Nat.bits (2 ^ N.length) else toLE N :=
  modExpModulus_eq N  -- POS1
-- owner ExtendedEuclidMachine: xgcdState
example (b r' r s' s : ℕ) : xgcdState b r' r s' s = pairEncode (Nat.bits b)
    (pairEncode (pairEncode (Nat.bits r') (Nat.bits r)) (pairEncode (Nat.bits s') (Nat.bits s))) :=
  rfl  -- NEG2
example (b r' r s' s : ℕ) : xgcdState b r' r s' s = pairEncode (Nat.bits b)
    (pairEncode (pairEncode (Nat.bits r') (Nat.bits r)) (pairEncode (Nat.bits s') (Nat.bits s))) :=
  xgcdState_eq b r' r s' s  -- POS2
-- owner PrimesInP: PrimesInP
example : PrimesInP ↔ Randomized.PRIMESBin ∈ Complexity.P := Iff.rfl  -- NEG3
example : PrimesInP ↔ Randomized.PRIMESBin ∈ Complexity.P := primesInP_iff  -- POS3
-- the base's mulStr (the scope request): no every-input reader exists
example (z : List Bool) : mulStr z = natToList ((pairFstD z).length + (pairSndD z).length)
    (listToNat (pairFstD z) * listToNat (pairSndD z)) := rfl  -- NEG4
example (a b : List Bool) : mulStr (pairEncode a b) =
    natToList (a.length + b.length) (listToNat a * listToNat b) := mulStr_pairEncode a b  -- POS4
