/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Candidates.ArithmeticDischarge
import TCSlib.Cryptography.Candidates.ExtendedEuclidMachine
import TCSlib.Complexity.Randomized.Primality

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# `PRIMES ∈ P` as the one remaining arithmetic hypothesis

Of the nine fields of the hypothesis bundle `TCSlib.Cryptography.Candidates.ArithmeticFP`,
eight are proved from the binary-arithmetic machines (`ArithmeticDischarge.lean`,
`ExtendedEuclidMachine.lean`). The ninth, `prime : PolyTimeComputable primeStr`, asks for a
deterministic polynomial-time primality test. It is true (Agrawal–Kayal–Saxena; [PS10, p. 33,
§2.6.5], [AB09, §7.2.2 and the chapter notes]), but the library has no deterministic primality
test, so it stays a **named hypothesis**, `PrimesInP`, stated in the library's language form
`PRIMESBin ∈ P` (Seyoon's ruling Q-H1-1 A).

## Main definitions

* `TCSlib.Cryptography.Candidates.PrimesInP` — the proposition `PRIMES ∈ P`.

## Main results

* `TCSlib.Cryptography.Candidates.primesInP_iff` — its reader.
* `TCSlib.Cryptography.Candidates.polyTimeComputable_primeStr_iff_bitsVal` — the bundle's
  most-significant-bit-first test `primeStr` is polynomial-time exactly when the
  little-endian test `x ↦ [bitsVal x is prime]` is.
* `TCSlib.Cryptography.Candidates.polyTimeComputable_primeStr_of_primesInP`,
  `primesInP_of_polyTimeComputable_primeStr` — `PrimesInP` is the bundle's primality field.
* `TCSlib.Cryptography.Candidates.ArithmeticFP.ofPrimesInP`,
  `TCSlib.Cryptography.Candidates.arithmeticFP_iff_primesInP` — the bundle from `PRIMES ∈ P`,
  and `ArithmeticFP ↔ PrimesInP`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (p. 33: primality testing is polynomial-time; §2.6.5, closing remark: the deterministic
  polynomial-time test of Agrawal, Kayal and Saxena.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§7.2.2, opening: Agrawal, Kayal and Saxena gave a deterministic
  polynomial-time algorithm for primality testing; chapter notes: they proved `PRIMES ∈ P`.)
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory TCSlib.Cryptography.Encoding.BinaryArith

/-- **`PRIMES ∈ P`**: the language `Randomized.PRIMESBin` of the little-endian binary words whose
value is prime is decided in deterministic polynomial time, `PRIMESBin ∈ P` [AB09, §7.2.2].

This is the **standing exception** of ruling Q5 A of the efficiency remediation: a true
statement (Agrawal–Kayal–Saxena, [PS10, §2.6.5], [AB09, §7.2.2 and chapter notes]) left as a
named hypothesis because the library has no deterministic primality test. It is a `Prop`, not
an axiom, and is never used as one: the results that need it take it as an explicit argument. -/
def PrimesInP : Prop := Randomized.PRIMESBin ∈ Complexity.P

/-- The reader of `PrimesInP`: `PrimesInP ↔ PRIMESBin ∈ P`. -/
theorem primesInP_iff : PrimesInP ↔ Randomized.PRIMESBin ∈ Complexity.P := Iff.rfl

/-- Glue. The little-endian primality bit of `x` is the bundle's test on the numeral of
`bitsVal x` at width `|x|`: `[bitsVal x is prime] = primeStr (fromLEPoly var ⟨x, x⟩)`
(`fromLEPoly_pairEncode`, `bitsVal x < 2^{|x|}`, `listToNat_natToList`). -/
theorem primeBit_eq_primeStr_fromLEPoly (x : List Bool) :
    [decide (LogProg.bitsVal x).Prime] = primeStr (fromLEPoly .var (pairEncode x x)) := by
  rw [fromLEPoly_pairEncode, PolyExpr.eval_var, primeStr_eq]
  beta_reduce
  rw [listToNat_natToList (LogProg.bitsVal_lt_two_pow x)]

/-- Glue. **The two primality tests are equally hard**: the bundle's test `primeStr`
(most significant bit first, `listToNat`) is polynomial-time if and only if the little-endian
test `x ↦ [bitsVal x is prime]` is.

**Proof sketch.** One way, `primeStr = (little-endian test) ∘ toLE`, as
`bitsVal (toLE w) = ⟦w⟧` (`bitsVal_toLE`). The other way, the little-endian test is
`primeStr ∘ (x ↦ fromLEPoly var ⟨x, x⟩)` (`primeBit_eq_primeStr_fromLEPoly`). -/
theorem polyTimeComputable_primeStr_iff_bitsVal :
    PolyTimeComputable primeStr ↔
      PolyTimeComputable fun x => [decide (LogProg.bitsVal x).Prime] := by
  constructor
  · intro h
    exact (h.comp' (polyTimeComputable_fromLEPoly_var (t := id) (g := id) polyTimeComputable_id
      polyTimeComputable_id)).congr fun x => (primeBit_eq_primeStr_fromLEPoly x).symm
  · intro h
    exact (h.comp' polyTimeComputable_toLE).congr fun w => by
      rw [bitsVal_toLE, primeStr_eq]


/-! ### The bridge and the bundle (with the readers of `PRIMESBin` and `PRIMES`) -/

/-- Glue. The little-endian primality test is the indicator of `PRIMESBin`:
`[bitsVal x is prime] = [x ∈ PRIMESBin]` (`Randomized.mem_PRIMESBin`, `Randomized.mem_PRIMES`,
`Randomized.indicator_eq_true_iff`). -/
theorem primeBit_eq_indicator (x : List Bool) :
    decide (LogProg.bitsVal x).Prime = MultiTapeTM.indicator Randomized.PRIMESBin x := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Randomized.indicator_eq_true_iff,
    Randomized.mem_PRIMESBin, Randomized.mem_PRIMES]

/-- **`PRIMES ∈ P` is the polynomial-time little-endian test**: `PrimesInP` holds if and only if
`x ↦ [bitsVal x is prime]` is polynomial-time (`test_of_mem_P`, `mem_P_of_test`). -/
theorem primesInP_iff_polyTimeComputable_primeBit :
    PrimesInP ↔ PolyTimeComputable fun x => [decide (LogProg.bitsVal x).Prime] := by
  rw [primesInP_iff]
  constructor
  · intro h
    exact (test_of_mem_P h).congr fun x => by rw [primeBit_eq_indicator]
  · intro h
    have hP := mem_P_of_test h
    have hset : {z : List Bool | decide (LogProg.bitsVal z).Prime = true} =
        Randomized.PRIMESBin := by
      ext x
      rw [Set.mem_setOf_eq, decide_eq_true_iff, Randomized.mem_PRIMESBin, Randomized.mem_PRIMES]
    rwa [hset] at hP

/-- **`PRIMES ∈ P` gives the bundle's primality field**: `PrimesInP → PolyTimeComputable primeStr`
[PS10, §2.6.5] (glue through `toLE`, `test_of_mem_P`). -/
theorem polyTimeComputable_primeStr_of_primesInP (h : PrimesInP) : PolyTimeComputable primeStr :=
  polyTimeComputable_primeStr_iff_bitsVal.2 (primesInP_iff_polyTimeComputable_primeBit.1 h)

/-- **The bundle's primality field gives `PRIMES ∈ P`**:
`PolyTimeComputable primeStr → PrimesInP` (glue through `fromLEPoly`, `mem_P_of_test`). -/
theorem primesInP_of_polyTimeComputable_primeStr (h : PolyTimeComputable primeStr) :
    PrimesInP :=
  primesInP_iff_polyTimeComputable_primeBit.2 (polyTimeComputable_primeStr_iff_bitsVal.1 h)

/-- **The arithmetic bundle from `PRIMES ∈ P`**: `PrimesInP → ArithmeticFP`. The eight
arithmetic fields are proved unconditionally (`ArithmeticDischarge.lean`,
`ExtendedEuclidMachine.lean`); only primality uses the hypothesis. -/
theorem ArithmeticFP.ofPrimesInP (h : PrimesInP) : ArithmeticFP where
  mul := polyTimeComputable_mulStr
  add := polyTimeComputable_addStr
  sub := polyTimeComputable_subStr
  divMod := polyTimeComputable_divModStr
  xgcd := polyTimeComputable_xgcdStr
  modExp := polyTimeComputable_modExpStr
  le := polyTimeComputable_leStr
  size := polyTimeComputable_sizeStr
  prime := polyTimeComputable_primeStr_of_primesInP h

/-- **The arithmetic bundle is exactly `PRIMES ∈ P`**: `ArithmeticFP ↔ PrimesInP`. -/
theorem arithmeticFP_iff_primesInP : ArithmeticFP ↔ PrimesInP :=
  ⟨fun H => primesInP_of_polyTimeComputable_primeStr H.prime, ArithmeticFP.ofPrimesInP⟩

end TCSlib.Cryptography.Candidates
