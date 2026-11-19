/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Encoding.BinaryArith
import TCSlib.Complexity.ClassP.BinaryArith.ModPow
import TCSlib.Complexity.ClassP.BinaryArith.Unary

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The cheap arithmetic fields of `ArithmeticFP`, from the binary-arithmetic machines

The hypothesis bundle `TCSlib.Cryptography.Candidates.ArithmeticFP` asks for nine string
functions on fixed-width, most-significant-bit-first numerals to be polynomial-time. This file
proves seven of them (`mulStr`, `addStr`, `subStr`, `divModStr`, `modExpStr`, `leStr`,
`sizeStr`) from the proved machines of `Complexity.BinArith` (normalized little-endian words)
and the representation adapters of `TCSlib.Cryptography.Encoding.BinaryArith` (`toLE`,
`fromLEPoly`), with no hypothesis.

Each machine reads the two components of its input with the total projections `pairFstD` and
`pairSndD`, converts them with `toLE`, runs the `Complexity.BinArith` machine, and writes the
result back at the width the bundle prescribes with `fromLEPoly` at the template `PolyExpr.var`,
whose first component carries the width as its length (`|a| + |b|`, `|a|`, `|b|` or `|N|`).

**Edge cases.** Leading zeros are allowed on input (`toLE` normalizes). At `⟦b⟧ = 0` Lean's
`a / 0 = 0` and `a mod 0 = a` agree with `BinArith.div` and `BinArith.mod`. For `modExpStr` at
`⟦N⟧ = 0` the bundle writes the low `|N|` bits of `a^x`; `BinArith.powMod` returns `0` at modulus
`0`, so the machine runs it at the modulus `2^{|N|}` instead (`natToList_mod_two_pow`), never
materializing `a^x`.

**Readers.** `Arithmetic.lean` reads the string functions on encoded pairs (`mulStr_pairEncode`,
…) and on every word (`mulStr_eq`, …). The machines are first proved on re-paired inputs
`z ↦ f ⟨pairFstD z, pairSndD z⟩`, then on every word through `f_eq`.

## Main definitions

* `TCSlib.Cryptography.Candidates.modExpModulus` — the modulus word the exponentiation machine
  runs at (`2^{|N|}` in place of a zero modulus).

## Main results

* `TCSlib.Cryptography.Candidates.polyTimeComputable_mulStr_pairEncode`,
  `polyTimeComputable_addStr_pairEncode`, `polyTimeComputable_subStr_pairEncode`,
  `polyTimeComputable_divModStr_pairEncode`, `polyTimeComputable_leStr_pairEncode` —
  the pair functions on re-paired inputs.
* `TCSlib.Cryptography.Candidates.polyTimeComputable_modExpStr_pairEncode` — modular
  exponentiation [PS10, Algorithm 45.5, Theorem 45.6] on re-paired triples.
* `TCSlib.Cryptography.Candidates.polyTimeComputable_sizeStr` — the bit length in unary
  (the field `ArithmeticFP.size`).
* `TCSlib.Cryptography.Candidates.polyTimeComputable_mulStr`, `polyTimeComputable_addStr`,
  `polyTimeComputable_subStr`, `polyTimeComputable_divModStr`, `polyTimeComputable_modExpStr`,
  `polyTimeComputable_leStr` — the fields `mul`, `add`, `sub`, `divMod`, `modExp`, `le`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 45.5 and Theorem 45.6, modular exponentiation.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§7.2 and Exercise 7.3, the binary-arithmetic machines.)

Everything else here is Glue: adaptation between the bundle's numerals and the machines' words.
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory TCSlib.Cryptography.Encoding.BinaryArith

/-! ### Reading the machines' words -/

/-- Glue. The first component of a word, converted to little-endian, is polynomial-time:
`z ↦ toLE (pairFstD z)`. -/
theorem polyTimeComputable_toLE_pairFstD : PolyTimeComputable fun z => toLE (pairFstD z) :=
  polyTimeComputable_toLE.comp' polyTimeComputable_pairFstD

/-- Glue. The second component of a word, converted to little-endian, is polynomial-time:
`z ↦ toLE (pairSndD z)`. -/
theorem polyTimeComputable_toLE_pairSndD : PolyTimeComputable fun z => toLE (pairSndD z) :=
  polyTimeComputable_toLE.comp' polyTimeComputable_pairSndD

/-- Glue. The machines' operand pair of a word, `z ↦ ⟨toLE (pairFstD z), toLE (pairSndD z)⟩`,
is polynomial-time. -/
theorem polyTimeComputable_toLE_pair :
    PolyTimeComputable fun z => pairEncode (toLE (pairFstD z)) (toLE (pairSndD z)) :=
  polyTimeComputable_toLE_pairFstD.pairEncode polyTimeComputable_toLE_pairSndD

/-- Glue. The machines' operand pair reads as the bundle's numbers:
`⟨toLE a, toLE b⟩ = ⟨bits ⟦a⟧, bits ⟦b⟧⟩` (`toLE_eq_natBits`). -/
theorem toLE_pair_eq (a b : List Bool) :
    pairEncode (toLE a) (toLE b) =
      pairEncode (Nat.bits (listToNat a)) (Nat.bits (listToNat b)) := by
  rw [toLE_eq_natBits, toLE_eq_natBits]

/-- Glue. Writing a normalized word at the width of a template: `fromLEPoly var ⟨u, bits n⟩`
is the `|u|`-bit numeral of `n` (`fromLEPoly_pairEncode`, `LogProg.bitsVal_bits`). -/
theorem fromLEPoly_var_bits (u : List Bool) (n : ℕ) :
    fromLEPoly .var (pairEncode u (Nat.bits n)) = natToList u.length n := by
  rw [fromLEPoly_pairEncode, LogProg.bitsVal_bits, PolyExpr.eval_var]

/-- Glue. A machine writing at the width of a template: if `t` and `g` are polynomial-time,
so is `z ↦ fromLEPoly var ⟨t z, g z⟩`. -/
theorem polyTimeComputable_fromLEPoly_var {t g : List Bool → List Bool}
    (ht : PolyTimeComputable t) (hg : PolyTimeComputable g) :
    PolyTimeComputable fun z => fromLEPoly .var (pairEncode (t z) (g z)) :=
  (polyTimeComputable_fromLEPoly .var).comp' (ht.pairEncode hg)

/-! ### Multiplication, addition, subtraction -/

/-- Glue. **Binary multiplication of numerals is polynomial-time** on re-paired inputs:
`z ↦ mulStr ⟨a, b⟩ = ⟦⟦a⟧ · ⟦b⟧⟧_{|a| + |b|}` with `a = pairFstD z`, `b = pairSndD z`
(`BinArith.polyTimeComputable_mul`, [AB09, §7.2]). -/
theorem polyTimeComputable_mulStr_pairEncode :
    PolyTimeComputable fun z => mulStr (pairEncode (pairFstD z) (pairSndD z)) :=
  (polyTimeComputable_fromLEPoly_var polyTimeComputable_pairConcat
      (BinArith.polyTimeComputable_mul.comp' polyTimeComputable_toLE_pair)).congr fun z => by
    rw [toLE_pair_eq, BinArith.mul_pairEncode, fromLEPoly_var_bits, List.length_append,
      mulStr_pairEncode]

/-- Glue. **Binary addition of numerals is polynomial-time** on re-paired inputs:
`z ↦ addStr ⟨a, b⟩ = ⟦⟦a⟧ + ⟦b⟧⟧_{|a| + |b|}` (`BinArith.polyTimeComputable_add`,
[AB09, §7.2]). -/
theorem polyTimeComputable_addStr_pairEncode :
    PolyTimeComputable fun z => addStr (pairEncode (pairFstD z) (pairSndD z)) :=
  (polyTimeComputable_fromLEPoly_var polyTimeComputable_pairConcat
      (BinArith.polyTimeComputable_add.comp' polyTimeComputable_toLE_pair)).congr fun z => by
    rw [toLE_pair_eq, BinArith.add_pairEncode, fromLEPoly_var_bits, List.length_append,
      addStr_pairEncode]

/-- Glue. **Truncated subtraction of numerals is polynomial-time** on re-paired inputs:
`z ↦ subStr ⟨a, b⟩ = ⟦⟦a⟧ ∸ ⟦b⟧⟧_{|a|}` (`BinArith.polyTimeComputable_sub`, [AB09, §7.2]). -/
theorem polyTimeComputable_subStr_pairEncode :
    PolyTimeComputable fun z => subStr (pairEncode (pairFstD z) (pairSndD z)) :=
  (polyTimeComputable_fromLEPoly_var polyTimeComputable_pairFstD
      (BinArith.polyTimeComputable_sub.comp' polyTimeComputable_toLE_pair)).congr fun z => by
    rw [toLE_pair_eq, BinArith.sub_pairEncode, fromLEPoly_var_bits, subStr_pairEncode]

/-! ### Division with remainder, comparison -/

/-- Glue. **Division with remainder of numerals is polynomial-time** on re-paired inputs:
`z ↦ divModStr ⟨a, b⟩ = ⟨⟦⟦a⟧ / ⟦b⟧⟧_{|a|}, ⟦⟦a⟧ mod ⟦b⟧⟧_{|b|}⟩`, including `⟦b⟧ = 0`, where
`a / 0 = 0` and `a mod 0 = a` hold for the machines as for Lean (`BinArith.polyTimeComputable_div`,
`BinArith.polyTimeComputable_mod`, [AB09, §7.2]). -/
theorem polyTimeComputable_divModStr_pairEncode :
    PolyTimeComputable fun z => divModStr (pairEncode (pairFstD z) (pairSndD z)) :=
  ((polyTimeComputable_fromLEPoly_var polyTimeComputable_pairFstD
      (BinArith.polyTimeComputable_div.comp' polyTimeComputable_toLE_pair)).pairEncode
    (polyTimeComputable_fromLEPoly_var polyTimeComputable_pairSndD
      (BinArith.polyTimeComputable_mod.comp' polyTimeComputable_toLE_pair))).congr fun z => by
    rw [toLE_pair_eq, BinArith.div_pairEncode, BinArith.mod_pairEncode, fromLEPoly_var_bits,
      fromLEPoly_var_bits, divModStr_pairEncode]

/-- Glue. **Comparison of numerals is polynomial-time** on re-paired inputs:
`z ↦ leStr ⟨a, b⟩ = [⟦a⟧ ≤ ⟦b⟧]` (`BinArith.polyTimeComputable_le`, [AB09, §7.2]). -/
theorem polyTimeComputable_leStr_pairEncode :
    PolyTimeComputable fun z => leStr (pairEncode (pairFstD z) (pairSndD z)) :=
  (BinArith.polyTimeComputable_le.comp' polyTimeComputable_toLE_pair).congr fun z => by
    rw [toLE_pair_eq, BinArith.le_pairEncode, leStr_pairEncode]

/-! ### Modular exponentiation -/

/-- Glue. The modulus the exponentiation machine runs at, as a little-endian word: `toLE N`
(`= bits ⟦N⟧`) when `⟦N⟧ ≠ 0`, and `bits (2^{|N|})` when `⟦N⟧ = 0` (the bundle then keeps the
low `|N|` bits of `a^x`). -/
def modExpModulus (N : List Bool) : List Bool :=
  if decide (LogProg.bitsVal (toLE N) = 0) then Nat.bits (2 ^ N.length) else toLE N

/-- The defining equation of `modExpModulus`:
`modExpModulus N = if bitsVal (toLE N) = 0 then bits (2^{|N|}) else toLE N`. -/
theorem modExpModulus_eq (N : List Bool) :
    modExpModulus N =
      if decide (LogProg.bitsVal (toLE N) = 0) then Nat.bits (2 ^ N.length) else toLE N := rfl

/-- Glue. **The exponentiation modulus as a number**: `modExpModulus N = bits M` with
`M = 2^{|N|}` if `⟦N⟧ = 0` and `M = ⟦N⟧` otherwise; in both cases `M ≠ 0` and
`⟦a^x mod M⟧_{|N|} = ⟦a^x mod ⟦N⟧⟧_{|N|}` for all `a, x` (for `⟦N⟧ = 0` the `|N|`-bit numeral
keeps only the low bits, `natToList_mod_two_pow`, and `a^x mod 0 = a^x`). -/
theorem modExpModulus_spec (N : List Bool) :
    ∃ M : ℕ, M ≠ 0 ∧ modExpModulus N = Nat.bits M ∧
      ∀ a x : ℕ, natToList N.length (a ^ x % M) = natToList N.length (a ^ x % listToNat N) := by
  rw [modExpModulus_eq, bitsVal_toLE]
  by_cases hN : listToNat N = 0
  · refine ⟨2 ^ N.length, (Nat.two_pow_pos _).ne', if_pos (decide_eq_true hN), fun a x => ?_⟩
    rw [natToList_mod_two_pow, hN, Nat.mod_zero]
  · exact ⟨listToNat N, hN, by rw [if_neg (by simpa using hN), toLE_eq_natBits], fun _ _ => rfl⟩

/-- Glue. The exponentiation modulus is polynomial-time: a zero test on `toLE N`
(`BinArith.polyTimeComputable_isZero`), then `bits (2^{|N|})`
(`BinArith.polyTimeComputable_powerOfTwo`) or `toLE N`. -/
theorem polyTimeComputable_modExpModulus : PolyTimeComputable modExpModulus :=
  (polyTimeComputable_ite (BinArith.polyTimeComputable_isZero.comp' polyTimeComputable_toLE)
      BinArith.polyTimeComputable_powerOfTwo polyTimeComputable_toLE).congr
    fun N => (modExpModulus_eq N).symm

/-- **Modular exponentiation of numerals is polynomial-time** [PS10, Algorithm 45.5,
Theorem 45.6] on re-paired triples: `z ↦ modExpStr ⟨a, ⟨x, N⟩⟩ = ⟦⟦a⟧^{⟦x⟧} mod ⟦N⟧⟧_{|N|}`
with `a = pairFstD z`, `x = pairFstD (pairSndD z)`, `N = pairSndD (pairSndD z)`, including
`⟦N⟧ = 0`, where the value is the low `|N|` bits of `⟦a⟧^{⟦x⟧}`.

**Deviation:** [PS10] reads `N > 0`; the bundle's total string function also fixes the value
at `N = 0`. The machine is `BinArith.powMod` ([AB09, Exercise 7.3], repeated squaring) at the
modulus `modExpModulus N` (`2^{|N|}` when `⟦N⟧ = 0`, since `powMod` returns `0` at modulus `0`).

**Proof sketch.** Convert `a` and `x` with `toLE`, compute the modulus word `bits M`
(`modExpModulus_spec`), run `powMod` on `⟨bits ⟦a⟧, ⟨bits ⟦x⟧, bits M⟩⟩` to get
`bits (⟦a⟧^{⟦x⟧} mod M)` (`BinArith.powMod_pairEncode`, `M ≠ 0`), and write it at width `|N|`;
the spec's last clause turns `mod M` into `mod ⟦N⟧`. -/
theorem polyTimeComputable_modExpStr_pairEncode :
    PolyTimeComputable fun z =>
      modExpStr (pairEncode (pairFstD z)
        (pairEncode (pairFstD (pairSndD z)) (pairSndD (pairSndD z)))) := by
  have hpow : PolyTimeComputable fun z =>
      BinArith.powMod (pairEncode (toLE (pairFstD z))
        (pairEncode (toLE (pairFstD (pairSndD z))) (modExpModulus (pairSndD (pairSndD z))))) :=
    BinArith.polyTimeComputable_powMod.comp' (polyTimeComputable_toLE_pairFstD.pairEncode
      ((polyTimeComputable_toLE.comp' BinArith.polyTimeComputable_slot2).pairEncode
        (polyTimeComputable_modExpModulus.comp' BinArith.polyTimeComputable_slot3)))
  refine (polyTimeComputable_fromLEPoly_var BinArith.polyTimeComputable_slot3 hpow).congr
    fun z => ?_
  obtain ⟨M, hM0, hMw, hMv⟩ := modExpModulus_spec (pairSndD (pairSndD z))
  rw [hMw, toLE_eq_natBits, toLE_eq_natBits, BinArith.powMod_pairEncode _ _ _ hM0,
    fromLEPoly_var_bits, hMv, modExpStr_pairEncode]

/-! ### The bit length -/

/-- **The bit length is polynomial-time** (the field `ArithmeticFP.size`): `sizeStr w =
1^{size ⟦w⟧}` is polynomial-time, being `1^{|toLE w|}` since `toLE w = bits ⟦w⟧` and
`|bits n| = size n` (Mathlib's `Nat.size_eq_bits_len`); Glue over `polyTimeComputable_toLE`
and the unary writer `polyTimeComputable_unaryPoly`. -/
theorem polyTimeComputable_sizeStr : PolyTimeComputable sizeStr :=
  ((polyTimeComputable_unaryPoly .var).comp' polyTimeComputable_toLE).congr fun w => by
    rw [PolyExpr.eval_var, toLE_eq_natBits, Nat.size_eq_bits_len, sizeStr_eq]

/-! ### The fields (with the every-input equations of `Arithmetic.lean`) -/

/-- **Binary multiplication is polynomial-time** (the field `ArithmeticFP.mul`):
`PolyTimeComputable mulStr`, from `polyTimeComputable_mulStr_pairEncode` and `mulStr_eq`. -/
theorem polyTimeComputable_mulStr : PolyTimeComputable mulStr :=
  polyTimeComputable_mulStr_pairEncode.congr fun z => by rw [mulStr_pairEncode, mulStr_eq]

/-- **Binary addition is polynomial-time** (the field `ArithmeticFP.add`):
`PolyTimeComputable addStr`. -/
theorem polyTimeComputable_addStr : PolyTimeComputable addStr :=
  polyTimeComputable_addStr_pairEncode.congr fun z => by rw [addStr_pairEncode, addStr_eq]

/-- **Truncated subtraction is polynomial-time** (the field `ArithmeticFP.sub`):
`PolyTimeComputable subStr`. -/
theorem polyTimeComputable_subStr : PolyTimeComputable subStr :=
  polyTimeComputable_subStr_pairEncode.congr fun z => by rw [subStr_pairEncode, subStr_eq]

/-- **Division with remainder is polynomial-time** (the field `ArithmeticFP.divMod`):
`PolyTimeComputable divModStr`. -/
theorem polyTimeComputable_divModStr : PolyTimeComputable divModStr :=
  polyTimeComputable_divModStr_pairEncode.congr fun z => by
    rw [divModStr_pairEncode, divModStr_eq]

/-- **Modular exponentiation is polynomial-time** (the field `ArithmeticFP.modExp`)
[PS10, Algorithm 45.5, Theorem 45.6]: `PolyTimeComputable modExpStr`. -/
theorem polyTimeComputable_modExpStr : PolyTimeComputable modExpStr :=
  polyTimeComputable_modExpStr_pairEncode.congr fun z => by
    rw [modExpStr_pairEncode, modExpStr_eq]

/-- **Comparison is polynomial-time** (the field `ArithmeticFP.le`):
`PolyTimeComputable leStr`. -/
theorem polyTimeComputable_leStr : PolyTimeComputable leStr :=
  polyTimeComputable_leStr_pairEncode.congr fun z => by rw [leStr_pairEncode, leStr_eq]

end TCSlib.Cryptography.Candidates
