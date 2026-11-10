/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Hashing.SIS.Basic
import TCSlib.Cryptography.SIS.Assumption
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A dyadic parameter profile for binary SIS hashing

## Main definitions

* `dyadicParameters`: with `t = κ + 1`, use `t` rows, `2 t²` columns, modulus `2^t`,
  and squared-norm bound `2 t²`.
* `dyadicFamily`: give these parameters polynomial residue and signed-output widths.

## Main results

The proved theorems give compression, solution existence, exclusion of nonzero
vectors whose coordinates are all modulus multiples, and exact bit budgets.
Two proved arithmetic lemmas supply the constructor proof fields.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definition 4.1.1 and observations after Equation (4.1.1).

**Deviation.** This explicit dyadic profile is a local specialization, not a parameter
choice asserted by the source. It excludes trivial modulus-multiple solutions but
does not establish hardness or exclude all attacks. A future security theorem requires
`SISAssumption dyadicFamily` as its own independent hypothesis. No LWE or lattice-hardness
reduction, efficient sampler or generic CRH bridge is asserted here.
-/

namespace TCSlib.Cryptography.Hashing.SIS

open Complexity
open TCSlib.Cryptography.SIS (Parameters Family IsSolution)

/-- The profile's modulus `2^(κ+1)` is at least two, including parameter zero.

**Proof sketch.** The exponent is at least one; use monotonicity of natural powers. -/
theorem dyadic_modulus_ge_two (κ : ℕ) : 2 ≤ 2 ^ (κ + 1) := by
  exact Nat.one_lt_two_pow' κ

/-- The squared-norm bound fits the conservative signed-magnitude width.

**Proof sketch.** Apply the elementary natural-number inequality `a < 2^(a+1)`
to `a = 2*(κ+1)^2`. This is representation coverage, not a hardness condition. -/
theorem dyadic_magnitude_fits (κ : ℕ) :
    2 * (κ + 1) ^ 2 < 2 ^ (2 * (κ + 1) ^ 2 + 1) := by
  exact (Nat.lt_two_pow_self (n := 2 * (κ + 1) ^ 2)).trans
    (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

/-- At parameter `κ`, the SIS matrix has `κ+1` rows, `2*(κ+1)^2` columns,
modulus `2^(κ+1)` and squared-norm bound equal to its column count
[Pei16, Definition 4.1.1, local dyadic specialization]. -/
def dyadicParameters (κ : ℕ) : Parameters where
  dimension := κ + 1
  columns := 2 * (κ + 1) ^ 2
  modulus := 2 ^ (κ + 1)
  sqNormBound := 2 * (κ + 1) ^ 2
  modulus_ge_two := dyadic_modulus_ge_two κ

attribute [simps (config := { isSimp := false }) dimension columns modulus sqNormBound]
  dyadicParameters

/-- The dyadic profile has exact polynomial dimensions, residue width `κ+1`,
and magnitude width `2*(κ+1)^2+1` [Pei16, Definition 4.1.1, local specialization].
Its proof fields express representation bounds; the definition asserts no hardness
or uniform implementation. -/
def dyadicFamily : Family where
  parameters := dyadicParameters
  dimensionBound := .add .var (.const 1)
  columnsBound := .mul (.const 2) (.pow (.add .var (.const 1)) 2)
  residueBits := .add .var (.const 1)
  magnitudeBits := .add (.mul (.const 2) (.pow (.add .var (.const 1)) 2)) (.const 1)
  dimension_le := fun κ => by
    rw [dyadicParameters_dimension, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
  columns_le := fun κ => by
    rw [dyadicParameters_columns, PolyExpr.eval_mul, PolyExpr.eval_const,
      PolyExpr.eval_pow, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
  modulus_le_pow := fun κ => by
    rw [dyadicParameters_modulus, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
  sqNormBound_lt_pow := fun κ => by
    simpa only [dyadicParameters_sqNormBound, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const, PolyExpr.eval_pow, PolyExpr.eval_var] using dyadic_magnitude_fits κ

attribute [simps (config := { isSimp := false }) parameters dimensionBound columnsBound
  residueBits magnitudeBits] dyadicFamily

/-- The profile's squared-norm bound is strictly less than the square of its modulus,
excluding the trivial `q`-times-coordinate vectors
[Pei16, observations after Equation (4.1.1), local profile check].

**Proof sketch.** Put `t = κ+1`. Prove `2 t² < 4^t` by induction for `t ≥ 1`:
the base is `2 < 4`, and `2(t+1)² ≤ 8t² < 4^(t+1)`. Rewrite `(2^t)^2 = 4^t`. -/
theorem dyadic_sqNormBound_lt_modulus_sq (κ : ℕ) :
    (dyadicParameters κ).sqNormBound < (dyadicParameters κ).modulus ^ 2 := by
  rw [dyadicParameters_sqNormBound, dyadicParameters_modulus]
  induction κ with
  | zero => decide
  | succ κ ih =>
    have ht : 1 ≤ κ + 1 := by omega
    calc
      2 * (κ + 1 + 1) ^ 2 ≤ 4 * (2 * (κ + 1) ^ 2) := by nlinarith
      _ < 4 * (2 ^ (κ + 1)) ^ 2 :=
        Nat.mul_lt_mul_of_pos_left ih (by decide)
      _ = (2 ^ (κ + 1 + 1)) ^ 2 := by rw [pow_succ]; ring

/-- The dyadic binary domain is strictly larger than the full modular codomain
[Pei16, observations after Equation (4.1.1), local profile check].

**Proof sketch.** For `t = κ+1 ≥ 1`, the cardinalities are `2^(2t²)` and
`(2^t)^t = 2^(t²)`. Strict monotonicity of powers gives the inequality. -/
theorem dyadic_cardinal_compression (κ : ℕ) :
    (dyadicParameters κ).modulus ^ (dyadicParameters κ).dimension <
      2 ^ (dyadicParameters κ).columns := by
  rw [dyadicParameters_modulus, dyadicParameters_dimension, dyadicParameters_columns,
    ← pow_mul]
  apply Nat.pow_lt_pow_right (by decide)
  have ht : 0 < κ + 1 := by omega
  nlinarith [sq_pos_of_pos ht]

/-- Every matrix in the dyadic profile has a valid SIS solution
[Pei16, observations after Equation (4.1.1), local specialization].

**Proof sketch.** Apply `exists_solution` with `dyadic_cardinal_compression` and
the parameter equations showing that the column count equals the norm budget. -/
theorem dyadic_exists_solution (κ : ℕ)
    (A : Matrix (Fin (dyadicParameters κ).dimension) (Fin (dyadicParameters κ).columns)
      (ZMod (dyadicParameters κ).modulus)) :
    ∃ z, IsSolution (dyadicParameters κ) A z := by
  apply exists_solution _ A (dyadic_cardinal_compression κ)
  rw [dyadicParameters_columns, dyadicParameters_sqNormBound]

/-- A vector all of whose integer coordinates are divisible by the modulus cannot
be a solution in this profile [Pei16, observations after Equation (4.1.1), local check].

**Proof sketch.** A zero vector fails nonzeroness. Otherwise a nonzero divisible
coordinate has absolute value at least the modulus and square at least its square.
The total squared norm contradicts `dyadic_sqNormBound_lt_modulus_sq`. -/
theorem dyadic_not_isSolution_of_modulus_dvd (κ : ℕ)
    (A : Matrix (Fin (dyadicParameters κ).dimension) (Fin (dyadicParameters κ).columns)
      (ZMod (dyadicParameters κ).modulus))
    (z : Fin (dyadicParameters κ).columns → ℤ)
    (hz : ∀ i, ((dyadicParameters κ).modulus : ℤ) ∣ z i) :
    ¬ IsSolution (dyadicParameters κ) A z := by
  classical
  intro h
  rcases (TCSlib.Cryptography.SIS.isSolution_iff _ A z).mp h with ⟨hne, hnorm, _⟩
  have hex : ∃ i, z i ≠ 0 := by
    by_contra hn
    apply hne
    funext i
    by_contra hi
    exact hn ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  have hsq : ((dyadicParameters κ).modulus : ℤ) ^ 2 ≤ z i ^ 2 := by
    have habs := Int.ofNat_le.mpr (Int.natAbs_le_of_dvd_ne_zero (hz i) hi)
    rw [Int.natAbs_natCast, Int.natCast_natAbs] at habs
    nlinarith [sq_abs (z i), abs_nonneg (z i),
      Int.natCast_nonneg (dyadicParameters κ).modulus]
  have hsingle : z i ^ 2 ≤ ∑ j, z j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)
  have hlt : ((dyadicParameters κ).sqNormBound : ℤ) <
      ((dyadicParameters κ).modulus : ℤ) ^ 2 := by
    exact_mod_cast dyadic_sqNormBound_lt_modulus_sq κ
  exact (not_le_of_gt hlt) (hsq.trans (hsingle.trans hnorm))

/-- The canonical matrix index budget is exactly `2*(κ+1)^4` bits.

**Proof sketch.** Read the existing `Family.inputBitsBound_eq`, the profile's
data projections and polynomial evaluation equations; normalize the product. -/
theorem dyadic_inputBitsBound_eval (κ : ℕ) :
    dyadicFamily.inputBitsBound.eval κ = 2 * (κ + 1) ^ 4 := by
  rw [Family.inputBitsBound_eq]
  simp only [dyadicFamily_dimensionBound, dyadicFamily_columnsBound,
    dyadicFamily_residueBits, PolyExpr.eval_mul, PolyExpr.eval_add,
    PolyExpr.eval_pow, PolyExpr.eval_var, PolyExpr.eval_const]
  ring

/-- The signed SIS output budget is exactly `4*(κ+1)^4 + 4*(κ+1)^2` bits.

**Proof sketch.** Read `Family.outputBitsBound_eq` and the profile projections.
There are `2t²` coordinates with `2t²+2` bits apiece; expand their product. -/
theorem dyadic_outputBitsBound_eval (κ : ℕ) :
    dyadicFamily.outputBitsBound.eval κ = 4 * (κ + 1) ^ 4 + 4 * (κ + 1) ^ 2 := by
  rw [Family.outputBitsBound_eq]
  simp only [dyadicFamily_columnsBound, dyadicFamily_magnitudeBits,
    PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_pow,
    PolyExpr.eval_var, PolyExpr.eval_const]
  ring

end TCSlib.Cryptography.Hashing.SIS
