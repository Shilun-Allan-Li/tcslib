/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Hashing.SIS.Basic
import TCSlib.Cryptography.Foundations.Experiments
import TCSlib.InformationTheory.LeftoverHash

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Universality and extraction for the existing binary matrix hash

## Main definitions

This module reuses `hash` without defining a second binary matrix hash.

## Main results

Distinct binary inputs have a uniform hash difference even over composite moduli.
The resulting collision universality gives a strong, seed-published leftover-hash
bound with explicit dimension and sample parameters.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Equation (4.1.1) and Section 5.2.1 (the binary linear extractor in Regev encryption).
* [Vad12] S. Vadhan, *Pseudorandomness*, 2012, Theorem 6.18.

No SIS or LWE hardness assumption is used here; the SIS norm field is irrelevant.
The family is collision-universal, not pairwise independent: its zero input always
hashes to zero. The proofs use the owner-side universality and min-entropy
equivalences to apply the strong leftover-hash lemma.
-/

namespace TCSlib.Cryptography.Hashing.SIS

open TCSlib.InformationTheory
open TCSlib.Cryptography.SIS (Parameters)

/-- Distinct binary inputs have an exactly uniform modular hash difference for a
uniform matrix [Pei16, Section 5.2.1, regularity argument].

**Proof sketch.** Choose a differing input coordinate. Its integer difference is
`1` or `-1`, hence a unit modulo every allowed modulus. Split the matrix into this
column and the other columns. Once the other columns are fixed, multiplying the
chosen column by the unit and translating is a bijection. Average the resulting
singleton probability over the other columns. The differing coordinate exists
whenever the inputs are distinct, so the empty-column case is vacuous. -/
theorem hash_difference_probability (P : Parameters) (x y : Fin P.columns → Bool)
    (hxy : x ≠ y) (z : Fin P.dimension → ZMod P.modulus) :
    uprob (fun A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) =>
      hash P A x - hash P A y = z) = 1 / (P.modulus : ℝ) ^ P.dimension := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
  let difference : Fin P.columns → ZMod P.modulus :=
    fun k => ((x k).toNat : ZMod P.modulus) - ((y k).toNat : ZMod P.modulus)
  have hpivot : difference j = 1 ∨ difference j = -1 := by
    cases hx : x j <;> cases hy : y j <;> simp_all [difference]
  have hunit : IsUnit (difference j) := by
    rcases hpivot with h | h
    · rw [h]
      exact isUnit_one
    · rw [h]
      exact isUnit_neg_one
  obtain ⟨unit, hunit⟩ := hunit
  let Column := Fin P.dimension → ZMod P.modulus
  let Other := {k : Fin P.columns // k ≠ j} → Column
  let split : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ≃ Other × Column :=
    (Equiv.piComm (fun _ _ => ZMod P.modulus)).trans
      ((Equiv.funSplitAt j Column).trans (Equiv.prodComm Column Other))
  -- For fixed other columns the difference is a unit scaling followed by a translation.
  let move (a : Other) : Equiv.Perm Column :=
    (Equiv.piCongrRight (fun _ : Fin P.dimension => unit.mulRight)).trans
      (Equiv.addRight (fun i => ∑ k : {k : Fin P.columns // k ≠ j}, a k i * difference k))
  have hhash (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus)) :
      hash P A x - hash P A y = move (split A).1 (split A).2 := by
    rw [hash_eq, hash_eq, ← Matrix.mulVec_sub]
    funext i
    change (∑ k, A i k * difference k) =
      A i j * (unit : ZMod P.modulus) + ∑ k : {k : Fin P.columns // k ≠ j}, A i k * difference k
    rw [hunit]
    exact Fintype.sum_eq_add_sum_subtype_ne _ j
  have huniform : uprob (fun c : Column => c = z) = 1 / (P.modulus : ℝ) ^ P.dimension := by
    rw [uprob_eq_card_filter]
    have hfilter : Finset.univ.filter (fun c : Column => c = z) = {z} := by
      ext c
      simp
    rw [hfilter, Finset.card_singleton]
    change ((1 : ℕ) : ℝ) / (Fintype.card (Fin P.dimension → ZMod P.modulus) : ℝ) = _
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_one, Nat.cast_pow]
  have hsection (a : Other) :
      uprob (fun c : Column => move a c = z) = 1 / (P.modulus : ℝ) ^ P.dimension :=
    (uprob_comp_equiv (move a) (· = z)).trans huniform
  -- Every choice of the other columns gives the same singleton probability.
  rw [← uprob_comp_equiv split.symm (fun A => hash P A x - hash P A y = z), uprob_prod]
  simp only [hhash, Equiv.apply_symm_apply, hsection, uexp_def, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

/-- The existing binary matrix hash is collision-universal over every allowed modulus
[Pei16, Section 5.2.1; Vad12, Theorem 6.18].

**Proof sketch.** Specialize the uniform-difference equation to zero, rewrite equality
as zero difference, and convert the probability equation to the owner's collision
count bound. No field structure, norm bound or hardness assumption is used. -/
theorem isUniversal_hash (P : Parameters) : IsUniversal (hash P) := by
  classical
  refine (isUniversal_iff (hash P)).2 ?_
  intro x y hxy
  let Key := Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus)
  have hprob : uprob (fun A : Key => hash P A x = hash P A y) =
      1 / (P.modulus : ℝ) ^ P.dimension := by
    simpa only [sub_eq_zero] using hash_difference_probability P x y hxy 0
  rw [uprob_eq_card_filter] at hprob
  have hkeys : (Fintype.card Key : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have houtputs : (Fintype.card (Fin P.dimension → ZMod P.modulus) : ℝ) =
      (P.modulus : ℝ) ^ P.dimension := by
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow]
  rw [houtputs]
  apply le_of_eq
  calc
    _ = (1 / (P.modulus : ℝ) ^ P.dimension) * Fintype.card Key :=
      (div_eq_iff hkeys).mp hprob
    _ = _ := by rw [one_div, mul_comm, ← div_eq_mul_inv]

/-- The full uniform distribution on binary words of length `m` has min-entropy `m`
[Vad12, Section 6.1, exact finite uniform specialization].

**Proof sketch.** Every word has probability `1/2^m` by the public uniform probability
equation and the finite function-space cardinality. This is `2^(-m)` over the reals. -/
theorem uniform_bits_hasMinEntropy (m : ℕ) :
    FinDist.HasMinEntropy (FinDist.uniform (Fin m → Bool)) (m : ℝ) := by
  refine (FinDist.hasMinEntropy_iff _ _).2 ?_
  intro r
  rw [FinDist.uniform_apply, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    Nat.cast_pow, Nat.cast_ofNat, Real.rpow_neg (by norm_num), Real.rpow_natCast]

/-- Publishing the uniform hash seed retains a statistical extraction error at most
`sqrt(q^dimension / 2^columns)/2` [Pei16, Section 5.2.1; Vad12, Theorem 6.18].

**Proof sketch.** Apply the existing strong leftover-hash lemma to `isUniversal_hash`
and uniform binary min-entropy. Evaluate the modular-vector cardinality and convert
the real negative power into division by the positive binary power. -/
theorem strong_leftover_hash (P : Parameters) :
    statDist (hashPair (hash P) (FinDist.uniform (Fin P.columns → Bool)))
      (FinDist.uniform
        (Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
          (Fin P.dimension → ZMod P.modulus))) ≤
      (1 / 2) * Real.sqrt ((P.modulus : ℝ) ^ P.dimension / (2 : ℝ) ^ P.columns) := by
  classical
  simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, div_eq_mul_inv]
    using leftover_hash (isUniversal_hash P) (uniform_bits_hasMinEntropy P.columns)

/-- Any independently randomized test of the seed-published hash has at most the
strong leftover-hash distinguishing error [Pei16, Section 5.2.1].

**Proof sketch.** For each target pair, the sampler fiber is the product of its
singleton key and the matching subset words. Sum the uniform mass over this
product to recover the public `hashPair` equation. The ideal sampler has a
singleton fiber. Apply the advantage bound for independently randomized tests
and the strong leftover-hash theorem. -/
theorem distAdv_hash_uniform_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters)
    (D : (Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
      (Fin P.dimension → ZMod P.modulus)) → ρ → Bool) :
    distAdv (fun r : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
      (Fin P.columns → Bool) => (r.1, hash P r.1 r.2))
      (id : (Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
        (Fin P.dimension → ZMod P.modulus)) → _) D ≤
      (1 / 2) * Real.sqrt ((P.modulus : ℝ) ^ P.dimension / (2 : ℝ) ^ P.columns) := by
  classical
  let Key := Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus)
  let Input := Fin P.columns → Bool
  let Output := Fin P.dimension → ZMod P.modulus
  let View := Key × Output
  let sampler (r : Key × Input) : View := (r.1, hash P r.1 r.2)
  have hmap : (FinDist.uniform (Key × Input)).map sampler =
      hashPair (hash P) (FinDist.uniform Input) := by
    apply FinDist.ext
    rintro ⟨A, y⟩
    have hfilter : (Finset.univ.filter fun r : Key × Input => sampler r = (A, y)) =
        ({A} : Finset Key) ×ˢ (Finset.univ.filter fun x : Input => hash P A x = y) := by
      apply Finset.ext
      intro r
      rw [Finset.mem_filter, Finset.mem_product]
      simp only [Finset.mem_univ, true_and, Finset.mem_singleton, Finset.mem_filter]
      change (r.1, hash P r.1 r.2) = (A, y) ↔ _
      rw [Prod.mk.injEq]
      constructor
      · rintro ⟨hA, hy⟩
        exact ⟨hA, by simpa only [hA] using hy⟩
      · rintro ⟨hA, hy⟩
        exact ⟨hA, by simpa only [hA]⟩
    rw [FinDist.map_apply, hashPair_apply, hfilter, Finset.sum_product, Finset.sum_singleton,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [FinDist.uniform_apply, Fintype.card_prod, Nat.cast_mul, mul_inv_rev, mul_comm, Key]
  have hideal : (FinDist.uniform View).map (id : View → View) = FinDist.uniform View := by
    apply FinDist.ext
    intro z
    rw [FinDist.map_apply]
    have hfilter : (Finset.univ.filter fun r : View => id r = z) = {z} := by
      ext r
      simp only [id_eq, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [hfilter, Finset.sum_singleton]
  have h := distAdv_le_statDist sampler (id : View → View) D
  rw [hmap, hideal] at h
  exact h.trans (strong_leftover_hash P)

/-- A residue width and `2κ` entropy slack give an explicit exponentially small
extraction error [Pei16, Section 5.2.1, quantitative repository refinement].

**Proof sketch.** Bound `q^dimension` by `2^(dimension*width)`. The sample budget
then bounds the ratio by `2^(-2κ)`, the square of the desired nonnegative bound
before the factor of one half. Compare the square root with that bound, including
parameter zero and empty output dimension. -/
theorem leftover_error_le (P : Parameters) (width κ : ℕ)
    (hq : P.modulus ≤ 2 ^ width) (hm : P.dimension * width + 2 * κ ≤ P.columns) :
    (1 / 2 : ℝ) * Real.sqrt ((P.modulus : ℝ) ^ P.dimension / (2 : ℝ) ^ P.columns) ≤
      (1 / 2 : ℝ) * ((2 : ℝ)⁻¹) ^ κ := by
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hwidth : (P.modulus : ℝ) ≤ (2 : ℝ) ^ width := by exact_mod_cast hq
  have hnum : (P.modulus : ℝ) ^ P.dimension ≤ (2 : ℝ) ^ (P.dimension * width) := by
    rw [Nat.mul_comm P.dimension width, pow_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hwidth _
  have hratio : (P.modulus : ℝ) ^ P.dimension / (2 : ℝ) ^ P.columns ≤
      1 / (2 : ℝ) ^ (2 * κ) := by
    apply (div_le_div_iff₀ (pow_pos htwo _) (pow_pos htwo _)).2
    rw [one_mul]
    calc
      _ ≤ (2 : ℝ) ^ (P.dimension * width) * (2 : ℝ) ^ (2 * κ) :=
        mul_le_mul_of_nonneg_right hnum (pow_nonneg htwo.le _)
      _ = (2 : ℝ) ^ (P.dimension * width + 2 * κ) := by rw [pow_add]
      _ ≤ (2 : ℝ) ^ P.columns := pow_le_pow_right₀ (by norm_num) hm
  have hsquare : 1 / (2 : ℝ) ^ (2 * κ) = (((2 : ℝ)⁻¹) ^ κ) ^ 2 := by
    rw [one_div, ← inv_pow, ← pow_mul, Nat.mul_comm 2 κ]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.sqrt_le_iff.mpr ⟨pow_nonneg (inv_nonneg.mpr htwo.le) _, hratio.trans_eq hsquare⟩

end TCSlib.Cryptography.Hashing.SIS
