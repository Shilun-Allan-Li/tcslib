/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Owen McGinty
-/

import TCSlib.BooleanAnalysis.Hypercontractivity.Randomization.Basic
import TCSlib.BooleanAnalysis.Hypercontractivity.Products.Norms

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Signed anisotropic noise contraction

## Main definitions

Coordinate noise is defined in `Randomization.Definitions`.

## Main results

* `coordinate_noise_negative_contraction`: an exponent-dependent negative rate is
  contractive in every coordinate, with rate `2/5` at exponent four.
* `signed_anisotropicNoise_contraction`: signed coordinate noise contracts every
  finite-product norm with exponent greater than one.

The coordinate laws may differ. The contraction rate depends only on the exponent.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, Proposition 9.19 (proof), Definition 10.40, Lemma 10.43,
  and Theorem 10.44.
-/

open scoped BigOperators

namespace BooleanAnalysis.Hypercontractivity

open RandomizationAux

universe u

/-- For every exponent `q ≥ 2`, a positive rate `c ≤ 1` makes negative noise in
any single coordinate contractive in `Lᵠ`; at exponent four, one may take `c = 2/5`.
[OD14, Lem. 10.43; Def. 10.40; Thm. 10.44, proof]
This states the coordinate contraction used in the proof of Theorem 10.44 separately
and extends the source's homogeneous products to heterogeneous finite coordinate laws.
The rate depends only on the exponent.

**Proof sketch.** Choose the rate from the normalized scalar contraction. Apply the
conditional-mean moment comparison while retaining all coordinates except the selected
one. Its reflected residual is exactly negative coordinate noise. Take the increasing
positive `q`th root to obtain the norm inequality. -/
theorem coordinate_noise_negative_contraction (q : ℝ) (hq : 2 ≤ q) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ (q = 4 → c = 2 / 5) ∧
      ∀ (n : ℕ) (P : FiniteProduct.{u} n) (i : Fin n) (f : P.Point → ℝ),
        P.norm q (coordinateNoise P i (-c) f) ≤ P.norm q f :=
  (by
  classical
  obtain ⟨c, hc0, hc1, hc4, hscalar⟩ :=
    CenteredContraction.scalar_contraction q hq
  refine ⟨c, hc0, hc1, hc4, ?_⟩
  intro n P i f
  have hqpos : 0 < q := by linarith
  unfold FiniteProduct.norm
  refine Real.rpow_le_rpow ?_ ?_ (one_div_nonneg.mpr hqpos.le)
  · unfold FiniteProduct.expect
    exact Finset.sum_nonneg (fun x _ =>
      mul_nonneg
        (Finset.prod_nonneg (fun j _ => (P.weight_pos j (x j)).le))
        (Real.rpow_nonneg (abs_nonneg _) q))
  · simpa only [coordinateNoise, FiniteProduct.laplacian, sub_sub_self,
      neg_mul, ← sub_eq_add_neg] using
      condExp_negative_moment_le P (Finset.univ.erase i) f q hqpos
        c hc0.le hc1 hscalar
)

/-- Noise in one coordinate is self-adjoint for the product expectation pairing
at every real rate. [OD14, Def. 10.40; Prop. 9.19 (proof)]
The identity also permits heterogeneous finite coordinate laws.

**Proof sketch.** Express coordinate noise as a linear combination of the
identity and conditional expectation onto the other coordinates. Conditional
expectation is self-adjoint, and finite expectation preserves linear
combinations. -/
private theorem coordinateNoise_selfAdjoint {n : ℕ} (P : FiniteProduct.{u} n)
    (i : Fin n) (ρ : ℝ) (f g : P.Point → ℝ) :
    P.expect (fun x => coordinateNoise P i ρ f x * g x) =
      P.expect (fun x => f x * coordinateNoise P i ρ g x) :=
  (by
  classical
  have h := P.condExp_selfAdjoint (Finset.univ.erase i) f g
  convert congrArg
      (fun a : ℝ =>
        ρ * P.expect (fun x => f x * g x) + (1 - ρ) * a)
      h.symm using 1 <;>
    simp only [FiniteProduct.expect, Finset.mul_sum, ← Finset.sum_add_distrib] <;>
    apply Finset.sum_congr rfl <;>
    intro x _ <;>
    simp only [coordinateNoise, FiniteProduct.laplacian] <;>
    ring
)

/-- Noise in a single coordinate at any rate between zero and one contracts
the finite-product `Lᵠ` norm for every `q ≥ 1`.
[OD14, Ex. 8.11; Def. 10.40; Thm. 10.44 (proof)]
The bound includes both endpoint rates and heterogeneous coordinate laws.

**Proof sketch.** Write coordinate noise as a convex combination of the function
and its conditional expectation over that coordinate. Weighted Jensen bounds its
absolute moment by the corresponding convex combination of moments. Conditional
expectation contracts the moment, so this average is at most the original moment.
Take the increasing positive `q`th root. -/
private theorem coordinate_noise_positive_contraction {n : ℕ}
    (P : FiniteProduct.{u} n) (i : Fin n) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (f : P.Point → ℝ)
    (q : ℝ) (hq : 1 ≤ q) :
    P.norm q (coordinateNoise P i ρ f) ≤ P.norm q f :=
  (by
  classical
  have hmass (x : P.Point) : 0 ≤ P.mass x :=
    Finset.prod_nonneg fun j _ => (P.weight_pos j (x j)).le
  have hpoint (x : P.Point) :
      |coordinateNoise P i ρ f x| ^ q ≤
        ρ * |f x| ^ q +
          (1 - ρ) * |P.condExp (Finset.univ.erase i) f x| ^ q := by
    have haff : coordinateNoise P i ρ f x =
        ρ * f x + (1 - ρ) * P.condExp (Finset.univ.erase i) f x := by
      simp only [coordinateNoise, FiniteProduct.laplacian]
      ring
    have h := weighted_abs_rpow_sum_le (Finset.univ : Finset Bool)
      (fun b => if b then ρ else 1 - ρ)
      (fun b => if b then f x else P.condExp (Finset.univ.erase i) f x) q
      (by intro b _; cases b <;> simp <;> linarith)
      (by simp) hq
    simpa [Fintype.sum_bool, haff] using h
  have hmoment :
      P.expect (fun x => |coordinateNoise P i ρ f x| ^ q) ≤
        P.expect (fun x => |f x| ^ q) := by
    calc
      P.expect (fun x => |coordinateNoise P i ρ f x| ^ q) ≤
          P.expect (fun x => ρ * |f x| ^ q +
            (1 - ρ) * |P.condExp (Finset.univ.erase i) f x| ^ q) := by
        unfold FiniteProduct.expect
        apply Finset.sum_le_sum
        intro x _
        exact mul_le_mul_of_nonneg_left (hpoint x) (hmass x)
      _ = ρ * P.expect (fun x => |f x| ^ q) +
          (1 - ρ) * P.expect
            (fun x => |P.condExp (Finset.univ.erase i) f x| ^ q) := by
        simp only [FiniteProduct.expect, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ ≤ ρ * P.expect (fun x => |f x| ^ q) +
          (1 - ρ) * P.expect (fun x => |f x| ^ q) :=
        add_le_add_left
          (mul_le_mul_of_nonneg_left
            (condExp_moment_le P (Finset.univ.erase i) f q hq)
            (sub_nonneg.mpr hρ1)) _
      _ = P.expect (fun x => |f x| ^ q) := by ring
  unfold FiniteProduct.norm
  refine Real.rpow_le_rpow ?_ hmoment
    (one_div_nonneg.mpr (zero_le_one.trans hq))
  unfold FiniteProduct.expect
  exact Finset.sum_nonneg fun x _ =>
    mul_nonneg (hmass x) (Real.rpow_nonneg (abs_nonneg _) _)
)

/-- For every exponent `q > 1`, a positive rate depending only on `q` makes
negative noise in any single coordinate contractive in the finite-product
`Lᵠ` norm. At exponents four and four-thirds, the rate may be `2/5`.
[OD14, Prop. 9.19 (proof); Thm. 10.44 (proof)]
The bound extends to heterogeneous finite coordinate laws.

**Proof sketch.** For exponents at least two, use the centered negative
contraction bound. Below two, apply that bound at the conjugate exponent
and transfer contraction through finite weighted norm duality, using
self-adjointness of coordinate noise. Four-thirds is conjugate to four,
so both exceptional exponents admit the same specified rate. -/
private theorem coordinate_noise_negative_contraction_allq
    (q : ℝ) (hq : 1 < q) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ((q = 4 ∨ q = 4 / 3) → c = 2 / 5) ∧
      ∀ (n : ℕ) (P : FiniteProduct.{u} n) (i : Fin n) (f : P.Point → ℝ),
        P.norm q (coordinateNoise P i (-c) f) ≤ P.norm q f :=
  (by
  classical
  by_cases hq2 : 2 ≤ q
  · obtain ⟨c, hc0, hc1, hc4, hcontract⟩ :=
      coordinate_noise_negative_contraction q hq2
    refine ⟨c, hc0, hc1, ?_, hcontract⟩
    rintro (h4 | h43)
    · exact hc4 h4
    · exfalso
      linarith
  · let p : ℝ := q / (q - 1)
    have hp2 : 2 ≤ p := by
      dsimp only [p]
      apply (le_div_iff₀ (sub_pos.mpr hq)).2
      linarith
    obtain ⟨c, hc0, hc1, hc4, hcontract⟩ :=
      coordinate_noise_negative_contraction p hp2
    refine ⟨c, hc0, hc1, ?_, ?_⟩
    · rintro (h4 | h43)
      · exfalso
        linarith
      · apply hc4
        dsimp only [p]
        rw [h43]
        norm_num
    · intro n P i f
      unfold FiniteProduct.norm FiniteProduct.expect
      refine FiniteNorms.selfAdjoint_contraction P.mass
        (fun x => Finset.prod_nonneg fun j _ => (P.weight_pos j (x j)).le)
        (coordinateNoise P i (-c)) ?_ q hq ?_ f
      · intro g h
        simpa only [FiniteProduct.expect, mul_assoc] using
          coordinateNoise_selfAdjoint P i (-c) g h
      · intro g
        simpa only [FiniteProduct.norm, FiniteProduct.expect, p] using
          hcontract n P i g
)

/-- Partial anisotropic noise applies the specified rates to coordinates
in `J` and leaves every other coordinate at rate one.
[OD14, Def. 10.40; Thm. 10.44 (proof)] -/
private noncomputable def partialNoise {n : ℕ} (P : FiniteProduct.{u} n)
    (J : Finset (Fin n)) (r : Fin n → ℝ) (f : P.Point → ℝ)
    (x : P.Point) : ℝ :=
  ∑ S : Finset (Fin n), (∏ j ∈ S ∩ J, r j) * P.component S f x

/-- Adding a previously untreated coordinate to partial anisotropic noise
is equivalent to applying noise in that coordinate at its specified rate.
[OD14, Def. 10.40; Thm. 10.44 (proof)]
The identity holds for arbitrary real rates.

**Proof sketch.** Conditional expectation over the new coordinate retains
exactly the components whose index omits that coordinate. Coordinate noise
therefore multiplies the other components by the new rate. Splitting the
intersection product according to whether the component contains the new
coordinate gives precisely the partial-noise expansion on the enlarged set. -/
private theorem partialNoise_insert {n : ℕ} (P : FiniteProduct.{u} n)
    (J : Finset (Fin n)) (r : Fin n → ℝ) (f : P.Point → ℝ)
    (i : Fin n) (hi : i ∉ J) :
    partialNoise P (insert i J) r f =
      coordinateNoise P i (r i) (partialNoise P J r f) :=
  (by
  classical
  funext x
  have hcond :
      P.condExp (Finset.univ.erase i) (partialNoise P J r f) x =
        ∑ S : Finset (Fin n), (∏ j ∈ S ∩ J, r j) *
          (if i ∉ S then P.component S f x else 0) := by
    change P.expect (fun y => ∑ S : Finset (Fin n),
      (∏ j ∈ S ∩ J, r j) *
        P.component S f
          (fun j => if j ∈ Finset.univ.erase i then x j else y j)) = _
    rw [P.expect_sum_mul]
    change (∑ S : Finset (Fin n), (∏ j ∈ S ∩ J, r j) *
      P.condExp (Finset.univ.erase i) (P.component S f) x) = _
    simp only [condExp_component, Finset.subset_erase,
      Finset.subset_univ, true_and]
  simp only [coordinateNoise, FiniteProduct.laplacian, sub_sub_self]
  rw [hcond]
  simp only [partialNoise, ← Finset.sum_sub_distrib, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hiS : i ∈ S
  · have hiSJ : i ∉ S ∩ J := fun h => hi (Finset.mem_inter.mp h).2
    rw [Finset.inter_insert_of_mem hiS, Finset.prod_insert hiSJ]
    simp only [hiS, not_true_eq_false, if_false]
    ring
  · rw [Finset.inter_insert_of_notMem hiS]
    simp only [if_pos hiS]
    ring
)

/-- Coordinatewise norm contraction implies contraction of anisotropic noise
on the finite product. [OD14, Def. 10.40; Thm. 10.44 (proof)]
This algebraic implication permits any real exponent because the coordinate
norm inequalities are explicit hypotheses.

**Proof sketch.** Induct on the set of treated coordinates. With no coordinates
treated, component reconstruction gives the original function. Inserting a
new coordinate applies its noise operator, so its assumed contraction preserves
the bound. At the full coordinate set, partial noise equals anisotropic noise. -/
private theorem anisotropicNoise_norm_le_of_coordinate {n : ℕ}
    (P : FiniteProduct.{u} n) (q : ℝ) (r : Fin n → ℝ)
    (hcoordinate : ∀ (i : Fin n) (g : P.Point → ℝ),
      P.norm q (coordinateNoise P i (r i) g) ≤ P.norm q g)
    (f : P.Point → ℝ) :
    P.norm q (anisotropicNoise P r f) ≤ P.norm q f :=
  (by
  classical
  have hbound (J : Finset (Fin n)) :
      P.norm q (partialNoise P J r f) ≤ P.norm q f := by
    induction J using Finset.induction_on with
    | empty =>
        have hempty : partialNoise P ∅ r f = f := by
          funext x
          simpa only [partialNoise, Finset.inter_empty, Finset.prod_empty, one_mul] using
            component_reconstruction P f x
        exact le_of_eq (congrArg (P.norm q) hempty)
    | @insert i J hi ih =>
        rw [partialNoise_insert P J r f i hi]
        exact (hcoordinate i (partialNoise P J r f)).trans ih
  have hfull : partialNoise P Finset.univ r f = anisotropicNoise P r f := by
    funext x
    simp only [partialNoise, Finset.inter_univ, anisotropicNoise]
  simpa only [hfull] using hbound Finset.univ
)

/-- For every exponent `q > 1`, a positive rate depending only on `q` makes
anisotropic noise contractive in the finite-product `Lᵠ` norm when each
coordinate rate is independently chosen to be that rate or its negative.
At exponents four and four-thirds, the rate may be `2/5`.
[OD14, Thm. 10.44 (proof)]
This pointwise sign estimate precedes averaging over the random signs and
extends the source's homogeneous products to heterogeneous coordinate laws.

**Proof sketch.** Choose the rate from negative coordinate contraction.
Positive coordinate noise at that rate is also contractive. Apply the
coordinate operators successively: each step decreases the norm, and their
spectral multipliers combine into the anisotropic noise multiplier. -/
theorem signed_anisotropicNoise_contraction (q : ℝ) (hq : 1 < q) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ((q = 4 ∨ q = 4 / 3) → c = 2 / 5) ∧
      ∀ (n : ℕ) (P : FiniteProduct.{u} n) (r : BoolCube n) (f : P.Point → ℝ),
        P.norm q (anisotropicNoise P (fun i => c * boolToSign (r i)) f) ≤
          P.norm q f :=
  (by
  classical
  obtain ⟨c, hc0, hc1, hcspecial, hnegative⟩ :=
    coordinate_noise_negative_contraction_allq q hq
  refine ⟨c, hc0, hc1, hcspecial, ?_⟩
  intro n P r f
  refine anisotropicNoise_norm_le_of_coordinate P q
    (fun i => c * boolToSign (r i)) ?_ f
  intro i g
  cases hr : r i
  · simpa [hr, boolToSign] using
      coordinate_noise_positive_contraction P i c hc0.le hc1 g q hq.le
  · simpa [hr, boolToSign] using hnegative n P i g
)

end BooleanAnalysis.Hypercontractivity
