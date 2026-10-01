/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomizationDefs
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomVariablesBasic
import TCSlib.BooleanAnalysis.KKL
import TCSlib.BooleanAnalysis.LMN.DecisionTreeFourier

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Randomization and low-degree projections: statement skeletons

## Main definitions

The constructions live in `RandomizationDefs` and `RandomVariablesBasic`.

## Main results

* `randomization_norm_two`: Proposition 10.34.
* Theorem 10.35 is subsumed by the later contraction statements; see the derivation note
  below `randomized_noise_contraction`.
* `cube_lowDegree_projection`, `cube_lowDegree_projection_noise`: 10.37–10.38.
* `product_lowDegree_projection`: Theorem 10.39, independent of atom probabilities.
* `half_noise_norm_le_randomization`, `centered_negative_contraction`,
  `randomized_noise_contraction`: 10.42–10.44.

The constants precede all product spaces and dimensions. Heterogeneous products extend
the source's homogeneous presentation by the same coordinatewise argument.
Four Fourier and noise identities reuse existing proofs; the substantive inequalities
remain statement skeletons.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, §10.4, Remark 10.33 through Theorem 10.44.
-/

open MeasureTheory
open scoped BigOperators

namespace BooleanAnalysis.Hypercontractivity

universe u

/-- At a fixed product input, each Walsh coefficient of the randomization is the
corresponding orthogonal component. [OD14, Rem. 10.33]

**Proof sketch.** Expand the finite Walsh sum and use orthogonality of the characters. -/
theorem randomization_fourier_coefficient {n : ℕ} (P : FiniteProduct.{u} n)
    (f : P.Point → ℝ) (x : P.Point) (S : Finset (Fin n)) :
    fourierCoeff (fun r => randomization P f r x) S = P.component S f x := by
  simpa only [randomization, mul_comm] using
    (DecisionTree.fourierCoeff_sum_chiS (fun T => P.component T f x) S)

/-- Randomization preserves the second norm. [OD14, Prop. 10.34]

**Proof sketch.** Apply Parseval in the signs at each input, average over inputs, and
apply orthogonality of the product decomposition. -/
theorem randomization_norm_two {n : ℕ} (P : FiniteProduct.{u} n) (f : P.Point → ℝ) :
    randomizationNorm P 2 f = P.norm 2 f := sorry

/-- Cube projection to degree `k` costs at most `(√(q-1))^k` for `q≥2`, and its reciprocal
to the same power for `1<q≤2`. [OD14, Prop. 10.37]

**Proof sketch.** For `q≥2` use hypercontractivity, second-norm contractivity of projection,
and norm monotonicity. Apply self-adjointness and duality for exponents below two. -/
theorem cube_lowDegree_projection {n : ℕ} (g : BooleanFunc n) (k : ℕ)
    (q : ℝ) (hq : 1 < q) :
    (2 ≤ q → cubeLpNorm q (KKL.lowDegreePart g k) ≤
      Real.sqrt (q - 1) ^ k * cubeLpNorm q g) ∧
    (q ≤ 2 → cubeLpNorm q (KKL.lowDegreePart g k) ≤
      (1 / Real.sqrt (q - 1)) ^ k * cubeLpNorm q g) := sorry

/-- Cube projection to degree `k` has fourth norm at most `(√3/ρ)^k` times the fourth
norm of the `ρ`-noised function. [OD14, Lem. 10.38]

**Proof sketch.** Apply Bonami to the projection, compare its second-norm Fourier weights
with those of the noisy function, and increase the norm exponent from two to four. -/
theorem cube_lowDegree_projection_noise {n : ℕ} (g : BooleanFunc n) (k : ℕ)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    cubeLpNorm 4 (KKL.lowDegreePart g k) ≤
      (Real.sqrt 3 / ρ) ^ k * cubeLpNorm 4 (noiseOp ρ g) := sorry

/-- Low-degree projection on any finite product costs at most `C(q)^k` in `Lᵠ`, independently
of its smallest atom; `q=4,4/3` permit `C=5√3`. [OD14, Thm. 10.39]

**Proof sketch.** Randomize twice-noised functions, apply the cube projection bound at
each input, and undo randomization with `c=2/5`. Use the corresponding exponent bound and
duality for general `q`. -/
theorem product_lowDegree_projection (q : ℝ) (hq : 1 < q) :
    ∃ C : ℝ, 1 ≤ C ∧ ((q = 4 ∨ q = 4 / 3) → C = 5 * Real.sqrt 3) ∧
      ∀ (n : ℕ) (P : FiniteProduct.{u} n) (f : P.Point → ℝ) (k : ℕ),
        P.norm q (P.lowDegree k f) ≤ C ^ k * P.norm q f := sorry

/-- Randomization equals anisotropic noise at the independently chosen sign rates.
[OD14, Fact 10.41]

**Proof sketch.** Compare their orthogonal-component expansions term by term. -/
theorem randomization_eq_anisotropicNoise {n : ℕ} (P : FiniteProduct.{u} n)
    (f : P.Point → ℝ) (r : BoolCube n) (x : P.Point) :
    randomization P f r x = anisotropicNoise P (fun i => boolToSign (r i)) f x := by
  rfl

/-- Half-noising has no larger norm than randomizing at every exponent `q≥1`.
[OD14, Thm. 10.42]

**Proof sketch.** Iterate Lemma 10.15 over coordinates, commuting the averaging and
coordinate-noise operations and interchanging the finite expectations. -/
theorem half_noise_norm_le_randomization {n : ℕ} (P : FiniteProduct.{u} n)
    (f : P.Point → ℝ) (q : ℝ) (hq : 1 ≤ q) :
    P.norm q (P.noise (1 / 2) f) ≤ randomizationNorm P q f := sorry

/-- A sufficiently small negative multiple of any centered variable costs no more in
`Lᵠ` than the original positive multiple, uniformly in the translate; `q=4` permits `c=2/5`.
[OD14, Lem. 10.43]

**Proof sketch.** Bound the scalar remainder after removing the affine part, then integrate
using centering. For exponent four, expand and use a nonnegative quadratic estimate. -/
theorem centered_negative_contraction (q : ℝ) (hq : 2 ≤ q) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ (q = 4 → c = 2 / 5) ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : Ω → ℝ) (a : ℝ), MemLp X (ENNReal.ofReal q) μ →
        (∫ ω, X ω ∂μ) = 0 →
        rvLpNorm (fun ω => a - c * X ω) μ q ≤ rvLpNorm (fun ω => a + X ω) μ q := sorry

/-- A fixed amount of noise makes randomization contractive for every `q>1`; `q=4,4/3`
permit `c=2/5`. [OD14, Thm. 10.44]

**Proof sketch.** Lemma 10.43 makes negative coordinate noise contractive for `q≥2`;
positive noise is already contractive. Tensorize and use self-adjointness and duality
for conjugate exponents below two. -/
theorem randomized_noise_contraction (q : ℝ) (hq : 1 < q) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ((q = 4 ∨ q = 4 / 3) → c = 2 / 5) ∧
      ∀ (n : ℕ) (P : FiniteProduct.{u} n) (f : P.Point → ℝ),
        randomizationNorm P q (P.noise c f) ≤ P.norm q f := sorry

/-! The comparison in [OD14, Thm. 10.35] has no separate statement skeleton here.
Its lower bound follows from `half_noise_norm_le_randomization`. For the upper bound,
apply `randomized_noise_contraction` to the inverse-noised function `P.noise c⁻¹ f`.
Formalizing that corollary still requires the product-decomposition identity
`P.noise c (P.noise c⁻¹ f) = f` for nonzero `c`, which has not yet been proved. -/

/-- At each product input, the randomized second moment equals the sum of squared
orthogonal components. [OD14, Rem. 10.33]

**Proof sketch.** Apply cube Parseval with the component-as-coefficient identity. -/
theorem randomization_pointwise_parseval {n : ℕ} (P : FiniteProduct.{u} n)
    (f : P.Point → ℝ) (x : P.Point) :
    expect (fun r => randomization P f r x ^ 2) =
      ∑ S : Finset (Fin n), P.component S f x ^ 2 := by
  simpa only [innerProduct, ← pow_two, randomization_fourier_coefficient] using
    (parseval (fun r => randomization P f r x))

/-- Equal anisotropic noise rates recover the ordinary product noise operator.
[OD14, Def. 10.40]

**Proof sketch.** The product of a constant rate over a set is its cardinality power. -/
theorem anisotropicNoise_constant {n : ℕ} (P : FiniteProduct.{u} n)
    (ρ : ℝ) (f : P.Point → ℝ) (x : P.Point) :
    anisotropicNoise P (fun _ => ρ) f x = P.noise ρ f x := by
  simp only [anisotropicNoise, FiniteProduct.noise, Finset.prod_const]

end BooleanAnalysis.Hypercontractivity
