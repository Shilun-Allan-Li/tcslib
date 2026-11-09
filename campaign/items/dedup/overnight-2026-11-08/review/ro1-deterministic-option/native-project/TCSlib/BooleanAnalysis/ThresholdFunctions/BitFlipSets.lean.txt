import TCSlib.BooleanAnalysis.ThresholdFunctions.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Flipping a set of coordinates

This file collects the combinatorial and Fourier-analytic tools used by the random-partition proof
of the influence-to-noise reduction (O'Donnell, Theorem 5.35): flipping all coordinates in a set
`S`, the associated disagreement probability, and the averaging identity for a uniformly random
partition of the coordinates into blocks.

## Main definitions

* `flipSet x S`: negate exactly the coordinates of `x` lying in `S`.
* `xorVec z c`: coordinatewise exclusive-or.
* `fiber π j`: the block `π⁻¹(j)` of a colouring `π`.
* `flipDisagreement f S`: the probability that flipping the coordinates in `S` changes `f`.

## Main results

* `chiS_flipSet` and `fourierCoeff_comp_flipSet`: the effect of an `S`-flip on the Walsh basis.
* `flipDisagreement_eq`: the Fourier formula for the disagreement probability.
* `sum_pi_sign`: for a uniformly random colouring `π` of the coordinates by `m` blocks, the average
  of `(-1)^|T ∩ π⁻¹(j₀)|` is `(1 - 2/m)^|T|`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  arXiv edition, 2021, §5.5.
-/

open scoped BigOperators

namespace BooleanAnalysis
namespace ThresholdFunctions

variable {n m : ℕ}

/-! ## Flipping a set of coordinates -/

/-- Negate exactly the coordinates of `x` that lie in `S`. -/
def flipSet (x : BoolCube n) (S : Finset (Fin n)) : BoolCube n :=
  fun i ↦ if i ∈ S then !x i else x i

/-- Coordinatewise exclusive-or of two points of the cube. -/
def xorVec (z c : BoolCube n) : BoolCube n := fun i ↦ xor (z i) (c i)

/-- The block `π⁻¹(j)` of a colouring of the coordinates. -/
noncomputable def fiber (π : Fin n → Fin m) (j : Fin m) : Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ π i = j)

/-- A coordinate lies in the block `π⁻¹(j)` exactly when its colour is `j`. -/
lemma mem_fiber {π : Fin n → Fin m} {j : Fin m} {i : Fin n} : i ∈ fiber π j ↔ π i = j := by
  simp [fiber]

/-- Flipping every coordinate is the antipodal map. -/
@[simp]
lemma flipSet_univ (x : BoolCube n) : flipSet x Finset.univ = fun i ↦ !x i := by
  funext i; simp [flipSet]

/-- Flipping the same set of coordinates twice is the identity. -/
@[simp]
lemma flipSet_flipSet (x : BoolCube n) (S : Finset (Fin n)) : flipSet (flipSet x S) S = x := by
  funext i; by_cases h : i ∈ S <;> simp [flipSet, h]

/-- Exclusive-or with a fixed point is an involution. -/
@[simp]
lemma xorVec_xorVec (z c : BoolCube n) : xorVec (xorVec z c) c = z := by
  funext i; simp [xorVec]

/-- Flipping a fixed set of coordinates permutes the cube, so it preserves sums. -/
lemma sum_comp_flipSet (F : BoolCube n → ℝ) (S : Finset (Fin n)) :
    ∑ x : BoolCube n, F (flipSet x S) = ∑ x : BoolCube n, F x :=
  Equiv.sum_comp
    (Function.Involutive.toPerm (fun x ↦ flipSet x S) (fun x ↦ flipSet_flipSet x S)) F

/-- Exclusive-or with a fixed point permutes the cube, so it preserves sums. -/
lemma sum_comp_xorVec (F : BoolCube n → ℝ) (c : BoolCube n) :
    ∑ z : BoolCube n, F (xorVec z c) = ∑ x : BoolCube n, F x :=
  Equiv.sum_comp
    (Function.Involutive.toPerm (fun z ↦ xorVec z c) (fun z ↦ xorVec_xorVec z c)) F

/-! ## The `S`-flip in the Walsh basis -/

/-- Flipping the coordinates in `S` multiplies the Walsh character `χ_T` by `(-1)^|T ∩ S|`. -/
lemma chiS_flipSet (T S : Finset (Fin n)) (x : BoolCube n) :
    chiS T (flipSet x S) = (-1 : ℝ) ^ (T ∩ S).card * chiS T x := by
  classical
  have h1 : ∀ i ∈ T, boolToSign (flipSet x S i)
      = (if i ∈ S then (-1 : ℝ) else 1) * boolToSign (x i) := by
    intro i _
    by_cases h : i ∈ S <;> simp [flipSet, h]
  rw [chiS, chiS, Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_ite]
  simp [Finset.filter_mem_eq_inter]

/-- Flipping the coordinates in `S` multiplies the Fourier coefficient `f̂(T)` by
`(-1)^|T ∩ S|`. -/
lemma fourierCoeff_comp_flipSet (f : BooleanFunc n) (S T : Finset (Fin n)) :
    fourierCoeff (fun x ↦ f (flipSet x S)) T = (-1 : ℝ) ^ (T ∩ S).card * fourierCoeff f T := by
  have h := sum_comp_flipSet (fun y ↦ f y * chiS T (flipSet y S)) S
  simp only [flipSet_flipSet, chiS_flipSet] at h
  simp only [fourierCoeff, innerProduct, expect, h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ ↦ by ring

/-- The correlation of `f` with its `S`-flip, expanded in the Fourier basis. -/
lemma expect_mul_flipSet (f : BooleanFunc n) (S : Finset (Fin n)) :
    expect (fun x ↦ f x * f (flipSet x S))
      = ∑ T : Finset (Fin n), (-1 : ℝ) ^ (T ∩ S).card * fourierCoeff f T ^ 2 := by
  change innerProduct f (fun x ↦ f (flipSet x S)) = _
  rw [plancherel]
  refine Finset.sum_congr rfl fun T _ ↦ ?_
  rw [fourierCoeff_comp_flipSet]
  ring

/-! ## Disagreement under an `S`-flip -/

/-- The probability that flipping the coordinates in `S` changes the value of `f`. -/
noncomputable def flipDisagreement (f : BooleanFunc n) (S : Finset (Fin n)) : ℝ :=
  expect (fun x ↦ (f x - f (flipSet x S)) ^ 2 / 4)

/-- For a `±1`-valued function, the `S`-flip disagreement probability is
`(1 - ∑_T (-1)^|T ∩ S| f̂(T)²) / 2`. -/
lemma flipDisagreement_eq {f : BooleanFunc n} (hf : isPmOne f) (S : Finset (Fin n)) :
    flipDisagreement f S
      = (1 - ∑ T : Finset (Fin n), (-1 : ℝ) ^ (T ∩ S).card * fourierCoeff f T ^ 2) / 2 := by
  have hpt : (fun x ↦ (f x - f (flipSet x S)) ^ 2 / 4)
      = fun x ↦ 2⁻¹ + (-2⁻¹) * (f x * f (flipSet x S)) := by
    funext x
    rcases hf x with h1 | h1 <;> rcases hf (flipSet x S) with h2 | h2 <;>
      rw [h1, h2] <;> norm_num
  rw [flipDisagreement, hpt, expect_add, expect_const, expect_const_mul, expect_mul_flipSet]
  ring

/-! ## Averaging over a random colouring of the coordinates -/

/-- The sign `(-1)^|T ∩ π⁻¹(j₀)|` as a product of one factor per coordinate. -/
private lemma neg_one_pow_card_inter_fiber (j₀ : Fin m) (T : Finset (Fin n))
    (π : Fin n → Fin m) :
    (-1 : ℝ) ^ (T ∩ fiber π j₀).card
      = ∏ i : Fin n, (if i ∈ T then (if π i = j₀ then (-1 : ℝ) else 1) else 1) := by
  classical
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.filter_mem_eq_inter,
    Finset.univ_inter, Finset.prod_ite]
  simp only [Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 2
  ext i
  simp [fiber]

/-- For a uniformly random colouring `π` of the `n` coordinates by `m` blocks, the average of
`(-1)^|T ∩ π⁻¹(j₀)|` equals `(1 - 2/m)^|T|`.

**Proof sketch.** The sign is a product of independent per-coordinate factors, so the sum over all
colourings factors as a product over coordinates. A coordinate outside `T` contributes `m`, and a
coordinate in `T` contributes `(m - 1) - 1 = m (1 - 2/m)`. -/
lemma sum_pi_sign (hm : 0 < m) (j₀ : Fin m) (T : Finset (Fin n)) :
    ∑ π : Fin n → Fin m, (-1 : ℝ) ^ (T ∩ fiber π j₀).card
      = (m : ℝ) ^ n * (1 - 2 / (m : ℝ)) ^ T.card := by
  classical
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  simp_rw [neg_one_pow_card_inter_fiber]
  rw [← Fintype.piFinset_univ,
    ← Finset.prod_univ_sum (fun _ : Fin n ↦ (Finset.univ : Finset (Fin m)))
      (fun (i : Fin n) (j : Fin m) ↦ if i ∈ T then (if j = j₀ then (-1 : ℝ) else 1) else 1)]
  -- Each coordinate contributes a factor `m` or `m (1 - 2/m)`.
  have hstep (i : Fin n) :
      (∑ j : Fin m, (if i ∈ T then (if j = j₀ then (-1 : ℝ) else 1) else 1))
        = (m : ℝ) * (if i ∈ T then (1 : ℝ) - 2 / (m : ℝ) else 1) := by
    by_cases h : i ∈ T
    · have hsplit (j : Fin m) :
          (if j = j₀ then (-1 : ℝ) else 1) = 1 + (if j = j₀ then (-2 : ℝ) else 0) := by
        split_ifs <;> norm_num
      simp only [h, if_true, hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
      field_simp
      ring
    · simp [h]
  rw [Finset.prod_congr rfl (fun i _ ↦ hstep i), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Finset.prod_ite]
  simp [Finset.filter_mem_eq_inter]

end ThresholdFunctions
end BooleanAnalysis
