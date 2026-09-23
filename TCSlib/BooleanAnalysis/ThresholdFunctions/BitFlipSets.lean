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

lemma mem_fiber {π : Fin n → Fin m} {j : Fin m} {i : Fin n} : i ∈ fiber π j ↔ π i = j := by
  simp [fiber]

lemma flipSet_flipSet (x : BoolCube n) (S : Finset (Fin n)) : flipSet (flipSet x S) S = x := by
  funext i; by_cases h : i ∈ S <;> simp [flipSet, h]

lemma xorVec_xorVec (z c : BoolCube n) : xorVec (xorVec z c) c = z := by
  funext i; simp [xorVec]

lemma sum_comp_flipSet (F : BoolCube n → ℝ) (S : Finset (Fin n)) :
    ∑ x : BoolCube n, F (flipSet x S) = ∑ x : BoolCube n, F x :=
  Equiv.sum_comp
    (Function.Involutive.toPerm (fun x ↦ flipSet x S) (fun x ↦ flipSet_flipSet x S)) F

lemma sum_comp_xorVec (F : BoolCube n → ℝ) (c : BoolCube n) :
    ∑ z : BoolCube n, F (xorVec z c) = ∑ x : BoolCube n, F x :=
  Equiv.sum_comp
    (Function.Involutive.toPerm (fun z ↦ xorVec z c) (fun z ↦ xorVec_xorVec z c)) F

/-! ## The `S`-flip in the Walsh basis -/

lemma chiS_flipSet (T S : Finset (Fin n)) (x : BoolCube n) :
    chiS T (flipSet x S) = (-1 : ℝ) ^ (T ∩ S).card * chiS T x := by
  classical
  simp only [chiS]
  have h1 : ∀ i ∈ T, boolToSign (flipSet x S i)
      = (if i ∈ S then (-1 : ℝ) else 1) * boolToSign (x i) := by
    intro i _
    by_cases h : i ∈ S <;> simp [flipSet, h]
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite]
  simp [Finset.filter_mem_eq_inter]

lemma fourierCoeff_comp_flipSet (f : BooleanFunc n) (S T : Finset (Fin n)) :
    fourierCoeff (fun x ↦ f (flipSet x S)) T = (-1 : ℝ) ^ (T ∩ S).card * fourierCoeff f T := by
  have hsum : ∑ x : BoolCube n, f (flipSet x S) * chiS T x
      = (-1 : ℝ) ^ (T ∩ S).card * ∑ x : BoolCube n, f x * chiS T x := by
    have h := sum_comp_flipSet (fun y ↦ f y * chiS T (flipSet y S)) S
    simp only [flipSet_flipSet] at h
    rw [h]
    simp_rw [chiS_flipSet]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ ↦ by ring
  simp only [fourierCoeff, innerProduct, expect]
  rw [hsum]
  ring

lemma expect_mul_flipSet (f : BooleanFunc n) (S : Finset (Fin n)) :
    expect (fun x ↦ f x * f (flipSet x S))
      = ∑ T : Finset (Fin n), (-1 : ℝ) ^ (T ∩ S).card * fourierCoeff f T ^ 2 := by
  have h : expect (fun x ↦ f x * f (flipSet x S))
      = innerProduct f (fun x ↦ f (flipSet x S)) := rfl
  rw [h, plancherel]
  refine Finset.sum_congr rfl fun T _ ↦ ?_
  rw [fourierCoeff_comp_flipSet]
  ring

/-! ## Disagreement under an `S`-flip -/

/-- The probability that flipping the coordinates in `S` changes the value of `f`. -/
noncomputable def flipDisagreement (f : BooleanFunc n) (S : Finset (Fin n)) : ℝ :=
  expect (fun x ↦ (f x - f (flipSet x S)) ^ 2 / 4)

lemma flipDisagreement_eq {f : BooleanFunc n} (hf : isPmOne f) (S : Finset (Fin n)) :
    flipDisagreement f S
      = (1 - ∑ T : Finset (Fin n), (-1 : ℝ) ^ (T ∩ S).card * fourierCoeff f T ^ 2) / 2 := by
  have hpt : ∀ x : BoolCube n, (f x - f (flipSet x S)) ^ 2 / 4
      = (1 - f x * f (flipSet x S)) / 2 := by
    intro x
    rcases hf x with h1 | h1 <;> rcases hf (flipSet x S) with h2 | h2 <;>
      rw [h1, h2] <;> norm_num
  unfold flipDisagreement
  rw [show (fun x : BoolCube n ↦ (f x - f (flipSet x S)) ^ 2 / 4)
      = fun x ↦ (1 - f x * f (flipSet x S)) / 2 from funext hpt, ← expect_mul_flipSet]
  simp only [expect, uniformWeight]
  have hsum : ∑ x : BoolCube n, (1 - f x * f (flipSet x S)) / 2
      = ((2 : ℝ) ^ n - ∑ x : BoolCube n, f x * f (flipSet x S)) / 2 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp
  rw [hsum]
  have h2 : (2 : ℝ)⁻¹ ^ n * (2 : ℝ) ^ n = 1 := by
    rw [← mul_pow]; norm_num
  linear_combination h2 / 2

/-! ## Averaging over a random colouring of the coordinates -/

lemma prod_form (j₀ : Fin m) (T : Finset (Fin n)) (π : Fin n → Fin m) :
    (-1 : ℝ) ^ (T ∩ fiber π j₀).card
      = ∏ i : Fin n, (if i ∈ T then (if π i = j₀ then (-1 : ℝ) else 1) else 1) := by
  classical
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, mul_one, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 2
  ext i
  simp [fiber]

/-- For a uniformly random colouring `π` of the `n` coordinates by `m` blocks, the average of
`(-1)^|T ∩ π⁻¹(j₀)|` equals `(1 - 2/m)^|T|`. -/
lemma sum_pi_sign (hm : 0 < m) (j₀ : Fin m) (T : Finset (Fin n)) :
    ∑ π : Fin n → Fin m, (-1 : ℝ) ^ (T ∩ fiber π j₀).card
      = (m : ℝ) ^ n * (1 - 2 / (m : ℝ)) ^ T.card := by
  classical
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  simp_rw [prod_form]
  rw [← Fintype.piFinset_univ,
    ← Finset.prod_univ_sum (fun _ : Fin n ↦ (Finset.univ : Finset (Fin m)))
      (fun (i : Fin n) (j : Fin m) ↦ if i ∈ T then (if j = j₀ then (-1 : ℝ) else 1) else 1)]
  have hstep : ∀ i : Fin n,
      (∑ j : Fin m, (if i ∈ T then (if j = j₀ then (-1 : ℝ) else 1) else 1))
        = (m : ℝ) * (if i ∈ T then (1 : ℝ) - 2 / (m : ℝ) else 1) := by
    intro i
    by_cases h : i ∈ T
    · simp only [h, if_true]
      have hsplit : ∀ j : Fin m,
          (if j = j₀ then (-1 : ℝ) else 1) = 1 + (if j = j₀ then (-2 : ℝ) else 0) := by
        intro j; split_ifs <;> norm_num
      rw [Finset.sum_congr rfl (fun j _ ↦ hsplit j), Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ j₀ (fun _ ↦ (-2 : ℝ))]
      simp only [Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
      field_simp
      ring
    · simp [h, Finset.card_univ]
  rw [Finset.prod_congr rfl (fun i _ ↦ hstep i), Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [Finset.prod_ite]
  simp [Finset.filter_mem_eq_inter]

end ThresholdFunctions
end BooleanAnalysis
