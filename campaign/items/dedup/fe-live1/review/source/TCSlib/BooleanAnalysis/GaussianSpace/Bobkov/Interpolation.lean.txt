/-
Copyright (c) 2026 TCSlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/

import TCSlib.BooleanAnalysis.GaussianSpace.Bobkov.Cube
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Symmetric interpolation for Bobkov's inequality

## Main definitions

* `BobkovInterpolation.pairLength`: the average of two symmetrically varying lengths.

## Main results

The scalar two-point inequality extends to contractions of symmetric pairs carrying
arbitrary extra Euclidean coordinates. The proof uses a bounded-supremum maximum
principle, a deterministic version of the stopped-walk argument.
The statement is generalized from the Gaussian profile to any continuous,
nonnegative profile satisfying the scalar two-point inequality.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press,
  2014; May 2021 arXiv edition, §11.4, Theorem 11.55 and Exercise 11.24.
-/

open scoped BigOperators Topology
open Set Filter

namespace BooleanAnalysis.GaussianSpace.BobkovInterpolation

/-- The average length of the profile coordinate and a finite vector at two
symmetrically displaced probabilities, with an additional squared length `c`.
[OD14, §11.4, Exercise 11.24]
This packages the auxiliary coordinates in the interpolation proof. -/
noncomputable def pairLength {m : ℕ} (P : ℝ → ℝ) (a b : ℝ) (u v : Fin m → ℝ)
    (t c : ℝ) : ℝ :=
  (Real.sqrt (P (a + t * b) ^ 2 + c + ∑ j, (u j + t * v j) ^ 2) +
    Real.sqrt (P (a - t * b) ^ 2 + c + ∑ j, (u j - t * v j) ^ 2)) / 2

/-- The difference between a symmetric length and the endpoint length with the
remaining squared displacement transferred to the clock. -/
noncomputable def pairDeficit {m : ℕ} (P : ℝ → ℝ) (a b : ℝ) (u v : Fin m → ℝ)
    (t c : ℝ) : ℝ :=
  pairLength P a b u v t c - pairLength P a b u v 1 (c + b ^ 2 * (1 - t ^ 2))

/-- A bounded-above function which can improve by a factor of two at every
point of a set is nonpositive throughout that set.

**Proof sketch.** The supremum is at most half itself, hence is nonpositive. -/
private lemma nonpos_of_bddAbove_of_half_step {α : Type*} {s : Set α} {f : α → ℝ}
    (hb : BddAbove (f '' s))
    (hstep : ∀ x ∈ s, ∃ y ∈ s, f x ≤ f y / 2) :
    ∀ x ∈ s, f x ≤ 0 := by
  intro x hx
  have hne : (f '' s).Nonempty := ⟨f x, x, hx, rfl⟩
  have hsup : sSup (f '' s) ≤ sSup (f '' s) / 2 := by
    apply csSup_le hne
    rintro z ⟨a, ha, rfl⟩
    obtain ⟨b, hbs, hab⟩ := hstep a ha
    exact hab.trans (div_le_div_of_nonneg_right (le_csSup hb ⟨b, hbs, rfl⟩) zero_le_two)
  exact (le_csSup hb ⟨x, hx, rfl⟩).trans (by linarith)

private lemma sqrt_add_le_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  apply (Real.sqrt_le_left
    (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy,
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

/-- Negating a symmetric displacement exchanges the two length terms. -/
lemma pairLength_neg {m : ℕ} (P : ℝ → ℝ) (a b : ℝ) (u v : Fin m → ℝ) (t c : ℝ) :
    pairLength P a b u v (-t) c = pairLength P a b u v t c := by
  simp only [pairLength, neg_mul, ← sub_eq_add_neg, sub_neg_eq_add, add_comm]

/-- A symmetric length depends only on the absolute displacement. -/
lemma pairLength_abs {m : ℕ} (P : ℝ → ℝ) (a b : ℝ) (u v : Fin m → ℝ) (t c : ℝ) :
    pairLength P a b u v |t| c = pairLength P a b u v t c := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht, pairLength_neg]

/-- Every point between two symmetric probability endpoints is a probability. -/
lemma probability_mem {a b t : ℝ} (hp : a + b ∈ Icc (0 : ℝ) 1)
    (hm : a - b ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (-1 : ℝ) 1) :
    a + t * b ∈ Icc (0 : ℝ) 1 := by
  convert (convex_Icc (0 : ℝ) 1) hp hm
    (show 0 ≤ (1 + t) / 2 by linarith [ht.1])
    (show 0 ≤ (1 - t) / 2 by linarith [ht.2]) (show (1 + t) / 2 + (1 - t) / 2 = 1 by ring) using 1
  simp only [smul_eq_mul]
  ring

/-- At the endpoint displacement, the symmetric length is concave in the
additional squared length.

**Proof sketch.** Each summand is the concave square-root function translated
by a nonnegative squared length. Their average is concave as well. -/
lemma concaveOn_pairLength_clock {m : ℕ} (P : ℝ → ℝ) (a b : ℝ)
    (u v : Fin m → ℝ) :
    ConcaveOn ℝ (Set.Ici 0) (fun c => pairLength P a b u v 1 c) := by
  have hK (K : ℝ) (hK : 0 ≤ K) :
      ConcaveOn ℝ (Set.Ici 0) (fun c => Real.sqrt (K + c)) := by
    refine ⟨convex_Ici 0, ?_⟩
    intro x hx y hy α β hα hβ hsum
    have h := Real.strictConcaveOn_sqrt.concaveOn.2
      (show K + x ∈ Set.Ici 0 from add_nonneg hK hx)
      (show K + y ∈ Set.Ici 0 from add_nonneg hK hy) hα hβ hsum
    simp only [smul_eq_mul] at h ⊢
    convert h using 1
    congr 1
    nlinarith [hsum]
  have h := ((hK (P (a + b) ^ 2 + ∑ j, (u j + v j) ^ 2) (by positivity)).add
    (hK (P (a - b) ^ 2 + ∑ j, (u j - v j) ^ 2) (by positivity))).smul
      (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  convert h using 1
  funext c
  simp only [pairLength, one_mul, Pi.add_apply, smul_eq_mul]
  ring_nf

/-- With a continuous probability profile, symmetric lengths vary continuously
with a displacement in the unit interval. -/
lemma continuousOn_pairLength_zero {m : ℕ} {P : ℝ → ℝ} (hP : ContinuousOn P (Icc (0 : ℝ) 1))
    {a b : ℝ} (hp : a + b ∈ Icc (0 : ℝ) 1) (hm : a - b ∈ Icc (0 : ℝ) 1)
    (u v : Fin m → ℝ) :
    ContinuousOn (fun t => pairLength P a b u v t 0) (Icc (0 : ℝ) 1) := by
  have hplus : ContinuousOn (fun t : ℝ => P (a + t * b)) (Icc (0 : ℝ) 1) :=
    hP.comp (by fun_prop) (fun t ht => probability_mem hp hm ⟨by linarith [ht.1], ht.2⟩)
  have hminus : ContinuousOn (fun t : ℝ => P (a - t * b)) (Icc (0 : ℝ) 1) := by
    apply hP.comp (by fun_prop)
    intro t ht
    simpa only [neg_mul, ← sub_eq_add_neg] using
      probability_mem hp hm (t := -t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  unfold pairLength
  exact ((((hplus.pow 2).add continuousOn_const).add (by fun_prop)).sqrt.add
    (((hminus.pow 2).add continuousOn_const).add (by fun_prop)).sqrt).div_const 2

/-- Adding a squared clock coordinate increases a symmetric length by at most
the square root of that coordinate. -/
lemma pairLength_clock_le {m : ℕ} (P : ℝ → ℝ) (a b : ℝ) (u v : Fin m → ℝ)
    (t : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    pairLength P a b u v t c ≤ Real.sqrt c + pairLength P a b u v t 0 := by
  have hp := sqrt_add_le_add_sqrt hc
    (show 0 ≤ P (a + t * b) ^ 2 + ∑ j, (u j + t * v j) ^ 2 by positivity)
  have hm := sqrt_add_le_add_sqrt hc
    (show 0 ≤ P (a - t * b) ^ 2 + ∑ j, (u j - t * v j) ^ 2 by positivity)
  unfold pairLength
  simp only [add_zero, add_assoc, add_comm] at hp hm ⊢
  linarith

/-- The two-point inequality bounds a symmetric length by the average of an
endpoint length and a new symmetric length, adding the squared step to the clock.
[OD14, §11.4, Exercise 11.24]

**Proof sketch.** At each of the two centers, use a step that reaches one
endpoint of the probability segment. Carry the clock and the affine vector
coordinates by the Euclidean triangle inequality, then average both bounds. -/
lemma pairLength_adaptive_midpoint {m : ℕ} (P : ℝ → ℝ)
    (hP : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ P x)
    (htwo : ∀ a b : ℝ, a + b ∈ Icc (0 : ℝ) 1 → a - b ∈ Icc (0 : ℝ) 1 →
      P a ≤ (Real.sqrt (P (a + b) ^ 2 + b ^ 2) +
        Real.sqrt (P (a - b) ^ 2 + b ^ 2)) / 2)
    {a b t c : ℝ} (u v : Fin m → ℝ)
    (hplus : a + b ∈ Icc (0 : ℝ) 1) (hminus : a - b ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hc : 0 ≤ c) :
    pairLength P a b u v t c ≤
      (pairLength P a b u v 1 (c + ((1 - t) * b) ^ 2) +
        pairLength P a b u v (2 * t - 1) (c + ((1 - t) * b) ^ 2)) / 2 := by
  -- Carry the fixed clock as one more Euclidean coordinate.
  have hcarry (z d : ℝ) (w e : Fin m → ℝ)
      (hp : z + d ∈ Icc (0 : ℝ) 1) (hm : z - d ∈ Icc (0 : ℝ) 1) :
      Real.sqrt (P z ^ 2 + c + ∑ j, w j ^ 2) ≤
        (Real.sqrt (P (z + d) ^ 2 + c + d ^ 2 + ∑ j, (w j + e j) ^ 2) +
          Real.sqrt (P (z - d) ^ 2 + c + d ^ 2 + ∑ j, (w j - e j) ^ 2)) / 2 := by
    have hz : z ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [hp.1, hm.1], by linarith [hp.2, hm.2]⟩
    have h := carried_midpoint (Fin.cons (Real.sqrt c) w) (Fin.cons 0 e)
      (P z) (Real.sqrt (P (z + d) ^ 2 + d ^ 2))
      (Real.sqrt (P (z - d) ^ 2 + d ^ 2)) (hP z hz) (htwo z d hp hm)
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_zero, sub_zero,
      Real.sq_sqrt hc] at h
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at h
    simpa only [add_assoc, add_left_comm, add_comm] using h
  have hp := hcarry (a + t * b) ((1 - t) * b)
    (fun j => u j + t * v j) (fun j => (1 - t) * v j)
    (by convert hplus using 1; ring)
    (by
      convert probability_mem hplus hminus (t := 2 * t - 1)
        ⟨by linarith [ht.1], by linarith [ht.2]⟩ using 1
      ring)
  have hm := hcarry (a - t * b) ((1 - t) * b)
    (fun j => u j - t * v j) (fun j => (1 - t) * v j)
    (by
      convert probability_mem hplus hminus (t := -(2 * t - 1))
        ⟨by linarith [ht.2], by linarith [ht.1]⟩ using 1
      ring)
    (by convert hminus using 1; ring)
  dsimp [pairLength]
  ring_nf at hp hm ⊢
  linarith

/-- Every symmetric length dominates the length of its clock coordinate. -/
lemma sqrt_clock_le_pairLength {m : ℕ} (P : ℝ → ℝ) (a b : ℝ) (u v : Fin m → ℝ)
    (t c : ℝ) : Real.sqrt c ≤ pairLength P a b u v t c := by
  have hp := Real.sqrt_le_sqrt (show c ≤ P (a + t * b) ^ 2 + c + ∑ j, (u j + t * v j) ^ 2 by
    nlinarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (u j + t * v j))])
  have hm := Real.sqrt_le_sqrt (show c ≤ P (a - t * b) ^ 2 + c + ∑ j, (u j - t * v j) ^ 2 by
    nlinarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg (u j - t * v j))])
  unfold pairLength
  linarith

/-- The interpolation deficit is uniformly bounded above, including over the
unbounded nonnegative clock coordinate.

**Proof sketch.** The square root of the clock bounds its contribution to the
first length from above and the endpoint length from below. What remains is
bounded by continuity of the zero-clock length on the compact unit interval. -/
lemma bddAbove_pairDeficit {m : ℕ} {P : ℝ → ℝ}
    (hP : ContinuousOn P (Set.Icc (0 : ℝ) 1))
    {a b : ℝ} (hp : a + b ∈ Set.Icc (0 : ℝ) 1)
    (hm : a - b ∈ Set.Icc (0 : ℝ) 1) (u v : Fin m → ℝ) :
    BddAbove ((fun s : ℝ × ℝ => pairDeficit P a b u v s.1 s.2) ''
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Ici (0 : ℝ))) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image
    (continuousOn_pairLength_zero hP hp hm u v)
  refine ⟨M, ?_⟩
  rintro y ⟨⟨t, c⟩, ⟨ht, hc⟩, rfl⟩
  have hq : c ≤ c + b ^ 2 * (1 - t ^ 2) :=
    le_add_of_nonneg_right (mul_nonneg (sq_nonneg b) (by nlinarith [ht.1, ht.2]))
  have hlow := (Real.sqrt_le_sqrt hq).trans
    (sqrt_clock_le_pairLength P a b u v 1 (c + b ^ 2 * (1 - t ^ 2)))
  have hupp := pairLength_clock_le P a b u v t hc
  have hbound := hM ⟨t, ht, rfl⟩
  dsimp [pairDeficit]
  linarith

/-- An adaptive midpoint step bounds the current interpolation deficit by half
the next deficit. [OD14, §11.4, Exercise 11.24]

**Proof sketch.** The step reaches an endpoint in one branch. The remaining
variance averaged over both branches equals the old remaining variance.
Concavity of the endpoint length in its clock absorbs that averaging. -/
lemma pairDeficit_half_step {m : ℕ} (P : ℝ → ℝ)
    (hP : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ P x)
    (htwo : ∀ a b : ℝ, a + b ∈ Icc (0 : ℝ) 1 → a - b ∈ Icc (0 : ℝ) 1 →
      P a ≤ (Real.sqrt (P (a + b) ^ 2 + b ^ 2) +
        Real.sqrt (P (a - b) ^ 2 + b ^ 2)) / 2)
    {a b t c : ℝ} (u v : Fin m → ℝ)
    (hplus : a + b ∈ Icc (0 : ℝ) 1) (hminus : a - b ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hc : 0 ≤ c) :
    pairDeficit P a b u v t c ≤
      pairDeficit P a b u v |2 * t - 1| (c + ((1 - t) * b) ^ 2) / 2 := by
  have hclock : 0 ≤ c + ((1 - t) * b) ^ 2 := add_nonneg hc (sq_nonneg _)
  have hvariance : 0 ≤ b ^ 2 * (1 - (2 * t - 1) ^ 2) :=
    mul_nonneg (sq_nonneg b) (by nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)])
  have hconc := (concaveOn_pairLength_clock P a b u v).2
    hclock (add_nonneg hclock hvariance)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul] at hconc
  have hmidpoint :
      (1 / 2 : ℝ) * (c + ((1 - t) * b) ^ 2) +
        (1 / 2 : ℝ) * (c + ((1 - t) * b) ^ 2 + b ^ 2 * (1 - (2 * t - 1) ^ 2)) =
          c + b ^ 2 * (1 - t ^ 2) := by ring
  rw [hmidpoint] at hconc
  have hstep := pairLength_adaptive_midpoint P hP htwo u v hplus hminus ht hc
  simp only [pairDeficit, pairLength_abs, sq_abs]
  linarith

/-- A continuous nonnegative profile satisfying the two-point inequality obeys
the symmetric endpoint comparison with arbitrary carried Euclidean coordinates.
[OD14, §11.4, Theorem 11.55 (proof mechanism)]

**Proof sketch.** The deficit is bounded above and every adaptive step bounds
it by half another deficit in the same domain. The supremum maximum principle
therefore makes every deficit nonpositive. This is a deterministic reformulation
of the stopped-walk argument, without a stochastic-process construction. -/
lemma pairLength_le_endpoint {m : ℕ} {P : ℝ → ℝ}
    (hcont : ContinuousOn P (Icc (0 : ℝ) 1))
    (hP : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ P x)
    (htwo : ∀ a b : ℝ, a + b ∈ Icc (0 : ℝ) 1 → a - b ∈ Icc (0 : ℝ) 1 →
      P a ≤ (Real.sqrt (P (a + b) ^ 2 + b ^ 2) +
        Real.sqrt (P (a - b) ^ 2 + b ^ 2)) / 2)
    {a b t c : ℝ} (u v : Fin m → ℝ)
    (hp : a + b ∈ Icc (0 : ℝ) 1) (hm : a - b ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (hc : 0 ≤ c) :
    pairLength P a b u v t c ≤ pairLength P a b u v 1 (c + b ^ 2 * (1 - t ^ 2)) := by
  have hnonpos := nonpos_of_bddAbove_of_half_step (bddAbove_pairDeficit hcont hp hm u v)
    (f := fun s : ℝ × ℝ => pairDeficit P a b u v s.1 s.2) ?_ (t, c) ⟨ht, hc⟩
  · exact sub_nonpos.mp hnonpos
  · rintro ⟨r, d⟩ ⟨hr, hd⟩
    change r ∈ Icc (0 : ℝ) 1 at hr
    change 0 ≤ d at hd
    refine ⟨(|2 * r - 1|, d + ((1 - r) * b) ^ 2), ?_, ?_⟩
    · change |2 * r - 1| ∈ Icc (0 : ℝ) 1 ∧ 0 ≤ d + ((1 - r) * b) ^ 2
      exact ⟨⟨abs_nonneg _, abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩⟩,
        add_nonneg hd (sq_nonneg _)⟩
    · exact pairDeficit_half_step P hP htwo u v hp hm hr hd

/-- Contracting a symmetric pair and its discrete derivative decreases its
average length, even with arbitrary carried Euclidean coordinates.
[OD14, Theorem 11.55, Exercise 11.24]

**Proof sketch.** Apply the endpoint comparison with initial clock `(t b)²`.
The remaining squared displacement makes the endpoint clock exactly `b²`. -/
lemma pairLength_contraction {m : ℕ} {P : ℝ → ℝ}
    (hcont : ContinuousOn P (Icc (0 : ℝ) 1))
    (hP : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ P x)
    (htwo : ∀ a b : ℝ, a + b ∈ Icc (0 : ℝ) 1 → a - b ∈ Icc (0 : ℝ) 1 →
      P a ≤ (Real.sqrt (P (a + b) ^ 2 + b ^ 2) +
        Real.sqrt (P (a - b) ^ 2 + b ^ 2)) / 2)
    {a b t : ℝ} (u v : Fin m → ℝ)
    (hp : a + b ∈ Icc (0 : ℝ) 1) (hm : a - b ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    pairLength P a b u v t ((t * b) ^ 2) ≤ pairLength P a b u v 1 (b ^ 2) := by
  convert pairLength_le_endpoint hcont hP htwo u v hp hm ht (sq_nonneg (t * b)) using 1
  congr 1
  ring

end BooleanAnalysis.GaussianSpace.BobkovInterpolation
