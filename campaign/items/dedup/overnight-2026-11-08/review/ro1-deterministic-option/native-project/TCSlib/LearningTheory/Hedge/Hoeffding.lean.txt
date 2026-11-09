/-
Copyright (c) 2026 Arhaan Aggarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arhaan Aggarwal
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hoeffding's Lemma and Log-MGF Bound

Hoeffding's lemma in the form needed by the Hedge analysis: for a probability vector `p`
and losses `ℓᵢ ∈ [0,1]`, the log-moment generating function `ln Σ pᵢ e^{-ηℓᵢ}` of the loss
of a randomly drawn expert is at most `-η·L + η²/8`, where `L = Σ pᵢ ℓᵢ` is the mean.  The
core is the Bernoulli case `bernoulli_mgf_bound`, proved by the second-derivative argument
of [MRT18, Lemma D.1] / [CBL06, Lemma A.1].  A weaker `η²/2` version via the elementary
chord bound of [FS97, §2.1, Eq. (3) in the proof of Lemma 1] is included for comparison.
`Hedge.Regret` uses `bernoulli_mgf_bound` (through `hoeffding_lemma`).

## Main definitions

None — this file proves inequalities only.

## Main results

- `exp_convexity_bound'`: For x ∈ [0,1], exp(-η·x) ≤ 1 - x + x·exp(-η) by convexity of
  exp.
- `weighted_exp_le_affine`: Weighted sum bound Σ pᵢ·exp(-η·ℓᵢ) ≤ 1 - (1-exp(-η))·L using
  convexity.
- `log_one_add_le`: For u > -1, ln(1+u) ≤ u.
- `eta_exp_bound`: For η ≥ 0, η - 1 + exp(-η) ≤ η²/2.
- `hoeffding_log_mgf_weak`: Weak log-MGF bound ln(Σ pᵢ·exp(-η·ℓᵢ)) ≤ -η·L + η²/2.
- `bernoulli_mgf_bound`: Bernoulli MGF bound ln(1 - L + L·exp(-η)) ≤ -L·η + η²/8.
- `hoeffding_log_mgf_tight`: Tight log-MGF bound ln(Σ pᵢ·exp(-η·ℓᵢ)) ≤ -η·L + η²/8.

## References

* [MRT18] M. Mohri, A. Rostamizadeh, A. Talwalkar, *Foundations of Machine Learning*,
  2nd ed., MIT Press, 2018.
* [CBL06] N. Cesa-Bianchi, G. Lugosi, *Prediction, Learning, and Games*, Cambridge
  University Press, 2006.
* [FS97] Y. Freund, R. E. Schapire, "A decision-theoretic generalization of on-line
  learning and an application to boosting", *J. Comput. Syst. Sci.* 55(1):119–139, 1997.

Original formalization by Arhaan Aggarwal.
-/

open Finset BigOperators Real

noncomputable section

/-! ## Auxiliary lemmas -/

/-- For `x ∈ [0,1]`, `x(1-x) ≤ 1/4`.  Real-arithmetic glue; currently unused (the same
inequality appears inline as `h_second_nonneg` in `bernoulli_mgf_bound`). -/
lemma mul_one_sub_le_quarter (x : ℝ) (_hx0 : 0 ≤ x) (_hx1 : x ≤ 1) :
    x * (1 - x) ≤ 1 / 4 := by
  linarith [sq_nonneg (x - 1 / 2)]

/-- For `x ∈ [0,1]` and any real `η`, `exp(-ηx) ≤ 1 - x + x·exp(-η)`: the exponential lies
below the chord joining its values at `0` and `-η`, by convexity of `exp`.  This is the bound
`β^x ≤ 1 - (1 - β)x` of [FS97, §2.1, Eq. (3) in the proof of Lemma 1] with `β = e^{-η}`. -/
theorem exp_convexity_bound' (η x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (-η * x) ≤ 1 - x + x * Real.exp (-η) := by
  -- We'll use that exponential functions are convex to show this inequality.
  have h_convex : ConvexOn ℝ (Set.univ : Set ℝ) Real.exp := by
    exact convexOn_exp;
  have := h_convex.2 ( Set.mem_univ 0 ) ( Set.mem_univ ( -η ) );
  convert @this ( 1 - x ) x ( by linarith ) ( by linarith ) ( by linarith ) using 1 <;> norm_num ; ring

/-- For a probability vector `p` on `Fin n` and losses `ℓᵢ ∈ [0,1]`, the weighted sum
`Σ pᵢ e^{-ηℓᵢ}` is at most `1 - (1 - e^{-η}) Σ pᵢ ℓᵢ` [FS97, §2.1, Eq. (3) in the proof of
Lemma 1]: apply the chord bound `exp_convexity_bound'` to each term and sum. -/
theorem weighted_exp_le_affine
    {n : ℕ}
    (p : Fin n → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ℓ : Fin n → ℝ) (hℓ_nonneg : ∀ i, 0 ≤ ℓ i) (hℓ_le : ∀ i, ℓ i ≤ 1)
    (η : ℝ) :
    ∑ i, p i * Real.exp (-η * ℓ i) ≤
      1 - (1 - Real.exp (-η)) * (∑ i, p i * ℓ i) := by
  -- Apply the convexity bound to each term in the sum.
  have h_term_bound : ∀ i, p i * Real.exp (-η * ℓ i) ≤ p i * (1 - ℓ i + ℓ i * Real.exp (-η)) := by
    exact fun i => mul_le_mul_of_nonneg_left ( exp_convexity_bound' η ( ℓ i ) ( hℓ_nonneg i ) ( hℓ_le i ) ) ( hp_nonneg i );
  convert Finset.sum_le_sum fun i _ => h_term_bound i using 1 ; ring_nf;
  simpa [ Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum _ _ _, ← Finset.sum_mul, hp_sum ] using by ring;

/-- For `u > -1`, `ln(1+u) ≤ u`.  Real-arithmetic glue (a restatement of `ln x ≤ x - 1`),
used in `hoeffding_log_mgf_weak`. -/
theorem log_one_add_le (u : ℝ) (hu : -1 < u) :
    Real.log (1 + u) ≤ u := by
  linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + u)]

/-- For `η ≥ 0`, `η - 1 + exp(-η) ≤ η²/2`; equivalently `exp(-η) ≤ 1 - η + η²/2`, the
second-order upper Taylor bound.  Real-arithmetic glue.  Proof: the function
`f(η) = η²/2 - η + 1 - e^{-η}` has `f(0) = 0` and nonnegative derivative on `[0, ∞)`, so by
the mean value theorem `f(η) ≥ 0`. -/
theorem eta_exp_bound (η : ℝ) (hη : 0 ≤ η) :
    η - 1 + Real.exp (-η) ≤ η ^ 2 / 2 := by
  -- Define the function $f(η) = η^2/2 - η + 1 - e^{-η}$.
  set f : ℝ → ℝ := fun η => η^2 / 2 - η + 1 - Real.exp (-η);
  -- We'll use the fact that $f(η)$ is differentiable and that its derivative is non-negative for $η ≥ 0$.
  have h_deriv_nonneg : ∀ η ≥ 0, deriv f η ≥ 0 := by
    intro η hη; erw [ deriv_sub ] <;> norm_num [ Real.exp_neg, Real.differentiableAt_exp ];
    rw [ div_le_iff₀ ] <;> nlinarith [ Real.exp_pos η, Real.exp_neg η, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos η ) ), Real.add_one_le_exp η, Real.add_one_le_exp ( -η ) ];
  by_contra h_contra;
  -- Apply the mean value theorem to $f$ on the interval $[0, η]$.
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo 0 η, deriv f c = (f η - f 0) / (η - 0) := by
    apply_rules [ exists_deriv_eq_slope ];
    · exact hη.lt_of_ne ( by rintro rfl; norm_num at h_contra );
    · fun_prop;
    · fun_prop;
  norm_num +zetaDelta at *;
  nlinarith [ h_deriv_nonneg c hc.1.1.le, mul_div_cancel₀ ( η ^ 2 / 2 - η + 1 - Real.exp ( -η ) ) ( by linarith : η ≠ 0 ) ]

/-! ## Weak Hoeffding bound (η²/2 constant) -/

/-- Weak log-MGF bound: for a probability vector `p` on `Fin n`, losses `ℓᵢ ∈ [0,1]`, and
`η > 0`, `ln(Σ pᵢ e^{-ηℓᵢ}) ≤ -η·L + η²/2` where `L = Σ pᵢ ℓᵢ` (chord bound: [FS97, §2.1,
Eq. (3) in the proof of Lemma 1]).  Deviation: the constant is `η²/2` (from the elementary
bound `e^{-η} ≤ 1 - η + η²/2`, which is not from FS97) rather than Hoeffding's `η²/8`,
which is `hoeffding_log_mgf_tight`.  The hypothesis `_hn` is not used.

**Proof sketch.**
Step 1: by the chord bound `weighted_exp_le_affine`, `Σ pᵢ e^{-ηℓᵢ} ≤ 1 - (1 - e^{-η}) L`.
Step 2: `L ∈ [0,1]`, as a convex combination of numbers in `[0,1]`.
Step 3: the left-hand sum is positive (some `pᵢ > 0` since `Σ pᵢ = 1`), so logarithms may
be taken.
Step 4: `ln(1 + u) ≤ u` (`log_one_add_le`) with `u = -(1 - e^{-η}) L > -1` gives
`ln(1 - (1 - e^{-η}) L) ≤ -(1 - e^{-η}) L`.
Step 5: `-(1 - e^{-η}) L = -ηL + (η - 1 + e^{-η}) L ≤ -ηL + η²/2`, by `eta_exp_bound` and
`0 ≤ L ≤ 1`. -/
theorem hoeffding_log_mgf_weak
    {n : ℕ} (_hn : 0 < n)
    (p : Fin n → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ℓ : Fin n → ℝ) (hℓ_nonneg : ∀ i, 0 ≤ ℓ i) (hℓ_le : ∀ i, ℓ i ≤ 1)
    (η : ℝ) (hη : 0 < η) :
    Real.log (∑ i, p i * Real.exp (-η * ℓ i)) ≤
      -η * (∑ i, p i * ℓ i) + η ^ 2 / 2 := by
  -- Step 1: convexity bound Σ pᵢ·exp(-η·ℓᵢ) ≤ 1 - (1 - exp(-η))·L, where L = Σ pᵢ·ℓᵢ.
  have h_affine : ∑ i, p i * Real.exp (-η * ℓ i) ≤
      1 - (1 - Real.exp (-η)) * (∑ i, p i * ℓ i) :=
    weighted_exp_le_affine p hp_nonneg hp_sum ℓ hℓ_nonneg hℓ_le η
  -- Step 2: L ∈ [0, 1].
  have hL0 : 0 ≤ ∑ i, p i * ℓ i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hp_nonneg i) (hℓ_nonneg i)
  have hL1 : ∑ i, p i * ℓ i ≤ 1 :=
    hp_sum ▸ Finset.sum_le_sum fun i _ => mul_le_of_le_one_right (hp_nonneg i) (hℓ_le i)
  -- Step 3: the left-hand sum is positive (some pᵢ > 0 since Σ pᵢ = 1).
  have h_sum_pos : 0 < ∑ i, p i * Real.exp (-η * ℓ i) := by
    obtain ⟨i, hi⟩ : ∃ i, 0 < p i := by
      by_contra h
      push_neg at h
      have : ∑ i, p i ≤ 0 := Finset.sum_nonpos fun i _ => h i
      linarith
    exact lt_of_lt_of_le (mul_pos hi (Real.exp_pos _))
      (Finset.single_le_sum (fun i _ => mul_nonneg (hp_nonneg i) (Real.exp_nonneg _))
        (Finset.mem_univ i))
  -- Step 4: log(1 + u) ≤ u with u = -(1 - exp(-η))·L (which is > -1 since exp(-η) < 1).
  have h_exp_lt_one : Real.exp (-η) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have h_log : Real.log (1 - (1 - Real.exp (-η)) * (∑ i, p i * ℓ i)) ≤
      -((1 - Real.exp (-η)) * (∑ i, p i * ℓ i)) := by
    rw [sub_eq_add_neg]
    exact log_one_add_le _ (by
      nlinarith [mul_nonneg (sub_nonneg.2 h_exp_lt_one.le) (sub_nonneg.2 hL1), Real.exp_pos (-η)])
  -- Step 5: η - 1 + exp(-η) ≤ η²/2 (`eta_exp_bound`), scaled by L ≤ 1.
  have h_nn : 0 ≤ η - 1 + Real.exp (-η) := by linarith [Real.add_one_le_exp (-η)]
  calc Real.log (∑ i, p i * Real.exp (-η * ℓ i))
      ≤ Real.log (1 - (1 - Real.exp (-η)) * (∑ i, p i * ℓ i)) :=
        Real.log_le_log h_sum_pos h_affine
    _ ≤ -((1 - Real.exp (-η)) * (∑ i, p i * ℓ i)) := h_log
    _ ≤ -η * (∑ i, p i * ℓ i) + η ^ 2 / 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hL1 h_nn, eta_exp_bound η hη.le]

/-! ## Tight Hoeffding bound (η²/8 constant) -/

/-- Step lemma for `bernoulli_mgf_bound` (Step 5): at any `x` where `1 - L + L e^{-x} > 0`,
the function `φ(x) = -L x + x²/8 - log(1 - L + L e^{-x})` has derivative
`φ'(x) = -L + x/4 + L e^{-x} / (1 - L + L e^{-x})`.  This is the `φ'` computation in the
proof of [MRT18, Lemma D.1]. -/
lemma bernoulli_mgf_bound_step1 (L x : ℝ) (hpos : 0 < 1 - L + L * Real.exp (-x)) :
    HasDerivAt (fun x => -L * x + x ^ 2 / 8 - Real.log (1 - L + L * Real.exp (-x)))
      (-L + x / 4 + L * Real.exp (-x) / (1 - L + L * Real.exp (-x))) x := by
  have hne : 1 - L + L * Real.exp (-x) ≠ 0 := hpos.ne'
  have h_den : HasDerivAt (fun x => 1 - L + L * Real.exp (-x)) (L * (Real.exp (-x) * -1)) x :=
    ((hasDerivAt_neg' x).exp.const_mul L).const_add (1 - L)
  have h := (((hasDerivAt_id' x).const_mul (-L)).fun_add ((hasDerivAt_pow 2 x).div_const 8)).fun_sub
    (h_den.log hne)
  convert h using 1
  field_simp
  ring

/-- Step lemma for `bernoulli_mgf_bound` (Step 5): at any `x` where `1 - L + L e^{-x} > 0`,
the derivative `φ'` of `bernoulli_mgf_bound_step1` has itself derivative
`φ''(x) = 1/4 - L (1 - L) e^{-x} / (1 - L + L e^{-x})²`.  This is the `φ''` computation in
the proof of [MRT18, Lemma D.1]. -/
lemma bernoulli_mgf_bound_step2 (L x : ℝ) (hpos : 0 < 1 - L + L * Real.exp (-x)) :
    HasDerivAt (fun x => -L + x / 4 + L * Real.exp (-x) / (1 - L + L * Real.exp (-x)))
      (1 / 4 - L * (1 - L) * Real.exp (-x) / (1 - L + L * Real.exp (-x)) ^ 2) x := by
  have hne : 1 - L + L * Real.exp (-x) ≠ 0 := hpos.ne'
  have h_num : HasDerivAt (fun x => L * Real.exp (-x)) (L * (Real.exp (-x) * -1)) x :=
    (hasDerivAt_neg' x).exp.const_mul L
  have h_den : HasDerivAt (fun x => 1 - L + L * Real.exp (-x)) (L * (Real.exp (-x) * -1)) x :=
    h_num.const_add (1 - L)
  have h := (((hasDerivAt_id' x).div_const 4).const_add (-L)).fun_add (h_num.fun_div h_den hne)
  convert h using 1
  field_simp
  ring

/-- **Hoeffding's lemma for a Bernoulli variable**: for `L ∈ [0,1]` and any real `η`,
`ln(1 - L + L·e^{-η}) ≤ -L·η + η²/8`; that is, the log-moment generating function of a
`{0,1}`-valued random variable with mean `L`, evaluated at `-η`, is at most `-Lη + η²/8`
[MRT18, Lemma D.1 (proof)]; [CBL06, Lemma A.1 (proof)].  Deviation: only the two-point
(Bernoulli) case is proved, and the argument is written as `-η`; this is the core
`φ(0) = 0`, `φ'(0) = 0`, `φ'' ≤ 1/4` step of the textbook proof, which reduces the general
`[a,b]`-valued case to it by convexity.

**Proof sketch.** Let `φ(x) = -L x + x²/8 - ln(1 - L + L e^{-x})`; the claim is
`φ(η) ≥ 0`.
Step 1: boundary case `L = 0`: the left side is `ln 1 = 0 ≤ η²/8`.
Step 2: boundary case `L = 1`: the left side is `ln e^{-η} = -η ≤ -η + η²/8`.
Step 3: for `0 < L < 1` the argument `1 - L + L e^{-x}` of the logarithm is positive for
every `x`, so `φ` is defined everywhere.
Step 4: the second derivative `φ''(x) = 1/4 - q(1-q)` with
`q = L e^{-x} / (1 - L + L e^{-x})` is nonnegative, since `q(1-q) ≤ 1/4`.
Step 5: `φ'` and `φ''` are computed by the step lemmas `bernoulli_mgf_bound_step1` and
`bernoulli_mgf_bound_step2`; with Step 4 and Mathlib's second-derivative criterion, `φ` is
convex on the real line.
Step 6: `φ'(0) = -L + 0 + L = 0`.
Step 7: a convex function whose (right) derivative vanishes at `0` attains its minimum at
`0`, and `φ(0) = 0`.
Step 8: hence `φ(η) ≥ φ(0) = 0`, which is the claim. -/
theorem bernoulli_mgf_bound (L η : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1) :
    Real.log (1 - L + L * Real.exp (-η)) ≤ -L * η + η ^ 2 / 8 := by
  -- Step 1: boundary case L = 0 (the left side is log 1 = 0).
  rcases hL0.eq_or_lt with rfl | hL
  · norm_num
    positivity
  -- Step 2: boundary case L = 1 (the left side is log (exp (-η)) = -η).
  rcases hL1.eq_or_lt with rfl | hL'
  · norm_num
    positivity
  -- Step 3: for 0 < L < 1 the argument of the logarithm is positive everywhere.
  have h_pos : ∀ x, 0 < 1 - L + L * Real.exp (-x) := fun x => by
    linarith [mul_pos hL (Real.exp_pos (-x))]
  -- Step 4: φ(x) = -L x + x²/8 - log(1 - L + L e^{-x}); its second derivative is ≥ 0
  -- because q(1-q) ≤ 1/4 with q = L e^{-x} / (1 - L + L e^{-x}).
  set f : ℝ → ℝ := fun x => -L * x + x ^ 2 / 8 - Real.log (1 - L + L * Real.exp (-x)) with hf
  have h_second_nonneg :
      ∀ x, 0 ≤ 1 / 4 - L * (1 - L) * Real.exp (-x) / (1 - L + L * Real.exp (-x)) ^ 2 := by
    intro x
    rw [sub_nonneg, div_le_iff₀ (pow_pos (h_pos x) 2)]
    nlinarith [sq_nonneg (1 - L - L * Real.exp (-x))]
  -- Step 5: φ is convex on ℝ (φ' and φ'' from the step lemmas).
  have h_convex : ConvexOn ℝ Set.univ f :=
    convexOn_of_hasDerivWithinAt2_nonneg convex_univ
      (fun x _ => (bernoulli_mgf_bound_step1 L x (h_pos x)).continuousAt.continuousWithinAt)
      (fun x _ => (bernoulli_mgf_bound_step1 L x (h_pos x)).hasDerivWithinAt)
      (fun x _ => (bernoulli_mgf_bound_step2 L x (h_pos x)).hasDerivWithinAt)
      (fun x _ => h_second_nonneg x)
  -- Step 6: φ'(0) = 0.
  have h_deriv0 : derivWithin f (Set.Ioi 0) 0 = 0 :=
    ((bernoulli_mgf_bound_step1 L 0 (h_pos 0)).hasDerivWithinAt.derivWithin
      (uniqueDiffWithinAt_Ioi 0)).trans (by norm_num)
  -- Step 7: a convex function with vanishing derivative at 0 is minimized at 0, and φ(0) = 0.
  have h_min : IsMinOn f Set.univ 0 := h_convex.isMinOn_of_rightDeriv_eq_zero (by simp) h_deriv0
  have h_f0 : f 0 = 0 := by simp [hf]
  -- Step 8: φ(η) ≥ φ(0) = 0 is the claim.
  have h_le : f 0 ≤ f η := isMinOn_iff.mp h_min η (Set.mem_univ η)
  rw [h_f0] at h_le
  simp only [hf] at h_le
  linarith

/-- **Hoeffding's lemma** in log-MGF form: for a probability vector `p` on `Fin n`, losses
`ℓᵢ ∈ [0,1]`, and `η > 0`, `ln(Σ pᵢ e^{-ηℓᵢ}) ≤ -η·L + η²/8` where `L = Σ pᵢ ℓᵢ`
[CBL06, Lemma 2.2] applied to the loss `ℓ_I` of an expert `I` drawn from `p`;
[MRT18, Lemma D.1].  The hypotheses `_hn` and `_hη` are not used.

Proof: by the chord bound `weighted_exp_le_affine`, `Σ pᵢ e^{-ηℓᵢ} ≤ 1 - L + L e^{-η}`; the
left side is positive, so take logarithms and apply `bernoulli_mgf_bound` to `L ∈ [0,1]`. -/
theorem hoeffding_log_mgf_tight
    {n : ℕ} (_hn : 0 < n)
    (p : Fin n → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (ℓ : Fin n → ℝ) (hℓ_nonneg : ∀ i, 0 ≤ ℓ i) (hℓ_le : ∀ i, ℓ i ≤ 1)
    (η : ℝ) (_hη : 0 < η) :
    Real.log (∑ i, p i * Real.exp (-η * ℓ i)) ≤
      -η * (∑ i, p i * ℓ i) + η ^ 2 / 8 := by
  -- By weighted_exp_le_affine, Σ p_i · exp(-η·ℓ_i) ≤ 1 - L + L·exp(-η) where L = Σ p_i·ℓ_i.
  have h1 : ∑ i, p i * Real.exp (-η * ℓ i) ≤ 1 - (1 - Real.exp (-η)) * (∑ i, p i * ℓ i) := by
    convert weighted_exp_le_affine p hp_nonneg hp_sum ℓ hℓ_nonneg hℓ_le η using 1;
  refine' le_trans ( Real.log_le_log ( _ ) h1 ) _;
  · -- Since $p$ is a probability distribution, there exists some $i$ such that $p_i > 0$.
    obtain ⟨i, hi⟩ : ∃ i, 0 < p i := by
      exact not_forall_not.mp fun h => by have := hp_sum ▸ Finset.sum_nonpos fun i _ => le_of_not_gt fun hi => h i hi; norm_num at this;
    exact lt_of_lt_of_le ( mul_pos hi ( Real.exp_pos _ ) ) ( Finset.single_le_sum ( fun i _ => mul_nonneg ( hp_nonneg i ) ( Real.exp_nonneg _ ) ) ( Finset.mem_univ i ) );
  · convert bernoulli_mgf_bound ( ∑ i, p i * ℓ i ) η _ _ using 1 <;> ring_nf;
    · exact Finset.sum_nonneg fun _ _ => mul_nonneg ( hp_nonneg _ ) ( hℓ_nonneg _ );
    · exact hp_sum ▸ Finset.sum_le_sum fun i _ => mul_le_of_le_one_right ( hp_nonneg i ) ( hℓ_le i )

end
