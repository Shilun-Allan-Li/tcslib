import TCSlib.BooleanAnalysis.Hypercontractivity.EvenMoments
import TCSlib.BooleanAnalysis.Hypercontractivity.General
import TCSlib.BooleanAnalysis.Hypercontractivity.OneBit
import Mathlib.Analysis.Analytic.Binomial

/-!
# Reverse Bonami-Beckner inequality

This file is a declaration-level outline of Borell's proof.  The intended order is:

1. define the extended `L^p` means used when `p ≤ 1`;
2. prove the two-point inequality by the even Taylor expansion from Lemma A.1;
3. tensorize with reverse Minkowski, using the last-coordinate decomposition;
4. remove the strict-positive-exponent and sharp-correlation assumptions;
5. derive the two-function form from reverse Hölder and self-adjointness.

The existing lemmas `OneBit.expect_abs_rpow_one_bit`, `Bonami.expect_succ_eq`,
`SimpleHypercontractivity.noiseOp_snoc`, `SimpleHypercontractivity.noiseOp_compose`,
and `BooleanAnalysis.noiseOp_self_adjoint` provide the Boolean-cube bookkeeping needed below.

## Organisation

* `lpMean` and its elementary calculus (`lpMean_nonneg`, `lpMean_mono`,
  `lpMean_const_mul`, `lpMean_collapse_last`, `lpMean_comm`);
* the behaviour of `noiseOp` on nonnegative functions and on one-bit affine
  functions;
* the two-point inequality `reverse_bonami_beckner_one_bit`;
* tensorization via `reverse_minkowski_mixed`;
* reverse Hölder and the statement of the general theorem.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  arXiv edition, 2021, Exercises 10.6--10.9.
-/

open BooleanAnalysis Bonami OneBit SimpleHypercontractivity

namespace ReverseBonamiBeckner

variable {n : ℕ}

/-! ### The extended `L^p` means -/

/-- Pointwise nonnegativity, the natural domain of reverse hypercontractivity. -/
def IsNonnegative (f : BooleanFunc n) : Prop :=
  ∀ x, 0 ≤ f x

open Classical in
/-- The extended uniform `L^p` mean.  At `p = 0` this is the geometric mean; for
`p ≤ 0`, a function with a zero has mean zero. -/
noncomputable def lpMean (p : ℝ) (f : BooleanFunc n) : ℝ :=
  if (∃ x, f x = 0) ∧ p ≤ 0 then 0
  else if p = 0 then Real.exp (expect (fun x ↦ Real.log |f x|))
  else (expect (fun x ↦ |f x| ^ p)) ^ (1 / p)

/-- For positive exponents, `lpMean` is the usual power mean. -/
lemma lpMean_of_pos (p : ℝ) (hp : 0 < p) (f : BooleanFunc n) :
    lpMean p f = (expect (fun x ↦ |f x| ^ p)) ^ (1 / p) := by
  simp [lpMean, hp.ne', not_le.mpr hp]

/-- Power means with a positive exponent are nonnegative. -/
lemma lpMean_nonneg (p : ℝ) (hp : 0 < p) (f : BooleanFunc n) : 0 ≤ lpMean p f := by
  rw [lpMean_of_pos p hp]
  exact Real.rpow_nonneg (expect_rpow_abs_nonneg p f) _

/-- Power means with a positive exponent are monotone on nonnegative functions. -/
lemma lpMean_mono (p : ℝ) (hp : 0 < p) {f g : BooleanFunc n} (hf : IsNonnegative f)
    (hfg : ∀ x, f x ≤ g x) : lpMean p f ≤ lpMean p g := by
  have hg : ∀ x, 0 ≤ g x := fun x ↦ (hf x).trans (hfg x)
  rw [lpMean_of_pos p hp, lpMean_of_pos p hp]
  simp_rw [abs_of_nonneg (hf _), abs_of_nonneg (hg _)]
  refine Real.rpow_le_rpow
    (by
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (hf x) p) ?_ (by positivity)
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun x _ ↦ Real.rpow_le_rpow (hf x) (hfg x) hp.le)
    (pow_nonneg (by norm_num) _)

/-- Power means with a positive exponent are homogeneous. -/
lemma lpMean_const_mul (p c : ℝ) (hp : 0 < p) (hc : 0 < c) (f : BooleanFunc n) :
    lpMean p (fun x ↦ c * f x) = c * lpMean p f := by
  have hE : expect (fun x ↦ |c * f x| ^ p) = c ^ p * expect (fun x ↦ |f x| ^ p) := by
    unfold expect
    simp_rw [abs_mul, abs_of_pos hc, Real.mul_rpow hc.le (abs_nonneg _), ← Finset.mul_sum]
    ring
  rw [lpMean_of_pos p hp, lpMean_of_pos p hp, hE,
    Real.mul_rpow (Real.rpow_nonneg hc.le p) (expect_rpow_abs_nonneg p f),
    ← Real.rpow_mul hc.le, mul_one_div, div_self hp.ne', Real.rpow_one]

/-- On the empty cube every mean is the single value of the function. -/
lemma lpMean_dim_zero (p : ℝ) (hp : 0 < p) (f : BooleanFunc 0) (hf : IsNonnegative f) :
    lpMean p f = f (fun i ↦ Fin.elim0 i) := by
  rw [lpMean_of_pos p hp]
  unfold expect uniformWeight
  norm_num
  change (|f (fun i ↦ Fin.elim0 i)| ^ p) ^ p⁻¹ = f (fun i ↦ Fin.elim0 i)
  rw [abs_of_nonneg (hf _), ← Real.rpow_mul (hf _), show p * p⁻¹ = 1 by field_simp,
    Real.rpow_one]

/-- Splitting off the last coordinate: an `L^p` mean on `n + 1` bits is the `L^p`
mean over the first `n` bits of the one-bit `L^p` means. -/
lemma lpMean_collapse_last (p : ℝ) (hp : 0 < p) (f : BooleanFunc (n + 1)) :
    lpMean p f =
      lpMean p (fun x : BoolCube n ↦
        lpMean p (fun y : BoolCube 1 ↦ f (Fin.snoc x (y 0)))) := by
  have hinner (x : BoolCube n) :
      0 ≤ expect (fun y : BoolCube 1 ↦ |f (Fin.snoc x (y 0))| ^ p) :=
    by
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun y _ ↦ Real.rpow_nonneg (abs_nonneg _) p
  rw [lpMean_of_pos p hp, lpMean_of_pos p hp]
  simp_rw [lpMean_of_pos p hp, abs_of_nonneg (Real.rpow_nonneg (hinner _) _),
    ← Real.rpow_mul (hinner _), show 1 / p * p = 1 by field_simp, Real.rpow_one]
  rw [GeneralHypercontractivity.norm_collapse_rpow p hp f]
  congr 2 with x
  unfold expect uniformWeight
  rw [show (Finset.univ : Finset (BoolCube 1)) = {fun _ ↦ false, fun _ ↦ true} by decide,
    Finset.sum_pair (by decide)]
  norm_num

/-- Iterated means over two blocks of coordinates commute. -/
lemma lpMean_comm (p : ℝ) (hp : 0 < p) (F : BoolCube n → BoolCube 1 → ℝ) :
    lpMean p (fun x ↦ lpMean p (fun y ↦ F x y)) =
      lpMean p (fun y ↦ lpMean p (fun x ↦ F x y)) := by
  have hx (x : BoolCube n) : 0 ≤ expect (fun y : BoolCube 1 ↦ |F x y| ^ p) :=
    by
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun y _ ↦ Real.rpow_nonneg (abs_nonneg _) p
  have hy (y : BoolCube 1) : 0 ≤ expect (fun x : BoolCube n ↦ |F x y| ^ p) :=
    by
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (abs_nonneg _) p
  simp_rw [lpMean_of_pos p hp, abs_of_nonneg (Real.rpow_nonneg (hx _) _),
    abs_of_nonneg (Real.rpow_nonneg (hy _) _), ← Real.rpow_mul (hx _), ← Real.rpow_mul (hy _),
    show 1 / p * p = 1 by field_simp, Real.rpow_one]
  congr 1
  unfold expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, mul_comm (uniformWeight n)]

/-! ### The noise operator on nonnegative and on affine functions -/

/-- Fourier coefficients are homogeneous. -/
lemma fourierCoeff_const_mul (c : ℝ) (f : BooleanFunc n) (S : Finset (Fin n)) :
    fourierCoeff (fun x ↦ c * f x) S = c * fourierCoeff f S := by
  unfold fourierCoeff innerProduct expect
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

/-- The noise operator is homogeneous. -/
lemma noiseOp_const_mul (ρ c : ℝ) (f : BooleanFunc n) :
    noiseOp ρ (fun x ↦ c * f x) = fun x ↦ c * noiseOp ρ f x := by
  funext x
  unfold noiseOp
  simp_rw [fourierCoeff_const_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ ↦ by ring

/-- On the empty cube the noise operator is the identity. -/
lemma noiseOp_dim_zero (ρ : ℝ) (f : BooleanFunc 0) : noiseOp ρ f = f := by
  funext x
  conv_rhs => rw [walsh_expansion f]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  obtain rfl : S = ∅ := Finset.eq_empty_of_forall_notMem fun i _ ↦ i.elim0
  simp

/-- The noise operator preserves nonnegativity, since its kernel is nonnegative. -/
lemma noiseOp_nonneg {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {f : BooleanFunc n}
    (hf : IsNonnegative f) : IsNonnegative (noiseOp ρ f) := fun x ↦ by
  rw [GeneralHypercontractivity.noiseOp_eq_kernel_sum]
  exact Finset.sum_nonneg fun y _ ↦
    mul_nonneg (GeneralHypercontractivity.noiseKernel_nonneg hρ0 hρ1 x y) (hf y)

/-- The noise operator shrinks the coefficient of a one-bit affine function. -/
lemma noiseOp_affine_one_bit (ρ a : ℝ) :
    noiseOp ρ (fun x : BoolCube 1 ↦ 1 + a * boolToSign (x 0)) =
      fun x ↦ 1 + (ρ * a) * boolToSign (x 0) := by
  funext x
  unfold noiseOp
  rw [show (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} by decide,
    Finset.sum_pair (by decide)]
  norm_num [fourierCoeff, innerProduct, expect, uniformWeight, chiS, boolToSign]
  repeat' first
    | rw [show (Finset.univ : Finset (BoolCube 1)) =
        {fun _ ↦ false, fun _ ↦ true} by decide]
    | rw [Finset.sum_pair (by decide)]
  cases hx : x 0 <;> norm_num [boolToSign] <;> ring

/-- The Fourier coefficients of the average of the two restrictions of the last bit. -/
lemma fourierCoeff_avgLast (f : BooleanFunc (n + 1)) (S : Finset (Fin n)) :
    fourierCoeff (avgLast f) S =
      (fourierCoeff (restrictLast f false) S + fourierCoeff (restrictLast f true) S) / 2 := by
  unfold fourierCoeff innerProduct expect avgLast
  ring_nf
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- The Fourier coefficients of the difference of the two restrictions of the last bit. -/
lemma fourierCoeff_diffLast (f : BooleanFunc (n + 1)) (S : Finset (Fin n)) :
    fourierCoeff (diffLast f) S =
      (fourierCoeff (restrictLast f false) S - fourierCoeff (restrictLast f true) S) / 2 := by
  unfold fourierCoeff innerProduct expect diffLast
  ring_nf
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- Noise on `n + 1` bits factors as noise on the last bit applied to the noised
restrictions of the first `n` bits. -/
lemma noiseOp_snoc_slice (ρ : ℝ) (f : BooleanFunc (n + 1)) (x : BoolCube n) (y : BoolCube 1) :
    noiseOp ρ f (Fin.snoc x (y 0)) =
      noiseOp ρ (fun t : BoolCube 1 ↦ noiseOp ρ (restrictLast f (t 0)) x) y := by
  have hy : y = Fin.snoc (fun i ↦ Fin.elim0 i) (y 0) := by
    funext i
    fin_cases i
    rfl
  conv_lhs => rw [noiseOp_snoc]
  conv_rhs => rw [hy, noiseOp_snoc, noiseOp_dim_zero, noiseOp_dim_zero]
  dsimp [avgLast, diffLast, restrictLast]
  unfold noiseOp
  simp_rw [fourierCoeff_avgLast, fourierCoeff_diffLast]
  simp only [show (Fin.snoc (fun i ↦ Fin.elim0 i) false : BoolCube 1) 0 = false from rfl,
    show (Fin.snoc (fun i ↦ Fin.elim0 i) true : BoolCube 1) 0 = true from rfl]
  ring_nf
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  repeat rw [← Finset.sum_mul]
  ring

/-! ### The two-point inequality -/

/-- Newton's binomial series: for `|x| < 1` the function `(1 + x) ^ s` is the sum
of the generalized binomial series. -/
private lemma hasSum_choose_rpow {s x : ℝ} (hx : |x| < 1) :
    HasSum (fun k : ℕ ↦ Ring.choose s k * x ^ k) ((1 + x) ^ s) := by
  have hsum := (one_add_rpow_hasFPowerSeriesOnBall_zero (a := s)).hasSum_sub
    (show x ∈ EMetric.ball (0 : ℝ) 1 by
      simpa [EMetric.mem_ball, edist_dist, Real.dist_eq] using hx)
  convert hsum using 1
  ext k
  simp [binomialSeries, mul_comm]

/-- The even part of the binomial series is summable. -/
private lemma summable_choose_even {s x : ℝ} (hx : |x| < 1) :
    Summable (fun k : ℕ ↦ Ring.choose s (2 * k) * x ^ (2 * k)) :=
  (hasSum_choose_rpow hx).summable.comp_injective
    (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0))

/-- Symmetrizing the binomial series kills the odd terms. -/
private lemma even_part_rpow_eq_tsum {s x : ℝ} (hx : |x| < 1) :
    ((1 + x) ^ s + (1 - x) ^ s) / 2 =
      ∑' k : ℕ, Ring.choose s (2 * k) * x ^ (2 * k) := by
  have hxneg : |-x| < 1 := by simpa using hx
  have hboth : HasSum
      (fun k : ℕ ↦ (Ring.choose s k * x ^ k + Ring.choose s k * (-x) ^ k) / 2)
      (((1 + x) ^ s + (1 + -x) ^ s) / 2) :=
    ((hasSum_choose_rpow hx).add (hasSum_choose_rpow hxneg)).div_const 2
  have heven := (summable_choose_even (s := s) hx).hasSum
  have hall : HasSum
      (fun k : ℕ ↦ (Ring.choose s k * x ^ k + Ring.choose s k * (-x) ^ k) / 2)
      ((∑' k : ℕ, Ring.choose s (2 * k) * x ^ (2 * k)) + 0) := by
    apply HasSum.even_add_odd
    · convert heven using 1
      funext k
      rw [Even.neg_pow (even_two.mul_right k)]
      ring
    · convert (hasSum_zero : HasSum (fun _ : ℕ ↦ (0 : ℝ)) 0) using 1
      funext k
      rw [show (-x) ^ (2 * k + 1) = -(x ^ (2 * k + 1)) by
        rw [pow_add, Even.neg_pow (even_two.mul_right k), pow_one]
        ring]
      ring
  rw [show 1 - x = 1 + -x by ring]
  simpa using hboth.unique hall

/-- The `L^s` moment of the one-bit function `1 + b χ`, for `|b| < 1`. -/
private lemma expect_abs_rpow_affine (s b : ℝ) (hb : |b| < 1) :
    expect (fun x : BoolCube 1 ↦ |1 + b * boolToSign (x 0)| ^ s) =
      ((1 + b) ^ s + (1 - b) ^ s) / 2 := by
  obtain ⟨hb1, hb2⟩ := abs_lt.mp hb
  set f : BooleanFunc 1 := fun x ↦ 1 + b * boolToSign (x 0) with hf_def
  have hfalse : (1 : ℝ) + b = fourierCoeff f ∅ + fourierCoeff f {⟨0, by omega⟩} := by
    rw [← OneBit.one_bit_val_false f, hf_def]
    norm_num [boolToSign]
  have htrue : (1 : ℝ) - b = fourierCoeff f ∅ - fourierCoeff f {⟨0, by omega⟩} := by
    rw [← OneBit.one_bit_val_true f, hf_def]
    norm_num [boolToSign]
    ring
  rw [OneBit.expect_abs_rpow_one_bit, show fourierCoeff f ∅ = 1 by linarith,
    show fourierCoeff f {⟨0, by omega⟩} = b by linarith,
    abs_of_pos (by linarith : (0:ℝ) < 1 + b), abs_of_pos (by linarith : (0:ℝ) < 1 - b)]

/-- The second generalized binomial coefficient. -/
private lemma ring_choose_two (s : ℝ) : Ring.choose s 2 = s * (s - 1) / 2 := by
  have h := Ring.choose_smul_choose (R := ℝ) s (show 1 ≤ 2 by omega)
  norm_num [nsmul_eq_mul, Ring.choose_one_right] at h ⊢
  linarith

/-- Two steps of Pascal's recurrence for generalized binomial coefficients. -/
private lemma ring_choose_even_succ (s : ℝ) (k : ℕ) :
    Ring.choose s (2 * (k + 1)) =
      Ring.choose s (2 * k) * (s - (2 * k : ℕ)) * (s - (2 * k + 1 : ℕ)) /
        (((2 * k + 1 : ℕ) : ℝ) * ((2 * k + 2 : ℕ) : ℝ)) := by
  have h1 := Ring.choose_smul_choose (R := ℝ) s (Nat.le_succ (2 * k))
  have h2 := Ring.choose_smul_choose (R := ℝ) s (Nat.le_succ (2 * k + 1))
  simp only [nsmul_eq_mul] at h1 h2
  norm_num at h1 h2 ⊢
  have h1' : Ring.choose s (2 * k + 1) =
      Ring.choose s (2 * k) * (s - 2 * (k : ℝ)) / (2 * (k : ℝ) + 1) :=
    (eq_div_iff (by positivity)).2 (by nlinarith [h1])
  have h2' : Ring.choose s (2 * k + 1 + 1) =
      Ring.choose s (2 * k + 1) * (s - (2 * (k : ℝ) + 1)) / (2 * (k : ℝ) + 2) :=
    (eq_div_iff (by positivity)).2 (by nlinarith [h2])
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega, h2', h1']
  field_simp

/-- For an exponent in `(0, 1)` all even generalized binomial coefficients past
the constant term are nonpositive. -/
private lemma ring_choose_even_nonpos (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∀ k : ℕ, 1 ≤ k → Ring.choose s (2 * k) ≤ 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      match k, hk with
      | 1, _ =>
          rw [ring_choose_two]
          nlinarith
      | (k + 2), _ =>
          rw [ring_choose_even_succ]
          have hprev := ih (k + 1) (by omega) (by omega)
          have hfac : 0 ≤ (s - (2 * (k + 1) : ℕ)) * (s - (2 * (k + 1) + 1 : ℕ)) := by
            apply mul_nonneg_of_nonpos_of_nonpos <;> norm_num <;> linarith
          refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
          rw [mul_assoc]
          exact mul_nonpos_of_nonpos_of_nonneg hprev hfac

/-- The scalar factor estimate used to compare corresponding even Taylor
coefficients in Borell's proof. -/
lemma borell_factor_bound (p q ρ : ℝ) (hq : 0 < q) (hqp : q < p) (hp : p < 1)
    (hρ0 : 0 ≤ ρ) (hρsq : ρ ^ 2 = (1 - p) / (1 - q))
    (m : ℕ) (hm : 2 ≤ m) :
    ρ * ((m : ℝ) - q) ≤ (m : ℝ) - p := by
  have hq1 : q < 1 := hqp.trans hp
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hρrel : ρ ^ 2 * (1 - q) = 1 - p := by
    rw [hρsq, div_mul_cancel₀ _ (sub_pos.mpr hq1).ne']
  have hquad : 0 ≤ (m : ℝ) ^ 2 - 2 * m + p + q - p * q := by
    nlinarith [mul_nonneg (show 0 ≤ (m : ℝ) by linarith) (show 0 ≤ (m : ℝ) - 2 by linarith),
      mul_nonneg hq.le (sub_pos.mpr hp).le]
  refine (sq_le_sq₀ (mul_nonneg hρ0 (by linarith)) (by linarith)).mp ?_
  have key : 0 ≤ ((m : ℝ) - p) ^ 2 * (1 - q) - ρ ^ 2 * (1 - q) * ((m : ℝ) - q) ^ 2 := by
    rw [hρrel]
    nlinarith [mul_nonneg (sub_nonneg.mpr hqp.le) hquad]
  nlinarith [key, sub_pos.mpr hq1]

/-- The inductive step of the coefficient comparison: Pascal's recurrence turns
the bound for `2K` into the bound for `2K + 2`, at the cost of the two factors
controlled by `borell_factor_bound`. -/
private lemma choose_even_ratio_step (p q ρ : ℝ) (hq : 0 < q) (hqp : q < p) (hp : p < 1)
    (hρ0 : 0 ≤ ρ) (hρsq : ρ ^ 2 = (1 - p) / (1 - q)) (K : ℕ) (hK : 1 ≤ K)
    (hih : Ring.choose p (2 * K) ≤ (p / q) * Ring.choose q (2 * K) * ρ ^ (2 * K)) :
    Ring.choose p (2 * (K + 1)) ≤
      (p / q) * Ring.choose q (2 * (K + 1)) * ρ ^ (2 * (K + 1)) := by
  have hp0 : 0 < p := hq.trans hqp
  have hq1 : q < 1 := hqp.trans hp
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hm1 : 0 ≤ ((2 * K + 1 : ℕ) : ℝ) - q := by push_cast; linarith
  have hmp0 : 0 ≤ ((2 * K : ℕ) : ℝ) - p := by push_cast; linarith
  have hmp1 : 0 ≤ ((2 * K + 1 : ℕ) : ℝ) - p := by push_cast; linarith
  -- the two factors introduced by Pascal's recurrence shrink by at least `ρ ^ 2`
  have hfac : ρ ^ 2 * ((((2 * K : ℕ) : ℝ) - q) * (((2 * K + 1 : ℕ) : ℝ) - q)) ≤
      (((2 * K : ℕ) : ℝ) - p) * (((2 * K + 1 : ℕ) : ℝ) - p) := by
    calc
      ρ ^ 2 * ((((2 * K : ℕ) : ℝ) - q) * (((2 * K + 1 : ℕ) : ℝ) - q)) =
          (ρ * (((2 * K : ℕ) : ℝ) - q)) * (ρ * (((2 * K + 1 : ℕ) : ℝ) - q)) := by ring
      _ ≤ (((2 * K : ℕ) : ℝ) - p) * (((2 * K + 1 : ℕ) : ℝ) - p) :=
        mul_le_mul (borell_factor_bound p q ρ hq hqp hp hρ0 hρsq (2 * K) (by omega))
          (borell_factor_bound p q ρ hq hqp hp hρ0 hρsq (2 * K + 1) (by omega))
          (mul_nonneg hρ0 hm1) hmp0
  -- the comparison term is nonpositive, so multiplying by it reverses `hfac`
  have hrq_nonpos : (p / q) * Ring.choose q (2 * K) * ρ ^ (2 * K) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (div_nonneg hp0.le hq.le)
        (ring_choose_even_nonpos q hq hq1 K hK))
      (pow_nonneg hρ0 _)
  have hnumle :
      Ring.choose p (2 * K) * (p - (2 * K : ℕ)) * (p - (2 * K + 1 : ℕ)) ≤
        (p / q) * (Ring.choose q (2 * K) * (q - (2 * K : ℕ)) *
          (q - (2 * K + 1 : ℕ))) * ρ ^ (2 * (K + 1)) := by
    calc
      Ring.choose p (2 * K) * (p - (2 * K : ℕ)) * (p - (2 * K + 1 : ℕ)) =
          Ring.choose p (2 * K) *
            ((((2 * K : ℕ) : ℝ) - p) * (((2 * K + 1 : ℕ) : ℝ) - p)) := by ring
      _ ≤ ((p / q) * Ring.choose q (2 * K) * ρ ^ (2 * K)) *
          ((((2 * K : ℕ) : ℝ) - p) * (((2 * K + 1 : ℕ) : ℝ) - p)) :=
        mul_le_mul_of_nonneg_right hih (mul_nonneg hmp0 hmp1)
      _ ≤ ((p / q) * Ring.choose q (2 * K) * ρ ^ (2 * K)) *
          (ρ ^ 2 * ((((2 * K : ℕ) : ℝ) - q) * (((2 * K + 1 : ℕ) : ℝ) - q))) :=
        mul_le_mul_of_nonpos_left hfac hrq_nonpos
      _ = (p / q) * (Ring.choose q (2 * K) * (q - (2 * K : ℕ)) *
          (q - (2 * K + 1 : ℕ))) * ρ ^ (2 * (K + 1)) := by
        rw [show 2 * (K + 1) = 2 * K + 2 by omega, pow_add]
        ring
  rw [ring_choose_even_succ p K, ring_choose_even_succ q K]
  convert div_le_div_of_nonneg_right hnumle
    (by positivity : (0:ℝ) ≤ (((2 * K + 1 : ℕ) : ℝ) * ((2 * K + 2 : ℕ) : ℝ))) using 1
  ring

/-- Coefficientwise comparison of the two even Taylor series in Borell's proof. -/
private lemma choose_even_ratio_le (p q ρ : ℝ) (hq : 0 < q) (hqp : q < p) (hp : p < 1)
    (hρ0 : 0 ≤ ρ) (hρsq : ρ ^ 2 = (1 - p) / (1 - q)) :
    ∀ k : ℕ, 1 ≤ k →
      Ring.choose p (2 * k) ≤ (p / q) * Ring.choose q (2 * k) * ρ ^ (2 * k) := by
  have hq1 : q < 1 := hqp.trans hp
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
      match k with
      | 0 =>
          rw [ring_choose_two, ring_choose_two]
          field_simp [hq.ne', (sub_pos.mpr hq1).ne'] at hρsq ⊢
          norm_num [pow_two] at hρsq ⊢
          nlinarith
      | (k + 1) =>
          exact choose_even_ratio_step p q ρ hq hqp hp hρ0 hρsq (k + 1) (by omega)
            (ih (by omega))

/-- Lemma A.1 away from the endpoints `a = ±1`.  Expand both sides in even
powers of `a` and compare coefficients with `choose_even_ratio_le`. -/
lemma reverse_two_point_normalized (p q ρ a : ℝ)
    (hq : 0 < q) (hqp : q < p) (hp : p < 1)
    (hρ0 : 0 ≤ ρ) (hρsq : ρ ^ 2 = (1 - p) / (1 - q))
    (ha : |a| < 1) :
    lpMean q (noiseOp ρ (fun x : BoolCube 1 ↦ 1 + a * boolToSign (x 0))) ≥
      lpMean p (fun x : BoolCube 1 ↦ 1 + a * boolToSign (x 0)) := by
  have hp0 : 0 < p := hq.trans hqp
  have hq1 : q < 1 := hqp.trans hp
  have hρ1 : ρ < 1 := by
    have : ρ ^ 2 < 1 := by rw [hρsq, div_lt_one (sub_pos.mpr hq1)]; linarith
    nlinarith [sq_nonneg ρ]
  have hρa : |ρ * a| < 1 := by
    rw [abs_mul, abs_of_nonneg hρ0]
    nlinarith [abs_nonneg a]
  -- the two Taylor series, with their constant terms split off
  have hsump := summable_choose_even (s := p) (x := a) ha
  have hsumq := summable_choose_even (s := q) (x := ρ * a) hρa
  have hPseries : ((1 + a) ^ p + (1 - a) ^ p) / 2 =
      1 + ∑' k : ℕ, Ring.choose p (2 * (k + 1)) * a ^ (2 * (k + 1)) := by
    rw [even_part_rpow_eq_tsum ha, hsump.tsum_eq_zero_add]
    simp
  have hQseries : ((1 + ρ * a) ^ q + (1 - ρ * a) ^ q) / 2 =
      1 + ∑' k : ℕ, Ring.choose q (2 * (k + 1)) * (ρ * a) ^ (2 * (k + 1)) := by
    rw [even_part_rpow_eq_tsum hρa, hsumq.tsum_eq_zero_add]
    simp
  -- comparison of the two tails
  have hterm (k : ℕ) :
      Ring.choose p (2 * (k + 1)) * a ^ (2 * (k + 1)) ≤
        (p / q) * (Ring.choose q (2 * (k + 1)) * (ρ * a) ^ (2 * (k + 1))) := by
    calc
      Ring.choose p (2 * (k + 1)) * a ^ (2 * (k + 1)) ≤
          ((p / q) * Ring.choose q (2 * (k + 1)) * ρ ^ (2 * (k + 1))) * a ^ (2 * (k + 1)) :=
        mul_le_mul_of_nonneg_right
          (choose_even_ratio_le p q ρ hq hqp hp hρ0 hρsq (k + 1) (by omega))
          (by rw [show 2 * (k + 1) = (k + 1) + (k + 1) by omega, pow_add]; exact mul_self_nonneg _)
      _ = (p / q) * (Ring.choose q (2 * (k + 1)) * (ρ * a) ^ (2 * (k + 1))) := by
        rw [mul_pow]; ring
  have htail :
      (∑' k : ℕ, Ring.choose p (2 * (k + 1)) * a ^ (2 * (k + 1))) ≤
        (p / q) * ∑' k : ℕ, Ring.choose q (2 * (k + 1)) * (ρ * a) ^ (2 * (k + 1)) := by
    rw [← tsum_mul_left]
    exact (hsump.comp_injective (add_left_injective 1)).tsum_le_tsum hterm
      ((hsumq.comp_injective (add_left_injective 1)).mul_left (p / q))
  -- the symmetrized moments are positive, and the tail comparison plus the
  -- tangent line inequality at `1` compares them
  obtain ⟨ha1, ha2⟩ := abs_lt.mp ha
  obtain ⟨hρa1, hρa2⟩ := abs_lt.mp hρa
  have hPpos : 0 < ((1 + a) ^ p + (1 - a) ^ p) / 2 := by
    have := Real.rpow_pos_of_pos (show (0:ℝ) < 1 + a by linarith) p
    have := Real.rpow_pos_of_pos (show (0:ℝ) < 1 - a by linarith) p
    linarith
  have hQpos : 0 < ((1 + ρ * a) ^ q + (1 - ρ * a) ^ q) / 2 := by
    have := Real.rpow_pos_of_pos (show (0:ℝ) < 1 + ρ * a by linarith) q
    have := Real.rpow_pos_of_pos (show (0:ℝ) < 1 - ρ * a by linarith) q
    linarith
  have hPQ : ((1 + a) ^ p + (1 - a) ^ p) / 2 ≤
      (((1 + ρ * a) ^ q + (1 - ρ * a) ^ q) / 2) ^ (p / q) := by
    calc
      ((1 + a) ^ p + (1 - a) ^ p) / 2 ≤
          1 + (p / q) * ((((1 + ρ * a) ^ q + (1 - ρ * a) ^ q) / 2) - 1) := by
        rw [hPseries, hQseries]; linarith
      _ ≤ (((1 + ρ * a) ^ q + (1 - ρ * a) ^ q) / 2) ^ (p / q) := by
        simpa using one_add_mul_self_le_rpow_one_add
          (s := (((1 + ρ * a) ^ q + (1 - ρ * a) ^ q) / 2) - 1) (by linarith)
          ((le_div_iff₀ hq).2 (by simpa using hqp.le))
  rw [ge_iff_le, lpMean_of_pos q hq, lpMean_of_pos p hp0, noiseOp_affine_one_bit,
    expect_abs_rpow_affine q (ρ * a) hρa, expect_abs_rpow_affine p a ha]
  refine (Real.rpow_le_rpow hPpos.le hPQ (by positivity)).trans_eq ?_
  rw [← Real.rpow_mul hQpos.le, show p / q * (1 / p) = 1 / q by field_simp]

/-- Every point of the one-bit cube is one of the two constant strings. -/
private lemma boolCube_one_cases (x : BoolCube 1) :
    x = (fun _ ↦ false) ∨ x = (fun _ ↦ true) := by
  cases hx : x 0
  · exact Or.inl (by funext i; fin_cases i; exact hx)
  · exact Or.inr (by funext i; fin_cases i; exact hx)

/-- A nonzero nonnegative one-bit function has the form `c (1 + a χ)` with
`c > 0` and `|a| ≤ 1`. -/
lemma normalize_one_bit (f : BooleanFunc 1) (hf : IsNonnegative f) (hf0 : f ≠ 0) :
    ∃ c a : ℝ, 0 < c ∧ -1 ≤ a ∧ a ≤ 1 ∧
      f = fun x ↦ c * (1 + a * boolToSign (x 0)) := by
  set u := f (fun _ ↦ false)
  set v := f (fun _ ↦ true)
  have hu : 0 ≤ u := hf _
  have hv : 0 ≤ v := hf _
  have huv : 0 < u + v := by
    rcases (by linarith : (0:ℝ) ≤ u + v).lt_or_eq with h | h
    · exact h
    · refine absurd (funext fun x ↦ ?_) hf0
      rcases boolCube_one_cases x with rfl | rfl
      · show u = 0; linarith
      · show v = 0; linarith
  refine ⟨(u + v) / 2, (u - v) / (u + v), by linarith, ?_, ?_, funext fun x ↦ ?_⟩
  · rw [le_div_iff₀ huv]; linarith
  · rw [div_le_iff₀ huv]; linarith
  · rcases boolCube_one_cases x with rfl | rfl <;>
      simp only [boolToSign_false, boolToSign_true] <;>
      field_simp <;> ring

/-- The one-bit power means depend continuously on the Fourier coefficient. -/
private lemma continuous_lpMean_affine (s : ℝ) (hs : 0 < s) :
    Continuous fun a : ℝ ↦ lpMean s (fun x : BoolCube 1 ↦ 1 + a * boolToSign (x 0)) := by
  simp_rw [lpMean_of_pos s hs]
  unfold expect
  refine (Real.continuous_rpow_const (by positivity)).comp
    (continuous_const.mul (continuous_finset_sum _ fun x _ ↦ ?_))
  exact (Real.continuous_rpow_const hs.le).comp
    (Continuous.abs (continuous_const.add (continuous_id.mul continuous_const)))

/-- The complete two-point reverse Bonami-Beckner inequality.  Homogeneity and
continuity discharge the zero function and the endpoints `a = ±1`.

**Source:** [OD14, Exs. 10.6--10.9]. -/
theorem reverse_bonami_beckner_one_bit (p q ρ : ℝ)
    (hq : 0 < q) (hqp : q < p) (hp : p < 1)
    (hρ0 : 0 ≤ ρ) (hρsq : ρ ^ 2 = (1 - p) / (1 - q))
    (f : BooleanFunc 1) (hf : IsNonnegative f) :
    lpMean q (noiseOp ρ f) ≥ lpMean p f := by
  have hp0 : 0 < p := hq.trans hqp
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [lpMean_of_pos p hp0, lpMean_of_pos q hq,
      show noiseOp ρ (0 : BooleanFunc 1) = 0 by
        funext x; simp [noiseOp, fourierCoeff, innerProduct, expect]]
    unfold expect
    simp only [Pi.zero_apply, abs_zero, Real.zero_rpow hp0.ne', Real.zero_rpow hq.ne',
      Finset.sum_const_zero, mul_zero, one_div]
    rw [Real.zero_rpow (inv_ne_zero hp0.ne'), Real.zero_rpow (inv_ne_zero hq.ne')]
  obtain ⟨c, a, hc, ha0, ha1, hfa⟩ := normalize_one_bit f hf hf0
  -- the inequality for `|a| < 1` extends to `a = ±1` by continuity
  have hclosed : IsClosed {b : ℝ |
      lpMean p (fun x : BoolCube 1 ↦ 1 + b * boolToSign (x 0)) ≤
        lpMean q (noiseOp ρ (fun x : BoolCube 1 ↦ 1 + b * boolToSign (x 0)))} :=
    isClosed_le (continuous_lpMean_affine p hp0)
      (by simpa only [noiseOp_affine_one_bit] using
        (continuous_lpMean_affine q hq).comp (continuous_const.mul continuous_id))
  have hIoo : Set.Ioo (-1 : ℝ) 1 ⊆ {b : ℝ |
      lpMean p (fun x : BoolCube 1 ↦ 1 + b * boolToSign (x 0)) ≤
        lpMean q (noiseOp ρ (fun x : BoolCube 1 ↦ 1 + b * boolToSign (x 0)))} := fun b hb ↦
    reverse_two_point_normalized p q ρ b hq hqp hp hρ0 hρsq (by rw [abs_lt]; exact hb)
  have hIcc := hclosed.closure_subset_iff.mpr hIoo
  rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] at hIcc
  rw [hfa, noiseOp_const_mul, lpMean_const_mul q c hq hc, lpMean_const_mul p c hp0 hc]
  exact mul_le_mul_of_nonneg_left (hIcc ⟨ha0, ha1⟩) hc.le

/-! ### Tensorization -/

/-- Minkowski's inequality for finite sums with exponent `r ≥ 1`. -/
private lemma finset_Lr_sum_le {ι κ : Type*} [DecidableEq ι] (r : ℝ) (hr : 1 ≤ r)
    (s : Finset ι) (t : Finset κ) (a : ι → κ → ℝ) (ha : ∀ i ∈ s, ∀ j ∈ t, 0 ≤ a i j) :
    (∑ j ∈ t, (∑ i ∈ s, a i j) ^ r) ^ (1 / r) ≤
      ∑ i ∈ s, (∑ j ∈ t, a i j ^ r) ^ (1 / r) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow hr0.ne', Real.zero_rpow (inv_ne_zero hr0.ne')]
  | @insert i s his ih =>
      simp only [Finset.sum_insert his]
      calc
        (∑ j ∈ t, (a i j + ∑ k ∈ s, a k j) ^ r) ^ (1 / r) ≤
            (∑ j ∈ t, a i j ^ r) ^ (1 / r) + (∑ j ∈ t, (∑ k ∈ s, a k j) ^ r) ^ (1 / r) :=
          Real.Lp_add_le_of_nonneg t hr (fun j hj ↦ ha i (Finset.mem_insert_self i s) j hj)
            (fun j hj ↦ Finset.sum_nonneg fun k hk ↦ ha k (Finset.mem_insert_of_mem hk) j hj)
        _ ≤ (∑ j ∈ t, a i j ^ r) ^ (1 / r) + ∑ k ∈ s, (∑ j ∈ t, a k j ^ r) ^ (1 / r) :=
          add_le_add_left (ih fun k hk j hj ↦ ha k (Finset.mem_insert_of_mem hk) j hj) _

/-- Reverse Minkowski in the mixed-norm form needed to exchange the last bit
with the first `n` bits during tensorization.

**Source:** [OD14, Exs. 10.6--10.9 (tensorization argument)]. -/
lemma reverse_minkowski_mixed (p q : ℝ) (hq : 0 < q) (hqp : q ≤ p)
    (F : BoolCube n → BoolCube 1 → ℝ) (hF : ∀ x y, 0 ≤ F x y) :
    lpMean q (fun x ↦ lpMean p (fun y ↦ F x y)) ≥
      lpMean p (fun y ↦ lpMean q (fun x ↦ F x y)) := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le hq hqp
  set r := p / q with hr_def
  have hr : 1 ≤ r := (le_div_iff₀ hq).2 (by simpa using hqp)
  have hEp (x : BoolCube n) : 0 ≤ expect fun y : BoolCube 1 ↦ F x y ^ p :=
    by
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun y _ ↦ Real.rpow_nonneg (hF x y) p
  have hEq (y : BoolCube 1) : 0 ≤ expect fun x : BoolCube n ↦ F x y ^ q :=
    by
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (hF x y) q
  rw [lpMean_of_pos q hq, lpMean_of_pos p hp0]
  simp_rw [lpMean_of_pos p hp0, lpMean_of_pos q hq, abs_of_nonneg (hF _ _),
    abs_of_nonneg (Real.rpow_nonneg (hEp _) _), abs_of_nonneg (Real.rpow_nonneg (hEq _) _),
    ← Real.rpow_mul (hEp _), ← Real.rpow_mul (hEq _)]
  ring_nf
  have hA0 : 0 ≤ expect fun x : BoolCube n ↦
      (expect fun y : BoolCube 1 ↦ F x y ^ p) ^ (p⁻¹ * q) :=
    by
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (hEp x) _
  have hB0 : 0 ≤ expect fun y : BoolCube 1 ↦
      (expect fun x : BoolCube n ↦ F x y ^ q) ^ (p * q⁻¹) :=
    by
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun y _ ↦ Real.rpow_nonneg (hEq y) _
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hA0 _) hq).1
  rw [← Real.rpow_mul hB0, ← Real.rpow_mul hA0]
  ring_nf
  rw [show q * p⁻¹ = 1 / r by rw [hr_def]; field_simp, show q * q⁻¹ = 1 by field_simp,
    Real.rpow_one]
  -- both sides are now unweighted finite sums, where Minkowski applies
  have hraw := finset_Lr_sum_le r hr Finset.univ Finset.univ (fun x y ↦ F x y ^ q)
    (fun x _ y _ ↦ Real.rpow_nonneg (hF x y) q)
  have hwn : (0:ℝ) ≤ uniformWeight n := pow_nonneg (by norm_num) _
  have hw1 : (0:ℝ) ≤ uniformWeight 1 := pow_nonneg (by norm_num) _
  unfold expect
  calc
    (uniformWeight 1 * ∑ y : BoolCube 1,
        (uniformWeight n * ∑ x : BoolCube n, F x y ^ q) ^ r) ^ (1 / r) =
        uniformWeight n * uniformWeight 1 ^ (1 / r) *
          (∑ y : BoolCube 1, (∑ x : BoolCube n, F x y ^ q) ^ r) ^ (1 / r) := by
      have hsum : 0 ≤ ∑ y : BoolCube 1, (∑ x : BoolCube n, F x y ^ q) ^ r :=
        Finset.sum_nonneg fun y _ ↦ Real.rpow_nonneg
          (Finset.sum_nonneg fun x _ ↦ Real.rpow_nonneg (hF x y) q) r
      rw [show (∑ y : BoolCube 1, (uniformWeight n * ∑ x : BoolCube n, F x y ^ q) ^ r) =
          uniformWeight n ^ r * ∑ y : BoolCube 1, (∑ x : BoolCube n, F x y ^ q) ^ r by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ ↦ Real.mul_rpow hwn
          (Finset.sum_nonneg fun x _ ↦ Real.rpow_nonneg (hF x y) q)]
      rw [Real.mul_rpow hw1 (mul_nonneg (Real.rpow_nonneg hwn r) hsum),
        Real.mul_rpow (Real.rpow_nonneg hwn r) hsum, ← Real.rpow_mul hwn,
        show r * (1 / r) = 1 by field_simp, Real.rpow_one]
      ring
    _ ≤ uniformWeight n * uniformWeight 1 ^ (1 / r) *
          ∑ x : BoolCube n, (∑ y : BoolCube 1, (F x y ^ q) ^ r) ^ (1 / r) :=
      mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = uniformWeight n * ∑ x : BoolCube n,
          (uniformWeight 1 * ∑ y : BoolCube 1, F x y ^ p) ^ (1 / r) := by
      rw [mul_assoc, Finset.mul_sum]
      refine congrArg _ (Finset.sum_congr rfl fun x _ ↦ ?_)
      rw [Real.mul_rpow hw1 (Finset.sum_nonneg fun y _ ↦ Real.rpow_nonneg (hF x y) p)]
      refine congrArg _ (congrArg (fun z : ℝ ↦ z ^ (1 / r)) (Finset.sum_congr rfl fun y _ ↦ ?_))
      rw [← Real.rpow_mul (hF x y), hr_def]
      congr 1
      field_simp

/-- A one-bit reverse bound tensorizes to every Boolean cube.  The inductive
step splits off the last bit with `noiseOp_snoc_slice` and `lpMean_collapse_last`,
then exchanges the two blocks with `reverse_minkowski_mixed`.

**Source:** [OD14, Exs. 10.6--10.9]. -/
theorem tensorize_reverse_bonami_beckner (p q ρ : ℝ)
    (hq : 0 < q) (hqp : q < p)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hone : ∀ f : BooleanFunc 1, IsNonnegative f →
      lpMean q (noiseOp ρ f) ≥ lpMean p f)
    (f : BooleanFunc n) (hf : IsNonnegative f) :
    lpMean q (noiseOp ρ f) ≥ lpMean p f := by
  have hp0 : 0 < p := hq.trans hqp
  induction n with
  | zero => rw [noiseOp_dim_zero, lpMean_dim_zero q hq f hf, lpMean_dim_zero p hp0 f hf]
  | succ k ih =>
      set F : BoolCube k → BoolCube 1 → ℝ :=
        fun x y ↦ noiseOp ρ (restrictLast f (y 0)) x
      have hF (x : BoolCube k) (y : BoolCube 1) : 0 ≤ F x y :=
        noiseOp_nonneg hρ0 hρ1 (fun z ↦ hf (Fin.snoc z (y 0))) x
      calc
        lpMean q (noiseOp ρ f) =
            lpMean q (fun x : BoolCube k ↦ lpMean q (noiseOp ρ (fun y : BoolCube 1 ↦ F x y))) := by
          rw [lpMean_collapse_last q hq (noiseOp ρ f)]
          exact congrArg _ (funext fun x ↦ congrArg _ (funext fun y ↦ noiseOp_snoc_slice ρ f x y))
        _ ≥ lpMean q (fun x : BoolCube k ↦ lpMean p (fun y : BoolCube 1 ↦ F x y)) :=
          lpMean_mono q hq (fun x ↦ lpMean_nonneg p hp0 _) fun x ↦ hone (fun y ↦ F x y) (hF x)
        _ ≥ lpMean p (fun y : BoolCube 1 ↦ lpMean q (fun x : BoolCube k ↦ F x y)) :=
          reverse_minkowski_mixed p q hq hqp.le F hF
        _ ≥ lpMean p (fun y : BoolCube 1 ↦
              lpMean p (fun x : BoolCube k ↦ restrictLast f (y 0) x)) :=
          lpMean_mono p hp0 (fun y ↦ lpMean_nonneg p hp0 _) fun y ↦
            ih (restrictLast f (y 0)) fun x ↦ hf (Fin.snoc x (y 0))
        _ = lpMean p (fun x : BoolCube k ↦
              lpMean p (fun y : BoolCube 1 ↦ f (Fin.snoc x (y 0)))) :=
          (lpMean_comm p hp0 fun x y ↦ f (Fin.snoc x (y 0))).symm
        _ = lpMean p f := (lpMean_collapse_last p hp0 f).symm

/-- States reverse hypercontractivity at sharp correlation for `0 < q < p < 1`.

**Source:** [OD14, Exs. 10.6--10.9]. -/
theorem reverse_bonami_beckner_positive_sharp (p q ρ : ℝ)
    (hq : 0 < q) (hqp : q < p) (hp : p < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρsq : ρ ^ 2 = (1 - p) / (1 - q))
    (f : BooleanFunc n) (hf : IsNonnegative f) :
    lpMean q (noiseOp ρ f) ≥ lpMean p f :=
  tensorize_reverse_bonami_beckner p q ρ hq hqp hρ0 hρ1
    (fun g hg ↦ reverse_bonami_beckner_one_bit p q ρ hq hqp hp hρ0 hρsq g hg) f hf

/-! ### Reverse Hölder and the general statement -/

/-- More noise can only increase an `L^q` mean when `q < 1`.  Together with
`noiseOp_compose`, this relaxes equality in the correlation constraint. -/
lemma lpMean_noise_antitone (q ρ σ : ℝ) (hq : q < 1)
    (hρ0 : 0 ≤ ρ) (hρσ : ρ ≤ σ) (hσ1 : σ ≤ 1)
    (f : BooleanFunc n) (hf : IsNonnegative f) :
    lpMean q (noiseOp ρ f) ≥ lpMean q (noiseOp σ f) := by
  classical
  have mean_nonneg : ∀ (r : ℝ) (u : BooleanFunc n), 0 ≤ lpMean r u := by
    intro r u
    unfold lpMean
    split_ifs
    · exact le_rfl
    · positivity
    · exact Real.rpow_nonneg (by
        rw [expect_eq_fintypeExpect]
        exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (abs_nonneg (u x)) r) _
  have expect_pos : ∀ (u : BooleanFunc n), (∀ x, 0 < u x) → 0 < expect u := by
    intro u hu
    unfold expect uniformWeight
    exact mul_pos (pow_pos (by norm_num) _)
      (Finset.sum_pos (fun x _ ↦ hu x) Finset.univ_nonempty)
  have noise_positive : ∀ (τ : ℝ), 0 ≤ τ → τ ≤ 1 → ∀ (u : BooleanFunc n),
      (∀ x, 0 < u x) → ∀ x, 0 < noiseOp τ u x := by
    intro τ hτ0 hτ1 u hu x
    rw [GeneralHypercontractivity.noiseOp_eq_kernel_sum]
    have hkdiag : 0 < GeneralHypercontractivity.noiseKernel τ x x := by
      unfold GeneralHypercontractivity.noiseKernel
      apply Finset.prod_pos
      intro i hi
      cases x i <;> norm_num [boolToSign] <;> linarith
    calc
      0 < GeneralHypercontractivity.noiseKernel τ x x * u x := mul_pos hkdiag (hu x)
      _ ≤ ∑ y : BoolCube n, GeneralHypercontractivity.noiseKernel τ x y * u y := by
        have h := Finset.single_le_sum
          (s := Finset.univ)
          (fun y _ ↦ mul_nonneg
            (GeneralHypercontractivity.noiseKernel_nonneg hτ0 hτ1 x y) (hu y).le)
          (Finset.mem_univ x)
        simpa using h
  have kernel_double_sum : ∀ (τ : ℝ), 0 ≤ τ → τ ≤ 1 → ∀ (u : BooleanFunc n),
      ∑ x : BoolCube n, ∑ y : BoolCube n,
          GeneralHypercontractivity.noiseKernel τ x y * u y = ∑ y : BoolCube n, u y := by
    intro τ hτ0 hτ1 u
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    rw [← Finset.sum_mul,
      GeneralHypercontractivity.noiseKernel_sum_left hτ0 hτ1 y, one_mul]
  have convex_rpow_of_neg : ∀ {r : ℝ}, r < 0 →
      ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ ↦ x ^ r) := by
    intro r hr
    have hneglog : ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ ↦ -Real.log x) := by
      simpa only [Pi.neg_apply] using strictConcaveOn_log_Ioi.concaveOn.neg
    have hinner : ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ ↦ r * Real.log x) := by
      have h := hneglog.smul (show 0 ≤ -r by linarith)
      convert h using 1
      ext x
      simp only [smul_eq_mul]
      ring
    refine ⟨convex_Ioi 0, ?_⟩
    intro x hx y hy a b ha hb hab
    have hinner_le := hinner.2 hx hy ha hb hab
    have hcombo : 0 < a • x + b • y := by
      simp only [smul_eq_mul]
      rcases eq_or_lt_of_le ha with ha0 | ha'
      · subst a
        norm_num at hab ⊢
        simpa [hab] using hy
      · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx) (mul_nonneg hb hy.le)
    calc
      (a • x + b • y) ^ r = Real.exp (r * Real.log (a • x + b • y)) := by
        rw [Real.rpow_def_of_pos hcombo]
        congr 1
        ring
      _ ≤ Real.exp (a • (r * Real.log x) + b • (r * Real.log y)) :=
        Real.exp_le_exp.mpr hinner_le
      _ ≤ a • Real.exp (r * Real.log x) + b • Real.exp (r * Real.log y) :=
        convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
      _ = a • x ^ r + b • y ^ r := by
        rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy]
        congr 2 <;> congr 1 <;> ring
  have expect_rpow_le_noise : ∀ (r τ : ℝ), 0 < r → r < 1 → 0 ≤ τ → τ ≤ 1 →
      ∀ (u : BooleanFunc n), IsNonnegative u →
        expect (fun x ↦ u x ^ r) ≤ expect (fun x ↦ noiseOp τ u x ^ r) := by
    intro r τ hr0 hr1 hτ0 hτ1 u hu
    unfold expect
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by norm_num) _)
    rw [← kernel_double_sum τ hτ0 hτ1 (fun x ↦ u x ^ r)]
    refine Finset.sum_le_sum fun x _ ↦ ?_
    rw [GeneralHypercontractivity.noiseOp_eq_kernel_sum]
    exact (Real.concaveOn_rpow hr0.le hr1.le).le_map_sum
      (fun y _ ↦ GeneralHypercontractivity.noiseKernel_nonneg hτ0 hτ1 x y)
      (GeneralHypercontractivity.noiseKernel_sum_right hτ0 hτ1 x)
      (fun y _ ↦ hu y)
  have expect_noise_le_rpow : ∀ (r τ : ℝ), r < 0 → 0 ≤ τ → τ ≤ 1 →
      ∀ (u : BooleanFunc n), (∀ x, 0 < u x) →
        expect (fun x ↦ noiseOp τ u x ^ r) ≤ expect (fun x ↦ u x ^ r) := by
    intro r τ hr hτ0 hτ1 u hu
    unfold expect
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by norm_num) _)
    rw [← kernel_double_sum τ hτ0 hτ1 (fun x ↦ u x ^ r)]
    refine Finset.sum_le_sum fun x _ ↦ ?_
    rw [GeneralHypercontractivity.noiseOp_eq_kernel_sum]
    exact (convex_rpow_of_neg hr).map_sum_le
      (fun y _ ↦ GeneralHypercontractivity.noiseKernel_nonneg hτ0 hτ1 x y)
      (GeneralHypercontractivity.noiseKernel_sum_right hτ0 hτ1 x)
      (fun y _ ↦ hu y)
  have expect_log_le_noise : ∀ (τ : ℝ), 0 ≤ τ → τ ≤ 1 →
      ∀ (u : BooleanFunc n), (∀ x, 0 < u x) →
        expect (fun x ↦ Real.log (u x)) ≤
          expect (fun x ↦ Real.log (noiseOp τ u x)) := by
    intro τ hτ0 hτ1 u hu
    unfold expect
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by norm_num) _)
    rw [← kernel_double_sum τ hτ0 hτ1 (fun x ↦ Real.log (u x))]
    refine Finset.sum_le_sum fun x _ ↦ ?_
    rw [GeneralHypercontractivity.noiseOp_eq_kernel_sum]
    exact strictConcaveOn_log_Ioi.concaveOn.le_map_sum
      (fun y _ ↦ GeneralHypercontractivity.noiseKernel_nonneg hτ0 hτ1 x y)
      (GeneralHypercontractivity.noiseKernel_sum_right hτ0 hτ1 x)
      (fun y _ ↦ hu y)
  have one_step : ∀ (r τ : ℝ), r < 1 → 0 ≤ τ → τ ≤ 1 →
      ∀ (u : BooleanFunc n), IsNonnegative u →
        lpMean r (noiseOp τ u) ≥ lpMean r u := by
    intro r τ hr hτ0 hτ1 u hu
    have hnoise := noiseOp_nonneg hτ0 hτ1 hu
    by_cases hrpos : 0 < r
    · rw [lpMean_of_pos r hrpos, lpMean_of_pos r hrpos]
      simp_rw [abs_of_nonneg (hnoise _), abs_of_nonneg (hu _)]
      exact Real.rpow_le_rpow
        (by
          rw [expect_eq_fintypeExpect]
          exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (hu x) r)
        (expect_rpow_le_noise r τ hrpos hr hτ0 hτ1 u hu)
        (by positivity)
    · have hrnonpos : r ≤ 0 := le_of_not_gt hrpos
      by_cases hz : ∃ x, u x = 0
      · rw [show lpMean r u = 0 by simp [lpMean, hz, hrnonpos]]
        exact mean_nonneg r _
      · have hupos : ∀ x, 0 < u x := fun x ↦
          lt_of_le_of_ne (hu x) (Ne.symm (not_exists.mp hz x))
        have hnpos := noise_positive τ hτ0 hτ1 u hupos
        have hnz : ¬∃ x, noiseOp τ u x = 0 := not_exists.mpr fun x hx ↦ (hnpos x).ne' hx
        rcases eq_or_lt_of_le hrnonpos with rfl | hrneg
        · rw [show lpMean 0 (noiseOp τ u) =
              Real.exp (expect (fun x ↦ Real.log |noiseOp τ u x|)) by simp [lpMean, hnz],
            show lpMean 0 u = Real.exp (expect (fun x ↦ Real.log |u x|)) by
              simp [lpMean, hz]]
          simp_rw [abs_of_pos (hnpos _), abs_of_pos (hupos _)]
          exact Real.exp_le_exp.mpr (expect_log_le_noise τ hτ0 hτ1 u hupos)
        · rw [show lpMean r (noiseOp τ u) =
              (expect (fun x ↦ |noiseOp τ u x| ^ r)) ^ (1 / r) by
                simp [lpMean, hnz, hrneg.ne],
            show lpMean r u = (expect (fun x ↦ |u x| ^ r)) ^ (1 / r) by
                simp [lpMean, hz, hrneg.ne]]
          simp_rw [abs_of_pos (hnpos _), abs_of_pos (hupos _)]
          exact (Real.rpow_le_rpow_iff_of_neg
            (expect_pos _ fun x ↦ Real.rpow_pos_of_pos (hupos x) r)
            (expect_pos _ fun x ↦ Real.rpow_pos_of_pos (hnpos x) r)
            (one_div_neg.mpr hrneg)).2
              (expect_noise_le_rpow r τ hrneg hτ0 hτ1 u hupos)
  have hσ0 : 0 ≤ σ := le_trans hρ0 hρσ
  by_cases hσzero : σ = 0
  · have hρzero : ρ = 0 := le_antisymm (by simpa [hσzero] using hρσ) hρ0
    subst σ
    subst ρ
    rfl
  · let τ : ℝ := ρ / σ
    have hτ0 : 0 ≤ τ := div_nonneg hρ0 hσ0
    have hσpos : 0 < σ := lt_of_le_of_ne hσ0 (Ne.symm hσzero)
    have hτ1 : τ ≤ 1 := (div_le_one hσpos).2 hρσ
    have hfac : noiseOp τ (noiseOp σ f) = noiseOp ρ f := by
      rw [noiseOp_compose]
      congr 2
      dsimp [τ]
      field_simp
    rw [← hfac]
    exact one_step q τ hq hτ0 hτ1 (noiseOp σ f)
      (noiseOp_nonneg hσ0 hσ1 hf)

/-- The reverse Young inequality: for `0 < r < 1` and conjugate exponent
`r / (r - 1) < 0` the arithmetic-geometric comparison reverses. -/
private lemma reverse_young {r a b : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ha : 0 ≤ a) (hb : 0 < b) :
    a * b ≥ a ^ r / r + b ^ (r / (r - 1)) / (r / (r - 1)) := by
  have hrm1 : r - 1 ≠ 0 := (sub_neg.mpr hr1).ne
  have hbase : 0 < b ^ (1 / (r - 1)) := Real.rpow_pos_of_pos hb _
  set t : ℝ := a / b ^ (1 / (r - 1)) with ht_def
  have ht : 0 ≤ t := div_nonneg ha hbase.le
  have haeq : a = t * b ^ (1 / (r - 1)) := by rw [ht_def]; field_simp
  -- the tangent line inequality at `t = 1` for the concave power `t ^ r`
  have htan : t ^ r ≤ 1 + r * (t - 1) := by
    simpa using rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith) hr0.le hr1.le
  have haq : a ^ r = t ^ r * b ^ (r / (r - 1)) := by
    rw [haeq, Real.mul_rpow ht hbase.le, ← Real.rpow_mul hb.le]
    congr 2
    ring
  have habeq : a * b = t * b ^ (r / (r - 1)) := by
    calc
      a * b = t * (b ^ (1 / (r - 1)) * b ^ (1 : ℝ)) := by rw [haeq, Real.rpow_one]; ring
      _ = t * b ^ (1 / (r - 1) + 1) := by rw [Real.rpow_add hb]
      _ = t * b ^ (r / (r - 1)) := by
        congr 2
        field_simp
        ring
  rw [haq, habeq]
  field_simp [hr0.ne', hrm1]
  nlinarith [mul_le_mul_of_nonneg_right htan (Real.rpow_nonneg hb.le (r / (r - 1)))]

/-- A nonnegative function with a positive value has positive `r`-th moment. -/
private lemma expect_rpow_pos {r : ℝ} {u : BooleanFunc n} (hu : ∀ x, 0 ≤ u x)
    (hex : ∃ x, 0 < u x) : 0 < expect (fun x ↦ u x ^ r) := by
  obtain ⟨x, hx⟩ := hex
  unfold expect uniformWeight
  exact mul_pos (pow_pos (by norm_num) _)
    (Finset.sum_pos' (fun z _ ↦ Real.rpow_nonneg (hu z) _)
      ⟨x, Finset.mem_univ x, Real.rpow_pos_of_pos hx _⟩)

/-- Dividing by its own `L^r` mean normalizes the `r`-th moment to `1`. -/
private lemma expect_normalized_rpow_eq_one {r : ℝ} (hr0 : r ≠ 0) (u : BooleanFunc n)
    (hu : ∀ x, 0 ≤ u x) (hE : 0 < expect (fun x ↦ u x ^ r)) :
    expect (fun x ↦ (u x / (expect (fun z ↦ u z ^ r)) ^ (1 / r)) ^ r) = 1 := by
  set E := expect (fun z ↦ u z ^ r)
  have hpow : (E ^ (1 / r)) ^ r = E := by
    rw [← Real.rpow_mul hE.le, one_div_mul_cancel hr0, Real.rpow_one]
  simp_rw [Real.div_rpow (hu _) (Real.rpow_pos_of_pos hE _).le, hpow]
  unfold expect
  rw [← Finset.sum_div, ← mul_div_assoc]
  exact div_self hE.ne'

/-- Rescaling both arguments of the inner product. -/
private lemma innerProduct_eq_mul_expect_div (u v : BooleanFunc n) {A B : ℝ}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    innerProduct u v = A * B * expect (fun x ↦ (u x / A) * (v x / B)) := by
  have hx (x : BoolCube n) : u x * v x = A * B * ((u x / A) * (v x / B)) := by field_simp
  unfold innerProduct expect
  simp_rw [hx, ← Finset.mul_sum]
  ring

/-- Reverse Hölder for a positive exponent `r < 1` and its negative conjugate. -/
private lemma reverse_holder_of_pos (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (u v : BooleanFunc n) (hu : IsNonnegative u) (hv : IsNonnegative v) :
    innerProduct u v ≥ lpMean r u * lpMean (r / (r - 1)) v := by
  classical
  set s := r / (r - 1) with hs_def
  have hsneg : s < 0 := div_neg_of_pos_of_neg hr0 (sub_neg.mpr hr1)
  by_cases hupos : ∃ x, 0 < u x
  · by_cases hvzero : ∃ x, v x = 0
    · -- a zero of `v` makes the right-hand side vanish
      rw [show lpMean s v = 0 by simp [lpMean, hvzero, hsneg.le], mul_zero]
      unfold innerProduct
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun x _ ↦ mul_nonneg (hu x) (hv x)
    · have hvpos (x : BoolCube n) : 0 < v x :=
        (hv x).lt_of_ne (Ne.symm (not_exists.mp hvzero x))
      have hEu : 0 < expect (fun x ↦ u x ^ r) := expect_rpow_pos hu hupos
      have hEv : 0 < expect (fun x ↦ v x ^ s) :=
        expect_rpow_pos hv ⟨Classical.arbitrary _, hvpos _⟩
      set A := (expect (fun x ↦ u x ^ r)) ^ (1 / r) with hA_def
      set B := (expect (fun x ↦ v x ^ s)) ^ (1 / s) with hB_def
      have hApos : 0 < A := Real.rpow_pos_of_pos hEu _
      have hBpos : 0 < B := Real.rpow_pos_of_pos hEv _
      -- the pointwise reverse Young inequality, averaged over the cube
      have hone : 1 ≤ expect (fun x ↦ (u x / A) * (v x / B)) := by
        have hright : expect (fun x ↦ (u x / A) ^ r / r + (v x / B) ^ s / s) = 1 := by
          have hnormu := expect_normalized_rpow_eq_one hr0.ne' u hu hEu
          have hnormv := expect_normalized_rpow_eq_one hsneg.ne v hv hEv
          rw [← hA_def] at hnormu
          rw [← hB_def] at hnormv
          unfold expect at hnormu hnormv ⊢
          rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, mul_add,
            ← mul_div_assoc, ← mul_div_assoc, hnormu, hnormv, hs_def]
          field_simp
          ring
        rw [← hright]
        unfold expect
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun x _ ↦ reverse_young hr0 hr1
            (div_nonneg (hu x) hApos.le) (div_pos (hvpos x) hBpos))
          (pow_nonneg (by norm_num) _)
      have hpu : lpMean r u = A := by
        rw [lpMean_of_pos r hr0, hA_def]
        simp_rw [abs_of_nonneg (hu _)]
      have hsv : lpMean s v = B := by
        rw [hB_def]
        simp [lpMean, hvzero, hsneg.ne, abs_of_pos (hvpos _)]
      rw [hpu, hsv, innerProduct_eq_mul_expect_div u v hApos.ne' hBpos.ne']
      nlinarith [mul_le_mul_of_nonneg_left hone (mul_nonneg hApos.le hBpos.le)]
  · -- `u` vanishes identically
    obtain rfl : u = 0 := funext fun x ↦ le_antisymm (not_lt.mp (not_exists.mp hupos x)) (hu x)
    simp [innerProduct, lpMean, expect, uniformWeight, hr0.ne', not_le.mpr hr0]

/-- Reverse Hölder for the extended means.  This is the duality input in
Lemma A.3 and in the two-function corollary.

**Source:** [OD14, Exs. 10.6--10.9]. -/
lemma reverse_holder (p : ℝ) (hp : p < 1) (hp0 : p ≠ 0)
    (f g : BooleanFunc n) (hf : IsNonnegative f) (hg : IsNonnegative g) :
    innerProduct f g ≥ lpMean p f * lpMean (p / (p - 1)) g := by
  rcases lt_or_gt_of_ne hp0 with hpneg | hppos
  · -- for `p < 0` apply the positive case to the conjugate exponent
    have hpm1 : p - 1 ≠ 0 := (sub_neg.mpr hp).ne
    have hq0 : 0 < p / (p - 1) := div_pos_of_neg_of_neg hpneg (sub_neg.mpr hp)
    have hq1 : p / (p - 1) < 1 := by
      rw [div_lt_iff_of_neg (sub_neg.mpr hp)]
      linarith
    have hconj : (p / (p - 1)) / (p / (p - 1) - 1) = p := by field_simp; ring
    have h := reverse_holder_of_pos (p / (p - 1)) hq0 hq1 g f hg hf
    rw [hconj] at h
    simpa only [BooleanAnalysis.innerProduct_comm, mul_comm] using h
  · exact reverse_holder_of_pos p hppos hp f g hf hg

/-- Lemma A.3: continuity at `p = 0, 1`, reverse Hölder for nonpositive
exponents, and the semigroup factorization across zero reduce the full result
to `reverse_bonami_beckner_positive_sharp`.

**Source:** [OD14, Exs. 10.6--10.9]. -/
lemma extend_reverse_bonami_beckner (p q ρ : ℝ)
    (hq : q < 1) (hqp : q ≤ p) (hp : p ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρsq : ρ ^ 2 ≤ (1 - p) / (1 - q))
    (f : BooleanFunc n) (hf : IsNonnegative f) :
    lpMean q (noiseOp ρ f) ≥ lpMean p f := by
  classical
  have mean_nonneg (r : ℝ) (u : BooleanFunc n) : 0 ≤ lpMean r u := by
    unfold lpMean
    split_ifs
    · exact le_rfl
    · positivity
    · exact Real.rpow_nonneg (by
        rw [expect_eq_fintypeExpect]
        exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (abs_nonneg _) r) _
  have noise_strict_pos : ∀ (R : ℝ), 0 ≤ R → R < 1 →
      ∀ (u : BooleanFunc n), IsNonnegative u → (∃ y, 0 < u y) →
        ∀ x, 0 < noiseOp R u x := by
    intro R hR0 hR1 u hu hex x
    rw [GeneralHypercontractivity.noiseOp_eq_kernel_sum]
    have hkernel (y : BoolCube n) :
        0 < GeneralHypercontractivity.noiseKernel R x y := by
      unfold GeneralHypercontractivity.noiseKernel
      apply Finset.prod_pos
      intro i hi
      cases x i <;> cases y i <;> norm_num [boolToSign] <;> nlinarith
    exact Finset.sum_pos'
      (fun y _ ↦ mul_nonneg (hkernel y).le (hu y))
      ⟨hex.choose, Finset.mem_univ _, mul_pos (hkernel hex.choose) hex.choose_spec⟩
  have positive_subsharp : ∀ (P Q R : ℝ), 0 < Q → Q < P → P < 1 →
      0 ≤ R → R ≤ 1 → R ^ 2 ≤ (1 - P) / (1 - Q) →
      ∀ (u : BooleanFunc n), IsNonnegative u →
        lpMean Q (noiseOp R u) ≥ lpMean P u := by
    intro P Q R hQ hQP hP hR0 hR1 hRsq u hu
    let S : ℝ := Real.sqrt ((1 - P) / (1 - Q))
    have hden : 0 < 1 - Q := sub_pos.mpr (lt_trans hQP hP)
    have hratio0 : 0 ≤ (1 - P) / (1 - Q) :=
      div_nonneg (sub_nonneg.mpr hP.le) hden.le
    have hS0 : 0 ≤ S := Real.sqrt_nonneg _
    have hSsq : S ^ 2 = (1 - P) / (1 - Q) := Real.sq_sqrt hratio0
    have hS1 : S ≤ 1 := by
      rw [← sq_le_sq₀ hS0 (by norm_num : (0 : ℝ) ≤ 1), hSsq]
      norm_num
      exact (div_le_one hden).2 (by linarith)
    have hRS : R ≤ S := by
      rw [← sq_le_sq₀ hR0 hS0, hSsq]
      exact hRsq
    exact le_trans
      (reverse_bonami_beckner_positive_sharp P Q S hQ hQP hP hS0 hS1 hSsq u hu)
      (lpMean_noise_antitone Q R S (lt_trans hQP hP) hR0 hRS hS1 u hu)
  have lpMean_continuous_zero (u : BooleanFunc n) (hu : ∀ x, 0 < u x) :
      ContinuousAt (fun r : ℝ ↦ lpMean r u) 0 := by
    let M : ℝ → ℝ := fun r ↦ expect (fun x ↦ u x ^ r)
    let A : ℝ := expect (fun x ↦ Real.log (u x))
    have hnz : ¬∃ x, u x = 0 := not_exists.mpr fun x hx ↦ (hu x).ne' hx
    have hM0 : M 0 = 1 := by simp [M, expect, uniformWeight]
    have hMpos (r : ℝ) : 0 < M r := by
      dsimp [M, expect, uniformWeight]
      apply mul_pos (pow_pos (by norm_num) _)
      exact Finset.sum_pos' (fun x _ ↦ (Real.rpow_pos_of_pos (hu x) r).le)
        ⟨Classical.arbitrary _, Finset.mem_univ _, Real.rpow_pos_of_pos (hu _) r⟩
    have hM : HasDerivAt M A 0 := by
      dsimp [M, A, expect]
      apply HasDerivAt.const_mul
      apply HasDerivAt.fun_sum
      intro x hx
      change HasDerivAt (fun r : ℝ ↦ u x ^ r) (Real.log (u x)) 0
      simpa only [Real.rpow_def_of_pos (hu x), id_eq, mul_zero, Real.exp_zero,
        one_mul, mul_one] using
        ((hasDerivAt_id (x := (0 : ℝ))).const_mul (Real.log (u x))).exp
    have hlog : HasDerivAt (fun r ↦ Real.log (M r)) A 0 := by
      convert hM.log (hMpos 0).ne' using 1
      all_goals simp [hM0]
    let G : ℝ → ℝ :=
      Function.update (fun r ↦ (Real.log (M r) - Real.log (M 0)) / (r - 0)) 0 A
    have hG : ContinuousAt G 0 := hlog.continuousAt_div
    have hfun : (fun r : ℝ ↦ lpMean r u) = fun r ↦ Real.exp (G r) := by
      funext r
      by_cases hr : r = 0
      · subst r
        simp [lpMean, hnz, G, A, abs_of_pos (hu _)]
      · rw [lpMean]
        simp only [hnz, false_and, if_neg hr]
        have habs : expect (fun x ↦ |u x| ^ r) = M r := by
          have heq : (fun x ↦ |u x| ^ r) = fun x ↦ u x ^ r := by
            funext x
            rw [abs_of_pos (hu x)]
          rw [heq]
        rw [habs, Real.rpow_def_of_pos (hMpos r)]
        simp [G, hr, hM0, div_eq_mul_inv]
    rw [hfun]
    simpa only [Function.comp_apply] using Real.continuous_exp.continuousAt.comp hG
  have zero_subsharp : ∀ (P R : ℝ), 0 < P → P < 1 →
      0 ≤ R → R ≤ 1 → R ^ 2 ≤ 1 - P →
      ∀ (u : BooleanFunc n), IsNonnegative u →
        lpMean 0 (noiseOp R u) ≥ lpMean P u := by
    intro P R hP0 hP1 hR0 hR1 hRsq u hu
    by_cases hu0 : u = 0
    · subst u
      rw [show noiseOp R (0 : BooleanFunc n) = 0 by
        simpa using noiseOp_const_mul R 0 (0 : BooleanFunc n)]
      simp [lpMean, hP0.ne', not_le.mpr hP0, expect, uniformWeight]
    · have hex : ∃ y, 0 < u y := by
        by_contra h
        push_neg at h
        exact hu0 (funext fun y ↦ le_antisymm (h y) (hu y))
      have hRlt : R < 1 := by nlinarith [sq_nonneg R]
      have houtpos := noise_strict_pos R hR0 hRlt u hu hex
      have ht : Filter.Tendsto (fun r : ℝ ↦ lpMean r (noiseOp R u))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (lpMean 0 (noiseOp R u))) :=
        (lpMean_continuous_zero (noiseOp R u) houtpos).mono_left inf_le_left
      apply ge_of_tendsto ht
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hP0).filter_mono inf_le_left] with r hr0 hrP
      change 0 < r at hr0
      have hr1 : r < 1 := lt_trans hrP hP1
      have hbound : R ^ 2 ≤ (1 - P) / (1 - r) := by
        rw [le_div_iff₀ (sub_pos.mpr hr1)]
        calc
          R ^ 2 * (1 - r) ≤ R ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg R)
          _ = R ^ 2 := by ring
          _ ≤ 1 - P := hRsq
      exact positive_subsharp P r R hr0 hrP hP1 hR0 hR1 hbound u hu
  have negative_subsharp : ∀ (P Q R : ℝ), Q < P → P < 0 →
      0 ≤ R → R ≤ 1 → R ^ 2 ≤ (1 - P) / (1 - Q) →
      ∀ (u : BooleanFunc n), IsNonnegative u →
        lpMean Q (noiseOp R u) ≥ lpMean P u := by
    intro P Q R hQP hP hR0 hR1 hRsq u hu
    by_cases hz : ∃ x, u x = 0
    · have hright : lpMean P u = 0 := by simp [lpMean, hz, hP.le]
      rw [hright]
      exact mean_nonneg Q _
    · have hupos : ∀ x, 0 < u x :=
        fun x ↦ (hu x).lt_of_ne (Ne.symm (not_exists.mp hz x))
      have hratio_lt : (1 - P) / (1 - Q) < 1 := by
        rw [div_lt_one (by linarith : 0 < 1 - Q)]
        linarith
      have hRlt : R < 1 := by nlinarith [sq_nonneg R]
      let H : BooleanFunc n := noiseOp R u
      have hHpos : ∀ x, 0 < H x :=
        noise_strict_pos R hR0 hRlt u hu ⟨Classical.arbitrary _, hupos _⟩
      have hE : 0 < expect (fun x ↦ H x ^ Q) :=
        expect_rpow_pos (fun x ↦ (hHpos x).le) ⟨Classical.arbitrary _, hHpos _⟩
      let A : ℝ := (expect (fun x ↦ H x ^ Q)) ^ (1 / Q)
      have hApos : 0 < A := Real.rpow_pos_of_pos hE _
      let Q' : ℝ := Q / (Q - 1)
      let P' : ℝ := P / (P - 1)
      have hQ'0 : 0 < Q' := by
        dsimp [Q']
        exact div_pos_of_neg_of_neg (lt_trans hQP hP) (by linarith)
      have hP'0 : 0 < P' := by
        dsimp [P']
        exact div_pos_of_neg_of_neg hP (by linarith)
      have hPm : P - 1 ≠ 0 := by linarith
      have hQm : Q - 1 ≠ 0 := by linarith
      have hOneP : 1 - P ≠ 0 := by linarith
      have hOneQ : 1 - Q ≠ 0 := by linarith
      have heqP : P / (P - 1) = (-P) / (1 - P) := by
        field_simp [hPm, hOneP]
        all_goals ring
      have heqQ : Q / (Q - 1) = (-Q) / (1 - Q) := by
        field_simp [hQm, hOneQ]
        all_goals ring
      have hP'Q' : P' < Q' := by
        dsimp [P', Q']
        rw [heqP, heqQ,
          div_lt_div_iff₀ (by linarith : 0 < 1 - P) (by linarith : 0 < 1 - Q)]
        nlinarith
      have hQ'1 : Q' < 1 := by
        dsimp [Q']
        rw [div_lt_iff_of_neg (by linarith : Q - 1 < 0)]
        linarith
      have h1Q : 1 - Q' = 1 / (1 - Q) := by
        dsimp [Q']
        field_simp [hQm, hOneQ]
        all_goals ring
      have h1P : 1 - P' = 1 / (1 - P) := by
        dsimp [P']
        field_simp [hPm, hOneP]
        all_goals ring
      have hratio : (1 - Q') / (1 - P') = (1 - P) / (1 - Q) := by
        rw [h1Q, h1P]
        field_simp [hOneP, hOneQ]
      let g : BooleanFunc n := fun x ↦ (H x / A) ^ (Q - 1)
      have hgpos (x : BoolCube n) : 0 < g x :=
        Real.rpow_pos_of_pos (div_pos (hHpos x) hApos) _
      have hQne : Q ≠ 0 := by linarith
      have hnormQ : expect (fun x ↦ (H x / A) ^ Q) = 1 := by
        simpa [A] using expect_normalized_rpow_eq_one
          hQne H (fun x ↦ (hHpos x).le) hE
      have hnormg : lpMean Q' g = 1 := by
        rw [lpMean_of_pos Q' hQ'0]
        simp_rw [abs_of_pos (hgpos _)]
        have hmom : expect (fun x ↦ g x ^ Q') = 1 := by
          rw [← hnormQ]
          apply congrArg expect
          funext x
          dsimp [g, Q']
          rw [← Real.rpow_mul (div_pos (hHpos x) hApos).le]
          congr 1
          field_simp [hQm]
        rw [hmom, one_div, Real.one_rpow]
      have hinner : innerProduct H g = A := by
        have hpoint (x : BoolCube n) : H x * g x = A * (H x / A) ^ Q := by
          dsimp [g]
          have hrpow :
              (H x / A) ^ Q = (H x / A) * (H x / A) ^ (Q - 1) := by
            calc
              (H x / A) ^ Q = (H x / A) ^ (Q - 1 + 1) := by
                congr 1
                all_goals ring
              _ = (H x / A) ^ (Q - 1) * (H x / A) ^ (1 : ℝ) :=
                Real.rpow_add (div_pos (hHpos x) hApos) (Q - 1) 1
              _ = (H x / A) * (H x / A) ^ (Q - 1) := by
                rw [Real.rpow_one]
                ring
          rw [hrpow]
          field_simp
        unfold innerProduct expect
        simp_rw [hpoint, ← Finset.mul_sum]
        rw [show uniformWeight n * (A * ∑ x, (H x / A) ^ Q) =
          A * (uniformWeight n * ∑ x, (H x / A) ^ Q) by ring]
        change A * expect (fun x ↦ (H x / A) ^ Q) = A
        rw [hnormQ]
        ring
      have hBB : lpMean P' (noiseOp R g) ≥ lpMean Q' g := by
        have hRsq' : R ^ 2 ≤ (1 - Q') / (1 - P') := by
          rw [hratio]
          exact hRsq
        exact positive_subsharp Q' P' R hP'0 hP'Q' hQ'1 hR0 hR1 hRsq' g
          (fun x ↦ (hgpos x).le)
      have hhold := reverse_holder P (by linarith : P < 1) (by linarith : P ≠ 0)
        u (noiseOp R g) hu (noiseOp_nonneg hR0 hR1 fun x ↦ (hgpos x).le)
      rw [show P / (P - 1) = P' by rfl] at hhold
      have hself : innerProduct u (noiseOp R g) = innerProduct H g := by
        dsimp [H]
        exact (BooleanAnalysis.noiseOp_self_adjoint R u g).symm
      rw [hself, hinner] at hhold
      rw [hnormg] at hBB
      have hmul : lpMean P u ≤ lpMean P u * lpMean P' (noiseOp R g) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hBB (mean_nonneg P u)
      have hA : A = lpMean Q H := by
        dsimp [A]
        rw [lpMean]
        simp only [not_exists.mpr (fun x hx ↦ (hHpos x).ne' hx), false_and, if_false,
          if_neg hQne]
        simp_rw [abs_of_pos (hHpos _)]
      dsimp [H] at hA
      rw [← hA]
      exact hmul.trans hhold
  have zero_target : ∀ (Q R : ℝ), Q < 0 →
      0 ≤ R → R ≤ 1 → R ^ 2 ≤ 1 / (1 - Q) →
      ∀ (u : BooleanFunc n), IsNonnegative u →
        lpMean Q (noiseOp R u) ≥ lpMean 0 u := by
    intro Q R hQ hR0 hR1 hRsq u hu
    by_cases hz : ∃ x, u x = 0
    · have hright : lpMean 0 u = 0 := by simp [lpMean, hz]
      rw [hright]
      exact mean_nonneg Q _
    · have hupos : ∀ x, 0 < u x :=
        fun x ↦ (hu x).lt_of_ne (Ne.symm (not_exists.mp hz x))
      have ht : Filter.Tendsto (fun r : ℝ ↦ lpMean r u)
          (nhdsWithin 0 (Set.Iio 0)) (nhds (lpMean 0 u)) :=
        (lpMean_continuous_zero u hupos).mono_left inf_le_left
      apply le_of_tendsto ht
      filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds hQ).filter_mono inf_le_left] with r hr0 hQr
      change r < 0 at hr0
      have hden : 0 < 1 - Q := by linarith
      have hscaled : R ^ 2 * (1 - Q) ≤ 1 := (le_div_iff₀ hden).mp hRsq
      have hbound : R ^ 2 ≤ (1 - r) / (1 - Q) := by
        rw [le_div_iff₀ hden]
        linarith
      exact negative_subsharp r Q R hQr hr0 hR0 hR1 hbound u hu
  have cross_zero : ∀ (P Q R : ℝ), Q < 0 → 0 < P → P < 1 →
      0 ≤ R → R ≤ 1 → R ^ 2 ≤ (1 - P) / (1 - Q) →
      ∀ (u : BooleanFunc n), IsNonnegative u →
        lpMean Q (noiseOp R u) ≥ lpMean P u := by
    intro P Q R hQ hP0 hP1 hR0 hR1 hRsq u hu
    let A : ℝ := Real.sqrt (1 / (1 - Q))
    have hden : 0 < 1 - Q := by linarith
    have hfrac : 0 < 1 / (1 - Q) := one_div_pos.mpr hden
    have hA0 : 0 < A := Real.sqrt_pos.2 hfrac
    have hAsq : A ^ 2 = 1 / (1 - Q) := Real.sq_sqrt hfrac.le
    have hfrac1 : 1 / (1 - Q) ≤ 1 := (div_le_one hden).2 (by linarith)
    have hA1 : A ≤ 1 := by nlinarith [hAsq, hA0, hfrac1]
    have hRA : R ≤ A := by
      rw [← sq_le_sq₀ hR0 hA0.le, hAsq]
      exact hRsq.trans (by
        rw [div_le_div_iff_of_pos_right hden]
        nlinarith)
    let T : ℝ := R / A
    have hT0 : 0 ≤ T := div_nonneg hR0 hA0.le
    have hT1 : T ≤ 1 := (div_le_one hA0).2 hRA
    have hscaled : R ^ 2 * (1 - Q) ≤ 1 - P := (le_div_iff₀ hden).mp hRsq
    have hTsq : T ^ 2 ≤ 1 - P := by
      dsimp [T]
      rw [div_pow, hAsq]
      field_simp [hden.ne', hA0.ne']
      nlinarith
    have hcomp : noiseOp A (noiseOp T u) = noiseOp R u := by
      rw [noiseOp_compose]
      congr 2
      dsimp [T]
      field_simp
    rw [← hcomp]
    exact le_trans
      (zero_subsharp P T hP0 hP1 hT0 hT1 hTsq u hu)
      (zero_target Q A hQ hA0.le hA1 hAsq.le (noiseOp T u)
        (noiseOp_nonneg hT0 hT1 hu))
  have lpMean_const (r c : ℝ) (hc : 0 ≤ c) :
      lpMean r (fun _ : BoolCube n ↦ c) = c := by
    by_cases hc0 : c = 0
    · subst c
      by_cases hr : r ≤ 0
      · simp [lpMean, hr]
      · have hr0 : 0 < r := lt_of_not_ge hr
        rw [lpMean_of_pos r hr0]
        simp [expect, uniformWeight, Real.zero_rpow hr0.ne']
        rw [Real.zero_rpow (inv_pos.mpr hr0).ne']
    · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
      by_cases hr0 : r = 0
      · subst r
        simp [lpMean, hc0, abs_of_pos hcpos, expect, uniformWeight, Real.exp_log hcpos]
      · rw [lpMean]
        simp only [not_exists.mpr (fun _ h ↦ hc0 h), false_and, if_false, if_neg hr0,
          abs_of_pos hcpos]
        have he : expect (fun _ : BoolCube n ↦ c ^ r) = c ^ r := by
          simp [expect, uniformWeight]
        rw [he, ← Real.rpow_mul hcpos.le]
        field_simp
        exact Real.rpow_one c
  have noiseOp_zero (u : BooleanFunc n) :
      noiseOp 0 u = fun _ ↦ expect u := by
    funext x
    rw [GeneralHypercontractivity.noiseOp_eq_kernel_sum]
    unfold GeneralHypercontractivity.noiseKernel expect uniformWeight
    simp [Finset.prod_const, Finset.card_univ, ← Finset.mul_sum]
  have endpoint_one : ∀ (Q R : ℝ), Q < 1 → 0 ≤ R → R ≤ 1 →
      R ^ 2 ≤ (1 - 1) / (1 - Q) →
      ∀ (u : BooleanFunc n), IsNonnegative u →
        lpMean Q (noiseOp R u) ≥ lpMean 1 u := by
    intro Q R hQ hR0 hR1 hRsq u hu
    have hR : R = 0 := by
      have hden : 0 < 1 - Q := sub_pos.mpr hQ
      rw [show (1 - 1) / (1 - Q) = 0 by
        field_simp
        all_goals ring] at hRsq
      nlinarith [sq_nonneg R]
    subst R
    rw [noiseOp_zero]
    have hexpect : 0 ≤ expect u := by
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun x _ ↦ hu x
    rw [lpMean_const Q (expect u) hexpect, lpMean_of_pos 1 (by norm_num)]
    simp_rw [abs_of_nonneg (hu _), Real.rpow_one]
    norm_num
  have noiseOp_one (u : BooleanFunc n) : noiseOp 1 u = u := by
    funext x
    unfold noiseOp
    simp only [one_pow, one_mul]
    exact (walsh_expansion u x).symm
  by_cases hp1 : p = 1
  · subst p
    exact endpoint_one q ρ hq hρ0 hρ1 hρsq f hf
  have hp' : p < 1 := lt_of_le_of_ne hp hp1
  by_cases hqp' : q = p
  · subst q
    simpa only [noiseOp_one] using
      lpMean_noise_antitone p ρ 1 hp' hρ0 hρ1 (by norm_num) f hf
  have hqp'' : q < p := lt_of_le_of_ne hqp hqp'
  rcases lt_trichotomy p 0 with hpneg | hpzero | hppos
  · exact negative_subsharp p q ρ hqp'' hpneg hρ0 hρ1 hρsq f hf
  · subst p
    exact zero_target q ρ (by linarith) hρ0 hρ1 (by simpa using hρsq) f hf
  · rcases lt_trichotomy q 0 with hqneg | hqzero | hqpos
    · exact cross_zero p q ρ hqneg hppos hp' hρ0 hρ1 hρsq f hf
    · subst q
      exact zero_subsharp p ρ hppos hp' hρ0 hρ1 (by simpa using hρsq) f hf
    · exact positive_subsharp p q ρ hqpos hqp'' hp' hρ0 hρ1 hρsq f hf

/-- Establishes reverse hypercontractivity for nonnegative Boolean-cube functions.

**Source:** [OD14, Exs. 10.6--10.9]. -/
theorem reverse_bonami_beckner (p q ρ : ℝ)
    (hq : q < 1) (hqp : q ≤ p) (hp : p ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρsq : ρ ^ 2 ≤ (1 - p) / (1 - q))
    (f : BooleanFunc n) (hf : IsNonnegative f) :
    lpMean q (noiseOp ρ f) ≥ lpMean p f :=
  extend_reverse_bonami_beckner p q ρ hq hqp hp hρ0 hρ1 hρsq f hf

private lemma lpMean_exponent_mono (a b : ℝ) (hab : a ≤ b) (hb : b ≤ 1)
    (f : BooleanFunc n) (hf : IsNonnegative f) :
    lpMean a f ≤ lpMean b f := by
  have lpMean_nonneg_all (p : ℝ) (f : BooleanFunc n) : 0 ≤ lpMean p f := by
    unfold lpMean
    split_ifs
    · exact le_rfl
    · positivity
    · exact Real.rpow_nonneg (by
        rw [expect_eq_fintypeExpect]
        exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (abs_nonneg (f x)) p) _
  have expect_pos_of_pos (f : BooleanFunc n) (hf : ∀ x, 0 < f x) : 0 < expect f := by
    unfold expect uniformWeight
    exact mul_pos (pow_pos (by norm_num) _)
      (Finset.sum_pos (fun x _ ↦ hf x) Finset.univ_nonempty)
  have expect_rpow_jensen (t : ℝ) (ht : 1 ≤ t)
      (f : BooleanFunc n) (hf : ∀ x, 0 ≤ f x) :
      (expect f) ^ t ≤ expect (fun x ↦ f x ^ t) := by
    unfold expect
    have hw : ∑ _x : BoolCube n, uniformWeight n = 1 := by
      unfold uniformWeight
      simp [Finset.card_univ]
    have h := Real.rpow_arith_mean_le_arith_mean_rpow
      (Finset.univ : Finset (BoolCube n)) (fun _ ↦ uniformWeight n) f
      (fun _ _ ↦ pow_nonneg (by norm_num) _) hw (fun x _ ↦ hf x) ht
    simpa only [← Finset.mul_sum] using h
  have expect_log_le_log_expect (f : BooleanFunc n) (hf : ∀ x, 0 < f x) :
      expect (fun x ↦ Real.log (f x)) ≤ Real.log (expect f) := by
    unfold expect
    have hw : ∑ _x : BoolCube n, uniformWeight n = 1 := by
      unfold uniformWeight
      simp [Finset.card_univ]
    have h := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
      (t := (Finset.univ : Finset (BoolCube n))) (w := fun _ ↦ uniformWeight n) (p := f)
      (fun _ _ ↦ pow_nonneg (by norm_num) _) hw (fun x _ ↦ hf x)
    simpa only [smul_eq_mul, ← Finset.mul_sum] using h
  have lpMean_mono_pos_exp {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
      (f : BooleanFunc n) (hf : IsNonnegative f) : lpMean a f ≤ lpMean b f := by
    have hb : 0 < b := lt_of_lt_of_le ha hab
    rw [lpMean_of_pos a ha, lpMean_of_pos b hb]
    simp_rw [abs_of_nonneg (hf _)]
    have hA : 0 ≤ expect (fun x ↦ f x ^ a) :=
      by
        rw [expect_eq_fintypeExpect]
        exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (hf x) a
    have hB : 0 ≤ expect (fun x ↦ f x ^ b) :=
      by
        rw [expect_eq_fintypeExpect]
        exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (hf x) b
    have hratio : 1 ≤ b / a := by
      apply (le_div_iff₀ ha).2
      simpa using hab
    have hJ := expect_rpow_jensen (b / a) hratio (fun x ↦ f x ^ a)
      (fun x ↦ Real.rpow_nonneg (hf x) a)
    simp_rw [← Real.rpow_mul (hf _)] at hJ
    have hab' : a * (b / a) = b := by field_simp
    rw [hab'] at hJ
    rw [← Real.rpow_le_rpow_iff (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _) hb]
    rw [← Real.rpow_mul hA, ← Real.rpow_mul hB]
    have hleft : 1 / a * b = b / a := by field_simp
    have hright : 1 / b * b = 1 := by field_simp
    rw [hleft, hright, Real.rpow_one]
    exact hJ
  have lpMean_mono_neg_exp {a b : ℝ} (ha : a < 0) (hab : a ≤ b) (hb : b < 0)
      (f : BooleanFunc n) (hf : IsNonnegative f) : lpMean a f ≤ lpMean b f := by
    by_cases hz : ∃ x, f x = 0
    · simp only [lpMean, hz, true_and, if_pos ha.le, if_pos hb.le]
      exact le_rfl
    · have hfpos : ∀ x, 0 < f x :=
        fun x ↦ lt_of_le_of_ne (hf x) (Ne.symm (not_exists.mp hz x))
      simp only [lpMean, hz, false_and, if_false, if_neg ha.ne, if_neg hb.ne]
      simp_rw [abs_of_pos (hfpos _)]
      have hA : 0 < expect (fun x ↦ f x ^ a) :=
        expect_pos_of_pos _ fun x ↦ Real.rpow_pos_of_pos (hfpos x) a
      have hB : 0 < expect (fun x ↦ f x ^ b) :=
        expect_pos_of_pos _ fun x ↦ Real.rpow_pos_of_pos (hfpos x) b
      have hratio : 1 ≤ a / b := by
        rw [le_div_iff_of_neg hb]
        nlinarith
      have hJ := expect_rpow_jensen (a / b) hratio (fun x ↦ f x ^ b)
        (fun x ↦ Real.rpow_nonneg (hf x) b)
      simp_rw [← Real.rpow_mul (hf _)] at hJ
      have hab' : b * (a / b) = a := by field_simp [hb.ne]
      rw [hab'] at hJ
      rw [← Real.rpow_le_rpow_iff_of_neg
        (Real.rpow_pos_of_pos hB _) (Real.rpow_pos_of_pos hA _) ha]
      rw [← Real.rpow_mul hB.le, ← Real.rpow_mul hA.le]
      have hleft : 1 / b * a = a / b := by field_simp
      have hright : 1 / a * a = 1 := by field_simp [ha.ne]
      rw [hleft, hright, Real.rpow_one]
      exact hJ
  have lpMean_neg_le_zero {a : ℝ} (ha : a < 0)
      (f : BooleanFunc n) (hf : IsNonnegative f) :
      lpMean a f ≤ lpMean 0 f := by
    by_cases hz : ∃ x, f x = 0
    · simp [lpMean, hz, ha.le]
    · have hfpos : ∀ x, 0 < f x :=
        fun x ↦ lt_of_le_of_ne (hf x) (Ne.symm (not_exists.mp hz x))
      rw [show lpMean a f = (expect (fun x ↦ f x ^ a)) ^ (1 / a) by
        simp [lpMean, hz, ha.ne, abs_of_pos (hfpos _)],
        show lpMean 0 f = Real.exp (expect (fun x ↦ Real.log (f x))) by
          simp [lpMean, hz, abs_of_pos (hfpos _)]]
      have hA : 0 < expect (fun x ↦ f x ^ a) :=
        expect_pos_of_pos _ fun x ↦ Real.rpow_pos_of_pos (hfpos x) a
      rw [Real.rpow_def_of_pos hA]
      apply Real.exp_le_exp.mpr
      have hJ := expect_log_le_log_expect (fun x ↦ f x ^ a)
        (fun x ↦ Real.rpow_pos_of_pos (hfpos x) a)
      simp_rw [Real.log_rpow (hfpos _)] at hJ
      have hJ' : a * expect (fun x ↦ Real.log (f x)) ≤
          Real.log (expect (fun x ↦ f x ^ a)) := by
        convert hJ using 1
        unfold expect
        rw [← Finset.mul_sum]
        ring
      calc
        Real.log (expect (fun x ↦ f x ^ a)) * (1 / a) =
            Real.log (expect (fun x ↦ f x ^ a)) / a := by ring_nf
        _ ≤ expect (fun x ↦ Real.log (f x)) :=
          (div_le_iff_of_neg ha).2 (by simpa [mul_comm] using hJ')
  have lpMean_zero_le_pos {b : ℝ} (hb : 0 < b)
      (f : BooleanFunc n) (hf : IsNonnegative f) :
      lpMean 0 f ≤ lpMean b f := by
    by_cases hz : ∃ x, f x = 0
    · have hzero : lpMean 0 f = 0 := by simp [lpMean, hz]
      rw [hzero]
      exact lpMean_nonneg_all b f
    · have hfpos : ∀ x, 0 < f x :=
        fun x ↦ lt_of_le_of_ne (hf x) (Ne.symm (not_exists.mp hz x))
      rw [show lpMean 0 f = Real.exp (expect (fun x ↦ Real.log (f x))) by
        simp [lpMean, hz, abs_of_pos (hfpos _)],
        lpMean_of_pos b hb]
      simp_rw [abs_of_pos (hfpos _)]
      have hB : 0 < expect (fun x ↦ f x ^ b) :=
        expect_pos_of_pos _ fun x ↦ Real.rpow_pos_of_pos (hfpos x) b
      rw [Real.rpow_def_of_pos hB]
      apply Real.exp_le_exp.mpr
      have hJ := expect_log_le_log_expect (fun x ↦ f x ^ b)
        (fun x ↦ Real.rpow_pos_of_pos (hfpos x) b)
      simp_rw [Real.log_rpow (hfpos _)] at hJ
      have hJ' : b * expect (fun x ↦ Real.log (f x)) ≤
          Real.log (expect (fun x ↦ f x ^ b)) := by
        convert hJ using 1
        unfold expect
        rw [← Finset.mul_sum]
        ring
      calc
        expect (fun x ↦ Real.log (f x)) ≤
            Real.log (expect (fun x ↦ f x ^ b)) / b :=
          (le_div_iff₀ hb).2 (by simpa [mul_comm] using hJ')
        _ = Real.log (expect (fun x ↦ f x ^ b)) * (1 / b) := by ring_nf
  rcases lt_trichotomy b 0 with hbneg | hbzero | hbpos
  · exact lpMean_mono_neg_exp (lt_of_le_of_lt hab hbneg) hab hbneg f hf
  · subst b
    rcases lt_or_eq_of_le hab with haneg | ha0
    · exact lpMean_neg_le_zero haneg f hf
    · subst a
      exact le_rfl
  · rcases lt_trichotomy a 0 with haneg | hazero | hapos
    · exact (lpMean_neg_le_zero haneg f hf).trans (lpMean_zero_le_pos hbpos f hf)
    · subst a
      exact lpMean_zero_le_pos hbpos f hf
    · exact lpMean_mono_pos_exp hapos hab f hf

/-- The two-function form: `E[f(x)g(y)] ≥ ‖f‖_p ‖g‖_q` for correlated
Boolean strings.

**Source:** [OD14, Exs. 10.6--10.9]. -/
theorem reverse_bonami_beckner_two_function (p q ρ : ℝ)
    (hp : p < 1) (hq : q < 1)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρsq : ρ ^ 2 ≤ (1 - p) * (1 - q))
    (f g : BooleanFunc n) (hf : IsNonnegative f) (hg : IsNonnegative g) :
    innerProduct f (noiseOp ρ g) ≥ lpMean p f * lpMean q g := by
  have lpMean_nonneg_all (r : ℝ) (u : BooleanFunc n) : 0 ≤ lpMean r u := by
    unfold lpMean
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
    · exact Real.rpow_nonneg (by
        rw [expect_eq_fintypeExpect]
        exact Finset.expect_nonneg fun x _ ↦ Real.rpow_nonneg (abs_nonneg _) _) _
  have lpMean_zero_le_expect (u : BooleanFunc n) (hu : IsNonnegative u) :
      lpMean 0 u ≤ expect u := by
    convert lpMean_exponent_mono 0 1 (by norm_num) le_rfl u hu using 1
    rw [lpMean_of_pos 1 zero_lt_one]
    simp [abs_of_nonneg (hu _)]
  have reverse_holder_zero (u v : BooleanFunc n) (hu : IsNonnegative u)
      (hv : IsNonnegative v) :
      innerProduct u v ≥ lpMean 0 u * lpMean 0 v := by
    classical
    by_cases huzero : ∃ x, u x = 0
    · rw [show lpMean 0 u = 0 by simp [lpMean, huzero], zero_mul]
      unfold innerProduct
      rw [expect_eq_fintypeExpect]
      exact Finset.expect_nonneg fun x _ ↦ mul_nonneg (hu x) (hv x)
    · by_cases hvzero : ∃ x, v x = 0
      · rw [show lpMean 0 v = 0 by simp [lpMean, hvzero], mul_zero]
        unfold innerProduct
        rw [expect_eq_fintypeExpect]
        exact Finset.expect_nonneg fun x _ ↦ mul_nonneg (hu x) (hv x)
      · have hupos : ∀ x, 0 < u x := fun x ↦
            (hu x).lt_of_ne (Ne.symm (not_exists.mp huzero x))
        have hvpos : ∀ x, 0 < v x := fun x ↦
            (hv x).lt_of_ne (Ne.symm (not_exists.mp hvzero x))
        have hprodpos : IsNonnegative (fun x ↦ u x * v x) :=
          fun x ↦ mul_nonneg (hu x) (hv x)
        have hprodzero : ¬∃ x, u x * v x = 0 := by
          push_neg
          exact fun x ↦ mul_ne_zero (hupos x).ne' (hvpos x).ne'
        have hmul : lpMean 0 (fun x ↦ u x * v x) = lpMean 0 u * lpMean 0 v := by
          rw [show lpMean 0 (fun x ↦ u x * v x) =
              Real.exp (expect (fun x ↦ Real.log (u x * v x))) by
            unfold lpMean
            rw [if_neg (by simpa using hprodzero), if_pos rfl]
            simp_rw [abs_of_pos (mul_pos (hupos _) (hvpos _))]]
          rw [show lpMean 0 u = Real.exp (expect (fun x ↦ Real.log (u x))) by
            simp [lpMean, huzero, abs_of_pos (hupos _)]]
          rw [show lpMean 0 v = Real.exp (expect (fun x ↦ Real.log (v x))) by
            simp [lpMean, hvzero, abs_of_pos (hvpos _)]]
          simp_rw [Real.log_mul (hupos _).ne' (hvpos _).ne']
          unfold expect
          rw [Finset.sum_add_distrib, mul_add, Real.exp_add]
        rw [← hmul]
        exact lpMean_zero_le_expect (fun x ↦ u x * v x) hprodpos
  have two_function_core : ∀ (a b R : ℝ), a < 1 → a ≠ 0 →
      0 ≤ R → R ≤ 1 → R ^ 2 ≤ (1 - a) * (1 - b) →
      ∀ (u v : BooleanFunc n), IsNonnegative u → IsNonnegative v →
        innerProduct u (noiseOp R v) ≥ lpMean a u * lpMean b v := by
    intro a b R ha ha0 hR0 hR1 hRsq u v hu hv
    let c := a / (a - 1)
    let d := 1 - R ^ 2 / (1 - a)
    have h1a : 0 < 1 - a := sub_pos.mpr ha
    have ham1 : a - 1 ≠ 0 := (sub_neg.mpr ha).ne
    have hc1 : c < 1 := by
      dsimp [c]
      rw [div_lt_iff_of_neg (sub_neg.mpr ha)]
      linarith
    have hconj : 1 - c = 1 / (1 - a) := by
      dsimp [c]
      field_simp [h1a.ne', ham1]
      ring
    have hRsq1 : R ^ 2 ≤ 1 := by nlinarith
    have hbd : b ≤ d := by
      have hdiv : R ^ 2 / (1 - a) ≤ 1 - b := by
        rw [div_le_iff₀ h1a]
        simpa [mul_comm] using hRsq
      dsimp [d]
      linarith
    have hd1 : d ≤ 1 := by
      dsimp [d]
      exact sub_le_self 1 (div_nonneg (sq_nonneg R) h1a.le)
    have hcd : c ≤ d := by
      rw [show c = 1 - 1 / (1 - a) by linarith [hconj]]
      dsimp [d]
      have := div_le_div_of_nonneg_right hRsq1 h1a.le
      linarith
    have hratio : (1 - d) / (1 - c) = R ^ 2 := by
      rw [hconj]
      dsimp [d]
      field_simp [h1a.ne']
      ring
    have hholder := reverse_holder a ha ha0 u (noiseOp R v) hu
      (noiseOp_nonneg hR0 hR1 hv)
    have hbb := reverse_bonami_beckner d c R hc1 hcd hd1 hR0 hR1
      (by rw [hratio]) v hv
    have hmean : lpMean c (noiseOp R v) ≥ lpMean b v :=
      (lpMean_exponent_mono b d hbd hd1 v hv).trans hbb
    exact (mul_le_mul_of_nonneg_left hmean (lpMean_nonneg_all a u)).trans hholder
  by_cases hp0 : p = 0
  · by_cases hq0 : q = 0
    · subst p
      subst q
      have hhold :=
        reverse_holder_zero f (noiseOp ρ g) hf (noiseOp_nonneg hρ0 hρ1 hg)
      have hcorr : ρ ^ 2 ≤ (1 - (0 : ℝ)) / (1 - (0 : ℝ)) := by
        norm_num
        simpa using hρsq
      have hbb := reverse_bonami_beckner 0 0 ρ (by norm_num) le_rfl (by norm_num)
        hρ0 hρ1 hcorr g hg
      exact (mul_le_mul_of_nonneg_left hbb (lpMean_nonneg_all 0 f)).trans hhold
    · subst p
      calc
        lpMean 0 f * lpMean q g = lpMean q g * lpMean 0 f := mul_comm _ _
        _ ≤ innerProduct g (noiseOp ρ f) := two_function_core q 0 ρ hq hq0 hρ0 hρ1
          (by simpa [mul_comm] using hρsq) g f hg hf
        _ = innerProduct f (noiseOp ρ g) := by
          rw [innerProduct_comm, noiseOp_self_adjoint]
  · exact two_function_core p q ρ hp hp0 hρ0 hρ1 hρsq f g hf hg

end ReverseBonamiBeckner
