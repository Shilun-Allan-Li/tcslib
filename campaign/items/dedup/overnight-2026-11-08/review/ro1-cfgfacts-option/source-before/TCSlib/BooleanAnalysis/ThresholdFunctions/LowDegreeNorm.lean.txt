import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import TCSlib.BooleanAnalysis.Hypercontractivity.Cube.General
import TCSlib.BooleanAnalysis.ThresholdFunctions.Polynomial

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Low-degree Boolean-cube norm inequality

The sharp hypercontractive estimate for polynomials of bounded Walsh degree compares their
squared Fourier norm to the square of their expected absolute value. This is the analytic
input to the Fourier-weight bound for polynomial threshold functions.

## Main definitions

No new definitions are exported.

## Main results

* `low_degree_l1_l2_sq`: a degree-`k` polynomial has `L²` norm at most `exp(k)`
  times its `L¹` norm, stated with squares.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  arXiv edition, 2021, Theorems 9.21 and 9.22.
-/

open scoped BigOperators
open Filter

namespace BooleanAnalysis
namespace ThresholdFunctions

open MultilinearPolynomial

/-- Noise at parameter `ρ ∈ [0,1]` retains at least `ρ^(2k)` of the squared norm of
a degree-`k` polynomial. [OD14, Thm. 9.21 (proof)]

**Proof sketch.** Parseval writes the noisy squared norm as a weighted sum of squared Fourier
coefficients. Every nonzero coefficient has degree at most `k`, so its weight is at least
`ρ^(2k)`. -/
private lemma noise_degree_lower {n k : ℕ} (p : MultilinearPolynomial n)
    (hdeg : p.HasDegreeAtMost k) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ρ ^ (2 * k) * (∑ S : Finset (Fin n), p S ^ 2) ≤
      expect (fun x ↦ (noiseOp ρ p.eval x) ^ 2) := by
  have hnoise := BooleanAnalysis.Hypercontractivity.noise_l2_fourier ρ p.eval
  have heq : expect (fun x ↦ (noiseOp ρ p.eval x) ^ 2) =
      innerProduct (noiseOp ρ p.eval) (noiseOp ρ p.eval) := by
    simp [innerProduct, sq]
  rw [heq, hnoise, Finset.mul_sum]
  simp_rw [fourierCoeff_eval]
  apply Finset.sum_le_sum
  intro S hS
  by_cases hSk : S.card ≤ k
  · have hpow : ρ ^ (2 * k) ≤ (ρ ^ S.card) ^ 2 := by
      rw [← pow_mul, mul_comm]
      exact pow_le_pow_of_le_one hρ0 hρ1 (by omega)
    exact mul_le_mul_of_nonneg_right hpow (sq_nonneg (p S))
  · have hpS : p S = 0 := hdeg S (Nat.lt_of_not_ge hSk)
    simp [hpS]

/-- For `1<t<2`, the sharp hypercontractive inequality bounds the squared norm of a
degree-`k` polynomial by its `t`-moment with factor `(t-1)^k`.
[OD14, Thm. 9.22 (proof)]

**Proof sketch.** Set the noise parameter to `√(t-1)`. Hypercontractivity sends the
`t`-norm of the original polynomial above the noisy `L²` norm, while the degree bound
gives the lower estimate for that noisy norm. -/
private lemma low_degree_moment_bound {n k : ℕ} (p : MultilinearPolynomial n)
    (hdeg : p.HasDegreeAtMost k) (t : ℝ) (ht1 : 1 < t) (ht2 : t < 2) :
    (t - 1) ^ k * (∑ S : Finset (Fin n), p S ^ 2) ≤
      (expect (fun x ↦ |p.eval x| ^ t)) ^ (2 / t) := by
  let ρ := Real.sqrt (t - 1)
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ ≤ 1 := by
    dsimp [ρ]
    rw [Real.sqrt_le_one]
    linarith
  have hρ : ρ ≤ Real.sqrt ((t - 1) / ((2 : ℝ) - 1)) := by
    norm_num [ρ]
  have hHC := BooleanAnalysis.Hypercontractivity.general_one_function_hypercontractivity
    t 2 (by linarith) (by linarith) (by norm_num)
    ρ hρ0 hρ1 hρ p.eval
  have hmoment : expect (fun x ↦ |noiseOp ρ p.eval x| ^ (2 : ℝ)) =
      expect (fun x ↦ (noiseOp ρ p.eval x) ^ 2) := by
    congr 1
    funext x
    norm_num [Real.rpow_natCast, sq_abs]
  rw [hmoment] at hHC
  have hleft : 0 ≤ expect (fun x ↦ (noiseOp ρ p.eval x) ^ 2) :=
    BooleanAnalysis.Hypercontractivity.expect_sq_noiseOp_nonneg ρ p.eval
  have hright : 0 ≤ (expect (fun x ↦ |p.eval x| ^ t)) ^ (1 / t) :=
    Real.rpow_nonneg (BooleanAnalysis.Hypercontractivity.expect_rpow_abs_nonneg _ _) _
  have hsq := (sq_le_sq₀ (Real.rpow_nonneg hleft _) hright).mpr hHC
  have hleft_eq : (expect (fun x ↦ (noiseOp ρ p.eval x) ^ 2)) ^ (1 / (2 : ℝ)) =
      Real.sqrt (expect (fun x ↦ (noiseOp ρ p.eval x) ^ 2)) := by
    rw [Real.sqrt_eq_rpow]
  rw [hleft_eq, Real.sq_sqrt hleft] at hsq
  have hright_eq :
      ((expect (fun x ↦ |p.eval x| ^ t)) ^ (1 / t)) ^ 2 =
        (expect (fun x ↦ |p.eval x| ^ t)) ^ (2 / t) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (BooleanAnalysis.Hypercontractivity.expect_rpow_abs_nonneg _ _)]
    congr 1
    ring
  rw [hright_eq] at hsq
  have hρlow := noise_degree_lower p hdeg ρ hρ0 hρ1
  have heq : ρ ^ (2 * k) = (t - 1) ^ k := by
    dsimp [ρ]
    rw [pow_mul, Real.sq_sqrt (by linarith)]
  rw [heq] at hρlow
  exact hρlow.trans hsq

/-- The `t`-moment for `1<t<2` is bounded by the geometric interpolation of the first
and second moments. [OD14, Thm. 9.22 (proof)]

**Proof sketch.** Apply weighted Hölder with weight `|f|`, observable `|f|^(t-1)`,
and exponent `1/(t-1)`; the weighted higher moment is then `E[f²]`. -/
private lemma moment_interpolation {n : ℕ} (f : BooleanFunc n)
    (t : ℝ) (ht1 : 1 < t) (ht2 : t < 2) :
    expect (fun x ↦ |f x| ^ t) ≤
      (expect (fun x ↦ |f x|)) ^ (2 - t) *
      (expect (fun x ↦ (f x) ^ 2)) ^ (t - 1) := by
  let r : ℝ := 1 / (t - 1)
  have hr : 1 ≤ r := by
    dsimp [r]
    apply (le_div_iff₀ (by linarith)).mpr
    linarith
  have hrinv : r⁻¹ = t - 1 := by
    dsimp [r]
    field_simp
  let w : BoolCube n → ℝ := fun x ↦ |f x|
  let v : BoolCube n → ℝ := fun x ↦ |f x| ^ (t - 1)
  have hholder := Real.compact_inner_le_weight_mul_Lp_of_nonneg
    (s := Finset.univ) (p := r) (w := w) (f := v) hr
    (by intro x; exact abs_nonneg _) (by intro x; exact Real.rpow_nonneg (abs_nonneg _) _)
  rw [← expect_eq_fintypeExpect, ← expect_eq_fintypeExpect,
    ← expect_eq_fintypeExpect] at hholder
  have hprod1 (x : BoolCube n) : w x * v x = |f x| ^ t := by
    dsimp [w, v]
    calc
      |f x| * |f x| ^ (t - 1) = |f x| ^ (1 : ℝ) * |f x| ^ (t - 1) := by
        rw [Real.rpow_one]
      _ = |f x| ^ (1 + (t - 1)) :=
        (Real.rpow_add_of_nonneg (abs_nonneg _) (by norm_num) (by linarith)).symm
      _ = |f x| ^ t := by congr 1; ring
  have hv (x : BoolCube n) : v x ^ r = |f x| := by
    dsimp [v]
    rw [← Real.rpow_mul (abs_nonneg _)]
    have hm : (t - 1) * r = 1 := by
      dsimp [r]
      apply mul_div_cancel₀
      linarith
    rw [hm, Real.rpow_one]
  have hprod2 (x : BoolCube n) : w x * v x ^ r = (f x) ^ 2 := by
    rw [hv]
    dsimp [w]
    nlinarith [sq_abs (f x)]
  simp_rw [hprod1, hprod2] at hholder
  rw [hrinv] at hholder
  have hexp : 1 - (t - 1) = 2 - t := by ring
  rw [hexp] at hholder
  exact hholder

/-- Clear the fractional exponents in the Hölder interpolation at
`t=(2m+1)/(m+1)` by raising to the natural power `2(m+1)`. -/
private lemma interp_pow (m : ℕ) (A B M : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hInt : M ≤ A ^ (1 / ((m + 1 : ℕ) : ℝ)) *
      B ^ ((m : ℝ) / ((m + 1 : ℕ) : ℝ))) :
    M ^ (2 * (m + 1)) ≤ A ^ 2 * B ^ (2 * m) := by
  have hpow := pow_le_pow_left₀ hM hInt (m + 1)
  rw [mul_pow] at hpow
  have ha : (A ^ (1 / ((m + 1 : ℕ) : ℝ))) ^ (m + 1) = A := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA]
    have he : (1 / ((m + 1 : ℕ) : ℝ)) * ((m + 1 : ℕ) : ℝ) = 1 := by field_simp
    rw [he, Real.rpow_one]
  have hb : (B ^ ((m : ℝ) / ((m + 1 : ℕ) : ℝ))) ^ (m + 1) = B ^ m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB]
    have he : ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) * ((m + 1 : ℕ) : ℝ) = m := by
      field_simp
    rw [he, Real.rpow_natCast]
  rw [ha, hb] at hpow
  have hsq := pow_le_pow_left₀ (pow_nonneg hM _) hpow 2
  rw [mul_pow] at hsq
  convert hsq using 1 <;> ring

/-- Clear the fractional hypercontractive exponent at
`t=(2m+1)/(m+1)` by raising to the natural power `2m+1`. -/
private lemma hc_pow (m k : ℕ) (B M D : ℝ)
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hHC : D ^ k * B ≤
      M ^ ((2 * (((m + 1 : ℕ) : ℝ))) / (((2 * m + 1 : ℕ) : ℝ)))) :
    (D ^ k * B) ^ (2 * m + 1) ≤ M ^ (2 * (m + 1)) := by
  have hpow := pow_le_pow_left₀ (mul_nonneg (pow_nonneg hD _) hB) hHC (2 * m + 1)
  have hMN : (M ^ ((2 * (((m + 1 : ℕ) : ℝ))) /
      (((2 * m + 1 : ℕ) : ℝ)))) ^ (2 * m + 1) =
      M ^ (2 * (m + 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM]
    have he : (2 * (((m + 1 : ℕ) : ℝ)) / (((2 * m + 1 : ℕ) : ℝ))) *
      (((2 * m + 1 : ℕ) : ℝ)) = (2 * (((m + 1 : ℕ) : ℝ))) := by
      field_simp
    rw [he, ← Real.rpow_natCast]
    congr 1
    norm_cast
  rwa [hMN] at hpow

/-- Cancel the positive squared norm after combining the two natural-power inequalities,
then enlarge the exponent to a form with a simple limit. -/
private lemma abstract_cancel (m k : ℕ) (A B M C D : ℝ)
    (hB : 0 < B) (hC : 1 ≤ C) (hCD : C * D = 1)
    (h1 : (D ^ k * B) ^ (2 * m + 1) ≤ M ^ (2 * (m + 1)))
    (h2 : M ^ (2 * (m + 1)) ≤ A ^ 2 * B ^ (2 * m)) :
    B ≤ (C ^ (m + 1)) ^ (2 * k) * A ^ 2 := by
  have h := le_trans h1 h2
  rw [mul_pow] at h
  have hBp : 0 < B ^ (2 * m) := pow_pos hB _
  have h' : (D ^ (k * (2 * m + 1)) * B) * B ^ (2 * m) ≤
      A ^ 2 * B ^ (2 * m) := by
    convert h using 1; ring
  have hcancel : D ^ (k * (2 * m + 1)) * B ≤ A ^ 2 :=
    (mul_le_mul_iff_left₀ hBp).mp h'
  have hCpow : 0 ≤ C ^ (k * (2 * m + 1)) := pow_nonneg (by linarith) _
  have hmul := mul_le_mul_of_nonneg_left hcancel hCpow
  have hres : B ≤ C ^ (k * (2 * m + 1)) * A ^ 2 := by
    calc
      B = C ^ (k * (2 * m + 1)) *
          (D ^ (k * (2 * m + 1)) * B) := by
            rw [← mul_assoc, ← mul_pow, hCD, one_pow, one_mul]
      _ ≤ C ^ (k * (2 * m + 1)) * A ^ 2 := hmul
  have hexp : k * (2 * m + 1) ≤ 2 * k * (m + 1) := by
    calc
      k * (2 * m + 1) ≤ k * (2 * m + 2) := Nat.mul_le_mul_left k (by omega)
      _ = 2 * k * (m + 1) := by ring
  have hCmono : C ^ (k * (2 * m + 1)) ≤ C ^ (2 * k * (m + 1)) :=
    pow_le_pow_right₀ hC hexp
  have hfinal := hres.trans (mul_le_mul_of_nonneg_right hCmono (sq_nonneg A))
  have hpowe : C ^ (2 * k * (m + 1)) = (C ^ (m + 1)) ^ (2 * k) := by
    rw [← pow_mul]
    congr 1
    ring
  rw [← hpowe]
  exact hfinal

/-- At `t=(2m+1)/(m+1)`, the hypercontractive moment bound and Hölder interpolation
give a finite estimate with constant `(1+1/m)^(2k(m+1))`.

**Proof sketch.** Clear both rational exponents by natural powers, cancel the positive
second moment, and use `(m/(m+1))(1+1/m)=1`. -/
private lemma finite_algebra (m k : ℕ) (hm : 1 ≤ m) (A B M : ℝ)
    (hA : 0 ≤ A) (hB : 0 < B) (hM : 0 ≤ M)
    (t : ℝ) (ht : t = ((2 * m + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ))
    (hHC : (t - 1) ^ k * B ≤ M ^ (2 / t))
    (hInt : M ≤ A ^ (2 - t) * B ^ (t - 1)) :
    B ≤ ((1 + 1 / (m : ℝ)) ^ (m + 1)) ^ (2 * k) * A ^ 2 := by
  let C : ℝ := 1 + 1 / (m : ℝ)
  let D : ℝ := (m : ℝ) / ((m + 1 : ℕ) : ℝ)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (one_div_nonneg.mpr hmpos.le)
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hCD : C * D = 1 := by
    dsimp [C, D]
    field_simp
    push_cast
    ring
  have htD : t - 1 = D := by
    rw [ht]
    dsimp [D]
    field_simp
    push_cast
    ring
  have ht2 : 2 - t = 1 / ((m + 1 : ℕ) : ℝ) := by
    rw [ht]
    field_simp
    push_cast
    ring
  have htExp : 2 / t =
      (2 * (((m + 1 : ℕ) : ℝ))) / (((2 * m + 1 : ℕ) : ℝ)) := by
    rw [ht]
    field_simp
  have hInt' : M ≤ A ^ (1 / ((m + 1 : ℕ) : ℝ)) *
      B ^ ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
    simpa only [ht2, htD] using hInt
  have hHC' : D ^ k * B ≤
      M ^ ((2 * (((m + 1 : ℕ) : ℝ))) / (((2 * m + 1 : ℕ) : ℝ))) := by
    simpa only [htD, htExp] using hHC
  have h1 := hc_pow m k B M D hB.le hM hD hHC'
  have h2 := interp_pow m A B M hA hB.le hM hInt'
  exact abstract_cancel m k A B M C D hB hC hCD h1 h2

/-- The finite constants converge to `exp(2k)` as `m → ∞`. [OD14, Thm. 9.22 (proof)] -/
private theorem degree_norm_limit (k : ℕ) :
    Filter.Tendsto (fun m : ℕ => ((1 + 1 / (m : ℝ)) ^ (m + 1)) ^ (2 * k))
      Filter.atTop (nhds (Real.exp ((2 * k : ℕ) : ℝ))) := by
  have hbase : Filter.Tendsto (fun m : ℕ => 1 + 1 / (m : ℝ))
      Filter.atTop (nhds (1 : ℝ)) := by
    simpa using (tendsto_const_nhds.add
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hpow : Filter.Tendsto (fun m : ℕ => (1 + 1 / (m : ℝ)) ^ m)
      Filter.atTop (nhds (Real.exp 1)) := by
    simpa using Real.tendsto_one_add_div_pow_exp 1
  have hmul := (hpow.mul hbase).pow (2 * k)
  have hlim : Filter.Tendsto
      (fun m : ℕ => ((1 + 1 / (m : ℝ)) ^ (m + 1)) ^ (2 * k))
      Filter.atTop (nhds ((Real.exp 1 * 1) ^ (2 * k))) := by
    simpa only [pow_succ] using hmul
  simpa [Real.exp_nat_mul] using hlim

/-- Pass the finite norm bounds to their exact endpoint constant. -/
private theorem degree_norm_endpoint (k : ℕ) (A B : ℝ)
    (h : ∀ m : ℕ, 2 ≤ m →
      B ≤ ((1 + 1 / (m : ℝ)) ^ (m + 1)) ^ (2 * k) * A ^ 2) :
    B ≤ Real.exp ((2 * k : ℕ) : ℝ) * A ^ 2 := by
  apply ge_of_tendsto ((degree_norm_limit k).mul_const (A ^ 2))
  exact Filter.eventually_atTop.2 ⟨2, fun m hm => h m hm⟩

/-- A degree-`k` Walsh polynomial has `L²` norm at most `exp(k)` times its `L¹`
norm, stated without square roots. [OD14, Thm. 9.22]

**Proof sketch.** For `m ≥ 1`, take `t=(2m+1)/(m+1)`. Hypercontractivity at noise
`√(t-1)` gives a lower bound for the `t`-moment in terms of the squared norm; weighted
Hölder gives an upper bound in terms of the first and second moments. After raising to
natural powers and canceling the positive second moment, the squared norm is at most
`(1+1/m)^(2k(m+1))` times the squared first moment. This constant tends to
`exp(2k)`, which gives the stated inequality. The zero polynomial is immediate. -/
theorem low_degree_l1_l2_sq {n k : ℕ} (p : MultilinearPolynomial n)
    (hdeg : p.HasDegreeAtMost k) :
    Real.exp (-2 * (k : ℝ)) * (∑ S : Finset (Fin n), p S ^ 2) ≤
      (expect (fun x ↦ |p.eval x|)) ^ 2 := by
  let A := expect (fun x ↦ |p.eval x|)
  let B := ∑ S : Finset (Fin n), p S ^ 2
  have hA : 0 ≤ A := expect_nonneg fun x ↦ abs_nonneg _
  have hB : 0 ≤ B := Finset.sum_nonneg (fun S hS => sq_nonneg _)
  by_cases hBzero : B = 0
  · change Real.exp (-2 * (k : ℝ)) * B ≤ A ^ 2
    rw [hBzero, mul_zero]
    exact sq_nonneg A
  have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hBzero)
  have hBeq : expect (fun x ↦ (p.eval x) ^ 2) = B := p.expect_eval_sq
  have hfinite (m : ℕ) (hm : 1 ≤ m) :
      B ≤ ((1 + 1 / (m : ℝ)) ^ (m + 1)) ^ (2 * k) * A ^ 2 := by
    let t : ℝ := ((2 * m + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hden : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have ht1 : 1 < t := by
      dsimp [t]
      rw [lt_div_iff₀ hden]
      push_cast
      nlinarith
    have ht2 : t < 2 := by
      dsimp [t]
      rw [div_lt_iff₀ hden]
      push_cast
      nlinarith
    let M := expect (fun x ↦ |p.eval x| ^ t)
    have hM : 0 ≤ M :=
      BooleanAnalysis.Hypercontractivity.expect_rpow_abs_nonneg t p.eval
    have hHC := low_degree_moment_bound p hdeg t ht1 ht2
    change (t - 1) ^ k * B ≤ M ^ (2 / t) at hHC
    have hInt := moment_interpolation p.eval t ht1 ht2
    rw [hBeq] at hInt
    change M ≤ A ^ (2 - t) * B ^ (t - 1) at hInt
    exact finite_algebra m k hm A B M hA hBpos hM t rfl hHC hInt
  have hlim : B ≤ Real.exp ((2 * k : ℕ) : ℝ) * A ^ 2 :=
    degree_norm_endpoint k A B (fun m hm => hfinite m (by omega))
  have he : Real.exp ((2 * k : ℕ) : ℝ) = Real.exp (2 * (k : ℝ)) := by norm_num
  rw [he] at hlim
  change Real.exp (-2 * (k : ℝ)) * B ≤ A ^ 2
  calc
    _ ≤ Real.exp (-2 * (k : ℝ)) * (Real.exp (2 * (k : ℝ)) * A ^ 2) :=
      mul_le_mul_of_nonneg_left hlim (le_of_lt (Real.exp_pos _))
    _ = A ^ 2 := by rw [← mul_assoc, ← Real.exp_add]; simp

end ThresholdFunctions
end BooleanAnalysis
