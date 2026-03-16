import TCSlib.CodingTheory.Basic
import TCSlib.CodingTheory.HammingBound

set_option linter.unusedSectionVars false

/-!
# Entropy and Asymptotic Bounds

This file establishes asymptotic bounds relating Hamming ball sizes to the q-ary entropy function,
and provides the key binomial coefficient lower bound used in the Gilbert–Varshamov theorem.

## Main Results

* `hamming_ball_size_asymptotic_upper_bound` : for `0 < p ≤ 1 - 1/q`, the Hamming ball of
  radius `⌊np⌋` has at most `q^(H_q(p)·n)` elements.
* `q_pow_qary_entropy_simp` / `q_pow_qary_entropy_simp'` : simplification lemmas for
  `q^(H_q(p))` in terms of elementary functions.
* `binomial_coef_asymptotic_lower_bound'` : the dominant binomial term `C(n,⌊np⌋)·(q-1)^(pn)`
  grows at least as fast as `q^(H_q(p)·n - ε(n))` where `ε = o(n)`.
* `qary_entropy_pos` : the q-ary entropy is positive for `0 < p ≤ 1 - 1/q`.

-/

open Set Filter Asymptotics Finset

namespace CodingTheory
namespace Codeword

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α]
variable {n k : ℕ}
variable {x : ℝ}

/-- **Asymptotic upper bound on ball size**: for `0 < p ≤ 1 - 1/q`, the Hamming ball of
    radius `⌊np⌋` has at most `q^(H_q(p)·n)` elements. -/
theorem hamming_ball_size_asymptotic_upper_bound (q n : ℕ) (p : ℝ)
    (hq : q = Fintype.card α) (hα : Nontrivial α)
    (hp : 0 < p ∧ p ≤ 1 - 1/q) :
    ∀ c : Codeword n α,
      (hamming_ball (Nat.floor (n*p)) c).card ≤ Real.rpow q ((qaryEntropy q p) * n) := by {
  intro c
  rw[hamming_ball_size]
  rw[← hq]
  have hq_pos : (0 : ℝ) < q := by
    rw [hq, Nat.cast_pos]
    exact Fintype.card_pos
  have hq_sub_one_nonneg : (0 : ℝ) ≤ ↑q - 1 := by
    rw [sub_nonneg]
    have : (1 : ℝ) ≤ q := by
      rw [hq]
      exact_mod_cast Nat.one_le_of_lt Fintype.card_pos
    exact this
  have hq_sub_one_pos : (0 : ℝ) < ↑q - 1 := by
    rw [hq]
    exact natCast_sub_one_pos_of_two_le (Nat.succ_le_iff.mpr Fintype.one_lt_card)
  have hp_lt_one : p < 1 := lt_one_of_le_one_sub_inv hq_pos hp.2
  have h_one_sub_p : 0 < 1 - p := one_sub_pos_of_lt_one hp_lt_one
  apply (div_le_one (by simpa using Real.rpow_pos_of_pos hq_pos ((qaryEntropy q p) * n))).1
  simp
  dsimp[qaryEntropy]

  rw[div_eq_mul_inv, ← Real.rpow_neg]
  have : -((p * Real.logb (↑q) (↑q - 1) - p * Real.logb (↑q) p - (1 - p) * Real.logb (↑q) (1 - p)) * ↑n) =
          (Real.logb (↑q) (↑q - 1)) * (-p * ↑n) + (Real.logb (↑q) p) * (p * ↑n) + (Real.logb (↑q) (1 - p)) * ((1-p) * ↑n) := by linarith
  rw[this]

  rw[Real.rpow_add, Real.rpow_add, Real.rpow_mul, Real.rpow_logb, Real.rpow_mul, Real.rpow_mul, Real.rpow_mul,Real.rpow_mul]
  rw[Real.rpow_logb, Real.rpow_logb]
  rw[← Real.rpow_mul, ← Real.rpow_mul]
  rw[Finset.sum_mul]


  simp only [neg_mul, ge_iff_le]

-- Doing all the algebra
  have h_alg1 : ∀ x, ↑(Nat.choose n x) * ↑(q - 1) ^ x * ((↑q - 1) ^ (-(p * ↑n)) * p ^ (p * ↑n) * (1 - p) ^ ((1 - p) * ↑n)) =
  ↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p/((q-1)*(1-p)))^(p*↑n) := by
    intro x
    rw[one_sub_mul, sub_eq_add_neg ↑n (p * ↑n)]
    rw[Real.rpow_add h_one_sub_p, ← mul_assoc, ← Real.rpow_natCast]
    calc
      ↑(Nat.choose n x) * ↑(q - 1) ^ (x :ℝ) * ((↑q - 1) ^ (-(p * ↑n)) * p ^ (p * ↑n)) * ((1 - p) ^ (n : ℝ) * (1 - p) ^ (-(p * ↑n))) =
      ↑(Nat.choose n x) * ↑(q - 1) ^ (x : ℝ) * (1 - p) ^ (n : ℝ) * ((((1 - p) ^(-(p * ↑n)) * (↑q - 1) ^ (-(p * ↑n)))) * p ^ (p * ↑n)) := by linarith
      _ = ↑(Nat.choose n x) * ↑(q - 1) ^ (x : ℝ) * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ (p * ↑n) := by {
        rw[← Real.mul_rpow]
        rw[Real.rpow_neg, ← Real.inv_rpow]
        rw[← Real.mul_rpow]
        rw[← div_eq_inv_mul]
        ring_nf
        · apply inv_nonneg.2
          apply mul_nonneg
          exact le_of_lt h_one_sub_p
          exact hq_sub_one_nonneg
        · linarith
        · exact (mul_nonneg_iff_of_pos_left h_one_sub_p).mpr hq_sub_one_nonneg
        · exact (mul_nonneg_iff_of_pos_left h_one_sub_p).mpr hq_sub_one_nonneg
        · exact le_of_lt h_one_sub_p
        · exact hq_sub_one_nonneg
      }

  have h_alg_2 : ∀ x ∈ (Finset.range (⌊↑n * p⌋₊ + 1)), ↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ (p * ↑n) ≤ (↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ x) := by
    intros x hx
    suffices (p / ((↑q - 1) * (1 - p))) ^ (p * ↑n) ≤ (p / ((↑q - 1) * (1 - p))) ^ x by {
      calc
        ↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ (p * ↑n) =
        (↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ)) * (p / ((↑q - 1) * (1 - p))) ^ (p * ↑n) := by linarith
        _ ≤ (↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ x) := by rel[this]
    }
    simp only [Finset.mem_range] at hx
    have : 0 < (p / ((↑q - 1) * (1 - p))) ∧ (p / ((↑q - 1) * (1 - p))) ≤ 1 := by
      constructor
      · apply div_pos
        linarith[hp.1]
        apply mul_pos
        exact hq_sub_one_pos
        linarith[h_one_sub_p]
      · suffices p / (q - 1) ≤ 1 - p by {
          rw[← div_div]
          apply (div_le_one h_one_sub_p).2
          exact this
        }
        calc
          p / (↑q - 1) ≤ 1/q := by {
            apply (div_le_iff₀ hq_sub_one_pos).2
            rw[mul_sub, one_div, mul_one, inv_mul_cancel₀]
            rw [one_div] at hp
            exact hp.2
            exact ne_of_gt hq_pos
          }
          _ ≤ 1 - p := by linarith

    have h_x_le_pn : x ≤ p * n := by
      have : 0 ≤ n*p := by
        apply mul_nonneg
        exact Nat.cast_nonneg n
        linarith[hp.1]
      rw[mul_comm]
      apply (Nat.le_floor_iff this).1
      exact Nat.lt_succ.mp hx

    rw[← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_ge this.1 this.2 h_x_le_pn



  calc
      (Finset.sum (Finset.range (⌊↑n * p⌋₊ + 1)) fun x =>
    ↑(Nat.choose n x) * ↑(q - 1) ^ x * ((↑q - 1) ^ (-(p * ↑n)) * p ^ (p * ↑n) * (1 - p) ^ ((1 - p) * ↑n))) =  (Finset.sum (Finset.range (⌊↑n * p⌋₊ + 1)) fun x =>
    ↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p/((q-1)*(1-p)))^(p*↑n)) := by {
      apply Finset.sum_congr
      rfl
      intro x hx
      exact h_alg1 x
    }
    _ ≤ (Finset.sum (Finset.range (⌊↑n * p⌋₊ + 1)) fun x => (↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ x)) := by {
      apply Finset.sum_le_sum
      intros i hi
      exact h_alg_2 i hi
    }
    _ ≤ (Finset.sum (Finset.range (n + 1)) fun x => (↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ x)) := by {
      apply Finset.sum_le_sum_of_subset_of_nonneg

      apply range_subset.2
      simp only [Finset.mem_range]
      intro x hx
      apply lt_of_lt_of_le hx
      simp only [add_le_add_iff_right]
      apply Nat.floor_le_of_le
      calc
        ↑n * p ≤ ↑n * 1 := by exact mul_le_mul_of_nonneg_left (le_of_lt hp_lt_one) (Nat.cast_nonneg n)
        _      ≤ ↑n     := by simp
      intros i _ _
      repeat apply mul_nonneg
      simp only [Nat.cast_nonneg]
      simp only [Nat.cast_nonneg, pow_nonneg]
      simp only [Real.rpow_natCast]
      exact pow_nonneg (le_of_lt h_one_sub_p) n
      apply pow_nonneg
      apply div_nonneg
      exact le_of_lt hp.1
      apply mul_nonneg
      exact hq_sub_one_nonneg
      exact le_of_lt h_one_sub_p
    }
    _ = Finset.sum (Finset.range (n + 1)) fun x => (↑(Nat.choose n x) * p ^ x * (1 - p) ^ ((n : ℝ) - x)) := by{
      apply Finset.sum_congr
      rfl
      intros x hx
      simp at hx
      apply Nat.lt_succ.1 at hx
      rw[div_pow, mul_pow]
      field_simp
      simp
      symm
      calc
        ↑(Nat.choose n x) * p ^ x * (↑q - 1) ^ x * (1 - p) ^ x * (1 - p) ^ ((n:ℝ) - (x:ℝ)) =
        ↑(Nat.choose n x) * (↑q - 1) ^ x * ((1 - p) ^ ((n:ℝ) - (x:ℝ)) * (1 - p) ^ x) * p ^ x := by linarith
        _ = ↑(Nat.choose n x) * (↑q - 1) ^ x * ((1 - p) ^ (n - x) * (1 - p) ^ x) * p ^ x := by rw[←Nat.cast_sub hx, Real.rpow_natCast]
        _ = ↑(Nat.choose n x) * (↑q - 1) ^ x * (1 - p) ^ n * p ^ x := by rw[←pow_add, Nat.sub_add_cancel hx]
        _ = ↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ n * p ^ x := by {
          simp only [mul_eq_mul_right_iff, mul_eq_mul_left_iff, Nat.cast_eq_zero, pow_eq_zero_iff',
            ne_eq]
          left
          left
          left
          rw[Nat.cast_sub, Nat.cast_one]
          rw[hq]
          exact Nat.one_le_of_lt Fintype.card_pos
        }
    }
    _ = Finset.sum (Finset.range (n + 1)) fun x => (p ^ x * (1 - p) ^ (n - x) * ↑(Nat.choose n x)) := by {
      apply Finset.sum_congr
      rfl
      intros x hx
      simp only [Finset.mem_range] at hx
      apply Nat.lt_succ.1 at hx
      rw[←Nat.cast_sub hx, Real.rpow_natCast]
      linarith
    }
    _ = 1 := by {
      rw[← add_pow p (1-p) n]
      simp only [add_sub_cancel, one_pow]
    }

  -- More algebras on inequalities
  exact le_of_lt hp.1
  exact hq_sub_one_nonneg
  exact hq_pos
  linarith[hq_sub_one_pos]
  exact h_one_sub_p
  exact hq_pos
  linarith[hq_sub_one_pos]
  exact hp.1
  exact le_of_lt hq_pos
  rw[Real.rpow_logb]
  exact le_of_lt hp.1
  exact hq_pos
  linarith[hq_sub_one_pos]
  exact hp.1
  linarith[hq_pos]
  exact hq_sub_one_nonneg
  exact hq_pos
  linarith[hq_sub_one_pos]
  exact hq_sub_one_pos
  linarith[hq_pos]
  exact hq_pos
  exact hq_pos
  linarith[hq_pos]
}

/-- Algebraic rewrite of the `q`-ary entropy exponent used in `rpow` simplifications. -/
private lemma qary_entropy_logb_expand (q : ℕ) (p : ℝ) :
    p * Real.logb (↑q) (↑q - 1) - p * Real.logb (↑q) p - (1 - p) * Real.logb (↑q) (1 - p) =
      Real.logb (↑q) (↑q - 1) * p + Real.logb (↑q) p * (-p) +
        Real.logb (↑q) (1 - p) * (-(1 - p)) := by
  linarith

/-- Simplification: `q^(H_q(p)) = (q-1)^p · p^(-p) · (1-p)^(-(1-p))`.
    Uses `Real.rpow`. -/
lemma q_pow_qary_entropy_simp {q : ℕ} {p : ℝ} (hq : 2 ≤ q) (hp : 0 < p ∧ p < 1) :
    Real.rpow q (qaryEntropy q p) =
      (q - 1)^p * p ^ (-p) * (1 - p)^(-(1 - p)) := by{
  simp only [Real.rpow_eq_pow, neg_sub]
  dsimp only [qaryEntropy]
  rw [qary_entropy_logb_expand q p]

  have hq₂ : 0 < (q : ℝ) := natCast_pos_of_two_le hq
  have hq₃ : (q : ℝ) ≠ 1 := natCast_ne_one_of_two_le hq
  have hq₄ : (0 : ℝ) < ↑q - 1 := natCast_sub_one_pos_of_two_le hq
  have hp₂ : 0 < 1 - p := one_sub_pos_of_lt_one hp.2

  rw[Real.rpow_add hq₂, Real.rpow_add hq₂]
  rw[Real.rpow_mul (le_of_lt hq₂), Real.rpow_mul (le_of_lt hq₂), Real.rpow_mul (le_of_lt hq₂)]
  rw[Real.rpow_logb hq₂ hq₃ hq₄, Real.rpow_logb hq₂ hq₃ hp.1, Real.rpow_logb hq₂ hq₃ hp₂]

  simp only [neg_sub]
}

/-- Variant of `q_pow_qary_entropy_simp` using natural-number power (`q ^ _`). -/
lemma q_pow_qary_entropy_simp' {q : ℕ} {p : ℝ} (hq : 2 ≤ q) (hp : 0 < p ∧ p < 1) :
    q ^ (qaryEntropy q p) = (q - 1)^p * p ^ (-p) * (1 - p)^(-(1 - p)) := by
  simpa using q_pow_qary_entropy_simp hq hp

/-- Helper: `√x - √⌊x⌋ ≤ 1` for `x ≥ 0`. -/
lemma sqrt_sub_sqrt_floor_le_one (hx : 0 ≤ x) : Real.sqrt x - Real.sqrt (Nat.floor x) ≤ 1 := by{
  suffices ‖Real.sqrt x - Real.sqrt (Nat.floor x)‖ ≤ ‖(1 : ℝ)‖ by{
    simp only [Real.norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary] at this
    rw[abs_of_nonneg] at this
    exact this
    simp only [sub_nonneg]
    apply Real.sqrt_le_sqrt
    exact Nat.floor_le hx
  }
  apply sq_le_sq.1
  rw[sub_sq]
  simp only [Nat.cast_nonneg, Real.sq_sqrt, one_pow]
  rw[Real.sq_sqrt hx]
  calc
    x - 2 * Real.sqrt x * Real.sqrt ↑⌊x⌋₊ + ↑⌊x⌋₊ ≤ x - 2 * (Real.sqrt ↑⌊x⌋₊ * Real.sqrt ↑⌊x⌋₊) +  ↑⌊x⌋₊:= by {
      suffices 2 * (Real.sqrt ↑⌊x⌋₊ * Real.sqrt ↑⌊x⌋₊) ≤ 2 * (Real.sqrt x * Real.sqrt ↑⌊x⌋₊)  by linarith
      suffices Real.sqrt ↑⌊x⌋₊ ≤ Real.sqrt x by {
        apply (mul_le_mul_iff_right₀ two_pos).2
        by_cases h: ↑⌊x⌋₊ = 0
        rw[h]
        simp only [CharP.cast_eq_zero, Real.sqrt_zero, mul_zero, le_refl]
        have hx_pos : 0 < Real.sqrt ↑⌊x⌋₊ := by simp; exact Nat.pos_of_ne_zero h
        apply (mul_le_mul_iff_left₀ hx_pos).2
        exact this
      }
      exact Real.sqrt_le_sqrt (Nat.floor_le hx)
    }
    _ = x - 2 * ↑⌊x⌋₊ +  ↑⌊x⌋₊ := by simp
    _ = x - ↑⌊x⌋₊             := by ring_nf
    _ ≤ 1                     := by linarith[Nat.sub_one_lt_floor x]

}

/-- AM-GM: the geometric mean of two nonneg reals is at most their arithmetic mean. -/
private lemma am_gm_sqrt_le_half_sum {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  have hab_sq : a * b ≤ ((a + b) / 2) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  calc Real.sqrt (a * b) ≤ Real.sqrt (((a + b) / 2) ^ 2) := Real.sqrt_le_sqrt hab_sq
    _ = (a + b) / 2 := Real.sqrt_sq (by linarith)

/-- `√(2πn) · √(π/2) · √n = πn`. -/
private lemma sqrt_two_pi_mul_sqrt_pi_half (n : ℝ) (hn : 0 ≤ n) :
    Real.sqrt (2 * Real.pi * n) * Real.sqrt (Real.pi / 2) * Real.sqrt n = Real.pi * n := by
  rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
  rw [show 2 * Real.pi * n * (Real.pi / 2) * n = (Real.pi * n) ^ 2 by ring_nf]
  exact Real.sqrt_sq (by positivity)

/-- When `n ≥ 2/(p(1-p)) + 1`, we have `n·p > 1`, so `⌊n·p⌋ ≥ 1`. -/
private lemma floor_np_pos {p : ℝ} (hp : 0 < p) (h1p : 0 < 1 - p)
    {n : ℕ} {N₂ : ℕ} (hN₂_def : N₂ = Nat.ceil (2 / (p * (1 - p))) + 1)
    (hn_N2 : N₂ ≤ n) : 0 < ⌊(n : ℝ) * p⌋₊ := by
  apply Nat.pos_of_ne_zero
  intro heq
  have hnp_lt1 : (n : ℝ) * p < 1 := Nat.floor_eq_zero.mp heq
  have hp1p : 0 < p * (1 - p) := mul_pos hp h1p
  have hn_cast : (N₂ : ℝ) ≤ n := by exact_mod_cast hn_N2
  have hN2_val : (2 : ℝ) / (p * (1 - p)) + 1 ≤ N₂ := by
    rw [hN₂_def]; push_cast; linarith [Nat.le_ceil (2 / (p * (1 - p)))]
  have h_n_lb : (2 : ℝ) / (p * (1 - p)) + 1 ≤ n := le_trans hN2_val hn_cast
  have h_prod_lb : (2 : ℝ) + p * (1 - p) ≤ n * (p * (1 - p)) := by
    have h1 := mul_le_mul_of_nonneg_right h_n_lb hp1p.le
    have h2 : (2 / (p * (1 - p)) + 1) * (p * (1 - p)) = 2 + p * (1 - p) := by
      field_simp [ne_of_gt hp, ne_of_gt h1p]
    linarith
  nlinarith [mul_le_mul_of_nonneg_right (le_of_lt (show p < 1 by linarith))
    (mul_nonneg (Nat.cast_nonneg n) h1p.le), mul_pos hp h1p]

set_option maxHeartbeats 400000 in
/-- Stirling-based ratio bound used in the binomial lower bound. -/
private lemma stirling_comb_bound
    {a b n : ℕ} {c : ℝ}
    (ha_pos : 0 < (a : ℝ)) (hb_pos : 0 < (b : ℝ)) (hc_pos : 0 < c)
    (hab : a + b = n)
    (hN_n : (a.factorial : ℝ) * b.factorial ≤
      c * (Real.sqrt 2 * Real.sqrt ↑a * Real.sqrt Real.pi * (↑a / Real.exp 1) ^ a *
           (Real.sqrt 2 * Real.sqrt ↑b * Real.sqrt Real.pi * (↑b / Real.exp 1) ^ b))) :
    (n : ℝ) ^ n / ((a : ℝ) ^ a * (b : ℝ) ^ b) / (c * Real.sqrt (Real.pi / 2) * Real.sqrt n) ≤
    (n.factorial : ℝ) / ((a.factorial : ℝ) * b.factorial) := by
  have hn_pos : (0 : ℝ) < n := by
    have : 0 < a + b := Nat.add_pos_left (by exact_mod_cast ha_pos) b
    rw [← hab]; exact_mod_cast this
  have hab_real : (a : ℝ) + b = n := by exact_mod_cast hab
  have hsq_ab : Real.sqrt 2 * Real.sqrt ↑a * Real.sqrt Real.pi *
      (Real.sqrt 2 * Real.sqrt ↑b * Real.sqrt Real.pi) = 2 * Real.pi * Real.sqrt ((a : ℝ) * b) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg a)]
    rw [show Real.sqrt 2 * Real.sqrt ↑a * Real.sqrt Real.pi * (Real.sqrt 2 * Real.sqrt ↑b * Real.sqrt Real.pi) =
        (Real.sqrt 2 * Real.sqrt 2) * (Real.sqrt ↑a * Real.sqrt ↑b) * (Real.sqrt Real.pi * Real.sqrt Real.pi) by ring_nf]
    rw [Real.mul_self_sqrt (by norm_num), Real.mul_self_sqrt Real.pi_pos.le,
        ← Real.sqrt_mul (Nat.cast_nonneg a)]
    ring_nf
  have h_stir_ab : (a.factorial : ℝ) * b.factorial ≤
      c * (2 * Real.pi * Real.sqrt ((a : ℝ) * b)) *
      (((a : ℝ) / Real.exp 1) ^ a * ((b : ℝ) / Real.exp 1) ^ b) := by
    calc (a.factorial : ℝ) * b.factorial
        ≤ c * (Real.sqrt 2 * Real.sqrt ↑a * Real.sqrt Real.pi * (↑a / Real.exp 1) ^ a *
          (Real.sqrt 2 * Real.sqrt ↑b * Real.sqrt Real.pi * (↑b / Real.exp 1) ^ b)) := hN_n
      _ = c * (2 * Real.pi * Real.sqrt (↑a * ↑b)) *
          ((↑a / Real.exp 1) ^ a * (↑b / Real.exp 1) ^ b) := by
          linear_combination c * ((↑a / Real.exp 1) ^ a * (↑b / Real.exp 1) ^ b) * hsq_ab
  have h_ab_AM_GM : Real.sqrt ((a : ℝ) * b) ≤ (n : ℝ) / 2 := by
    have : Real.sqrt ((a : ℝ) * b) ≤ ((a : ℝ) + b) / 2 :=
      am_gm_sqrt_le_half_sum (Nat.cast_nonneg a) hb_pos.le
    linarith [hab_real]
  have h_stir_n : Real.sqrt (2 * Real.pi * n) * ((n : ℝ) / Real.exp 1) ^ n ≤ n.factorial :=
    Stirling.le_factorial_stirling n
  have h_e_a : ((↑a / Real.exp 1) ^ a : ℝ) = (↑a) ^ a / Real.exp ↑a := by
    rw [div_pow, ← Real.exp_nat_mul, mul_one]
  have h_e_b : ((↑b / Real.exp 1) ^ b : ℝ) = (↑b) ^ b / Real.exp ↑b := by
    rw [div_pow, ← Real.exp_nat_mul, mul_one]
  have h_e_n : ((↑n / Real.exp 1) ^ n : ℝ) = (↑n) ^ n / Real.exp ↑n := by
    rw [div_pow, ← Real.exp_nat_mul, mul_one]
  have h_exp_sum : Real.exp (↑a : ℝ) * Real.exp (↑b : ℝ) = Real.exp (↑n : ℝ) := by
    rw [← Real.exp_add, hab_real]
  have h_pi_ident : Real.sqrt (2 * Real.pi * ↑n) * Real.sqrt (Real.pi / 2) * Real.sqrt ↑n =
      Real.pi * ↑n := sqrt_two_pi_mul_sqrt_pi_half _ hn_pos.le
  have h_denom_pos' : (0 : ℝ) < c * Real.sqrt (Real.pi / 2) * Real.sqrt ↑n := by positivity
  have h_ab_pos : (0 : ℝ) < (↑a : ℝ) ^ a * (↑b : ℝ) ^ b :=
    mul_pos (pow_pos ha_pos _) (pow_pos hb_pos _)
  suffices h : (↑n) ^ n * (↑(a.factorial) * ↑(b.factorial)) ≤
      (↑(n.factorial)) * ((↑a) ^ a * (↑b) ^ b) * (c * Real.sqrt (Real.pi / 2) * Real.sqrt ↑n) by
    rw [div_div, div_le_div_iff₀ (mul_pos h_ab_pos h_denom_pos') (by positivity)]
    calc (↑n) ^ n * (↑(a.factorial) * ↑(b.factorial))
        ≤ (↑(n.factorial)) * ((↑a) ^ a * (↑b) ^ b) * (c * Real.sqrt (Real.pi / 2) * Real.sqrt ↑n) := h
      _ = (↑(n.factorial)) * ((↑a) ^ a * (↑b) ^ b * (c * Real.sqrt (Real.pi / 2) * Real.sqrt ↑n)) := by ring_nf
  calc (↑n) ^ n * (↑(a.factorial) * ↑(b.factorial))
      ≤ (↑n) ^ n * (c * (2 * Real.pi * Real.sqrt (↑a * ↑b)) *
            ((↑a / Real.exp 1) ^ a * (↑b / Real.exp 1) ^ b)) :=
            mul_le_mul_of_nonneg_left h_stir_ab (by positivity)
    _ = c * (2 * Real.pi * Real.sqrt (↑a * ↑b)) *
            ((↑n / Real.exp 1) ^ n * ((↑a) ^ a * (↑b) ^ b)) := by
            rw [h_e_a, h_e_b, h_e_n]
            rw [show Real.exp ↑n = Real.exp ↑a * Real.exp ↑b from h_exp_sum.symm]
            ring_nf
    _ ≤ c * (Real.pi * ↑n) *
            ((↑n / Real.exp 1) ^ n * ((↑a) ^ a * (↑b) ^ b)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith [h_ab_AM_GM, Real.pi_pos]
    _ = Real.sqrt (2 * Real.pi * ↑n) * (↑n / Real.exp 1) ^ n *
            ((↑a) ^ a * (↑b) ^ b) * (c * Real.sqrt (Real.pi / 2) * Real.sqrt ↑n) := by
            rw [← h_pi_ident]; ring_nf
    _ ≤ ↑(n.factorial) * ((↑a) ^ a * (↑b) ^ b) *
            (c * Real.sqrt (Real.pi / 2) * Real.sqrt ↑n) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right h_stir_n (by positivity)

set_option maxHeartbeats 800000 in
/-- **Binomial lower bound**: there exists `ε = o(n)` such that for all large `n`,
    `C(n,⌊np⌋) · (q-1)^(pn) ≥ q^(H_q(p)·n - ε(n))`.
    This is a key ingredient in the Gilbert–Varshamov bound. -/
lemma binomial_coef_asymptotic_lower_bound' {q: ℕ} {p : ℝ} (hp : 0 < p ∧ p < 1) (hq : 2 ≤ q) :
    ∃ (ε : ℕ → ℝ),
      Asymptotics.IsLittleO atTop ε (fun n ↦ (n: ℝ)) ∧
      ∀ᶠ n in atTop,
        Nat.choose n (Nat.floor (n*p)) * (q - 1) ^ (p*n) ≥
          Real.rpow q ((qaryEntropy q p) * n - ε n) := by{
  -- Helper Statement
  have self_ge_frac_floor : ∀ x : ℕ, ⌊(x : ℝ) * p⌋₊ ≤ x := by
    intro x
    suffices (⌊↑x * p⌋₊:ℝ) ≤ ↑x by {
      simp only [Nat.cast_le] at this
      exact this
    }
    calc
        ⌊↑x * p⌋₊ ≤ ↑x * p := by exact Nat.floor_le (by {
          apply mul_nonneg
          simp
          linarith
        })
        _        ≤ ↑x      := by {
          by_cases h : x=0
          rw[h]
          simp only [CharP.cast_eq_zero, zero_mul, le_refl]
          have : 0 < (x:ℝ) := by simp only [Nat.cast_pos]; exact Nat.pos_of_ne_zero h
          apply (mul_le_iff_le_one_right (this)).2
          linarith
        }

  -- Stirling's on floor(np)! and (n - floor(np))!
  have h_stirling := Stirling.factorial_isEquivalent_stirling
  have h_stirling_np : (fun (n : ℕ) => ↑(Nat.factorial (Nat.floor (n*p)))) ~[atTop] fun n => Real.sqrt (2 * (Nat.floor (n*p)) * Real.pi) * ((Nat.floor (n*p)) / Real.exp 1) ^ (Nat.floor (n*p)) := by
    apply Asymptotics.IsLittleO.isEquivalent
    apply Asymptotics.IsEquivalent.isLittleO at h_stirling
    let k : ℕ → ℕ := fun n ↦ Nat.floor (n*p)
    have hk : Filter.Tendsto k atTop atTop := by
      apply Filter.tendsto_atTop_atTop_of_monotone
      refine monotone_nat_of_le_succ ?hk.hf.hf
      intro n
      apply Nat.floor_le_floor
      apply (mul_le_mul_iff_left₀ hp.1).2
      simp only [Nat.cast_add, Nat.cast_one, le_add_iff_nonneg_right, zero_le_one]
      intro b
      use Nat.ceil (b/p)
      calc
        ⌊↑⌈↑b / p⌉₊ * p⌋₊ ≥ ⌊↑b / p * p⌋₊ := by {
          apply Nat.floor_le_floor
          apply (mul_le_mul_iff_left₀ hp.1).2
          exact Nat.le_ceil (b/p)
        }
        _                  ≥ ⌊b⌋₊ := by {
          have h₁ : p ≠ 0 := by linarith
          have h₂ : ↑b / p * p = b := by exact div_mul_cancel₀ (↑b) h₁
          rw[h₂]
          simp
        }
    have h_tend := Asymptotics.IsLittleO.comp_tendsto h_stirling hk
    simp only [k] at h_tend ⊢
    rw[Function.comp_def, Function.comp_def] at h_tend
    exact h_tend
  have h_stirling_n1p : (fun (n : ℕ) => ↑(Nat.factorial (n - (Nat.floor (n*p))))) ~[atTop] fun n => Real.sqrt (2 * ((n - (Nat.floor (n*p))) : ℕ) * Real.pi) * (((n - (Nat.floor (n*p))) : ℕ) / Real.exp 1) ^ ((n - (Nat.floor (n*p))) : ℕ) := by
    apply Asymptotics.IsLittleO.isEquivalent
    apply Asymptotics.IsEquivalent.isLittleO at h_stirling
    rw[Pi.sub_def] at h_stirling ⊢
    let k : ℕ → ℕ := fun n ↦ n - (Nat.floor (n*p))
    have hk : Filter.Tendsto k atTop atTop := by
      intros S hS
      simp only [mem_atTop_sets, ge_iff_le, Filter.mem_map, Set.mem_preimage] at hS ⊢
      rcases hS with ⟨a, ha⟩
      use Nat.ceil (a/(1-p))
      intro b hb
      apply ha
      suffices a ≤ (((b - ⌊↑b * p⌋₊):ℕ) : ℝ) by {
        simp only [Nat.cast_le] at this
        exact this
      }
      have hbp: ⌊↑b * p⌋₊ ≤ b := by exact self_ge_frac_floor b
      have h1p : 0 < 1 - p := one_sub_pos_of_lt_one hp.2
      calc
        (((b - ⌊↑b * p⌋₊):ℕ):ℝ) = b - ⌊↑b * p⌋₊ := by rw[Nat.cast_sub hbp]
        _                       ≥ b - b * p := by {
          have : b * p ≥ 0 := by exact mul_nonneg (by linarith) (by linarith)
          linarith[Nat.floor_le this]
        }
        _            = b * (1 - p) := by linarith
        _            ≥ ⌈↑a / (1 - p)⌉₊ * (1-p) := by rel[hb]
        _            ≥ a / (1 - p) * (1 - p) := by exact (mul_le_mul_iff_left₀ h1p).2 (Nat.le_ceil (a/(1 -p)))
        _            = a                     := by exact div_mul_cancel₀ (a : ℝ) (by linarith)

    have h_tend := Asymptotics.IsLittleO.comp_tendsto h_stirling hk
    simp only [k] at h_tend ⊢
    rw[Function.comp_def, Function.comp_def] at h_tend
    exact h_tend

  have h_np_bigO := Asymptotics.IsEquivalent.isBigO (Asymptotics.IsEquivalent.mul h_stirling_np h_stirling_n1p)
  rw[Asymptotics.IsBigO_def] at h_np_bigO
  rcases h_np_bigO with ⟨c_denom, hc⟩
  rw[Asymptotics.IsBigOWith_def] at hc
  simp only [Pi.mul_apply, norm_mul, RCLike.norm_natCast, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left,
    Nat.cast_nonneg, Real.sqrt_mul, Nat.ofNat_nonneg, Real.norm_eq_abs, norm_pow, norm_div,
    Real.abs_exp, eventually_atTop, ge_iff_le] at hc
  rcases hc with ⟨N, hN⟩
  -- ε'(n) absorbs: Stirling error (c_denom * sqrt(π/2)) and entropy difference ((q-1)*e²/p)
  let ε : ℕ → ℝ := fun n ↦ Real.logb q (n ^ ((1 : ℝ)/2))
  let ε' : ℕ → ℝ := fun n ↦ Real.logb q (c_denom * ((q : ℝ) - 1) * Real.exp 1 ^ 2 * Real.sqrt (Real.pi / 2) / p) + (ε n)
  use ε'
  constructor
  · -- ε' = o(n): constant term is o(n), and ε(n) = (1/2)*logb q n = o(n)
    simp only [Real.exp_one_pow, Nat.cast_ofNat, Nat.ofNat_nonneg, Real.sqrt_div', ε']
    apply Asymptotics.IsLittleO.add
    · simp only [isLittleO_const_left, Real.logb_eq_zero, Nat.cast_eq_zero, Nat.cast_eq_one,
      div_eq_zero_iff, mul_eq_zero, Real.exp_ne_zero, or_false, Nat.ofNat_nonneg, Real.sqrt_eq_zero,
      OfNat.ofNat_ne_zero]
      right
      have h1 : (norm ∘ (fun (n:ℕ) => (n:ℝ))) = (fun (n : ℕ) ↦ ‖(n: ℝ)‖) := by exact rfl
      rw[h1]
      simp only [RCLike.norm_natCast]
      apply tendsto_natCast_atTop_iff.2
      have h2 : (fun (n:ℕ) ↦ n) = id := by exact rfl
      rw[h2]
      exact Filter.tendsto_id
    · simp only [one_div, ε]
      have h₁ : (fun (x:ℕ) => Real.logb (↑q) (↑x ^ ((1:ℝ) / 2))) = (fun (x:ℕ) => 1/2 * 1 / Real.log (↑q) * Real.log (↑x)) := by
        ext x
        by_cases hx : x = 0
        rw[hx]
        simp only [CharP.cast_eq_zero, one_div, ne_eq, inv_eq_zero, OfNat.ofNat_ne_zero,
          not_false_eq_true, Real.zero_rpow, Real.logb_zero, mul_one, Real.log_zero, mul_zero]
        apply Nat.pos_of_ne_zero at hx
        rw [← Real.log_div_log, Real.log_rpow]
        field_simp
        exact Nat.cast_pos.mpr hx
      simp only [one_div, mul_one] at h₁
      rw[h₁]
      apply Asymptotics.IsLittleO.const_mul_left
      exact IsLittleO.comp_tendsto Real.isLittleO_log_id_atTop tendsto_natCast_atTop_atTop
  -- Main inequality: for n ≥ max(N, N₂), C(n,⌊np⌋)*(q-1)^(pn) ≥ q^(H_q(p)*n - ε'(n))
  simp only [Real.rpow_eq_pow, ge_iff_le, eventually_atTop]
  have h1p : 0 < 1 - p := one_sub_pos_of_lt_one hp.2
  have hp1p : 0 < p * (1 - p) := mul_one_sub_pos hp.1 hp.2
  -- N₂ ensures n*(1-p) ≥ 2 (needed for the entropy bound below)
  let N₂ : ℕ := Nat.ceil (2 / (p * (1 - p))) + 1
  use max N N₂
  intro n hn
  have hn_N : N ≤ n := le_trans (le_max_left N N₂) hn
  have hn_N2 : N₂ ≤ n := le_trans (le_max_right N N₂) hn
  have hn_pos : 0 < n := Nat.lt_of_lt_of_le (Nat.succ_pos _) hn_N2
  -- Basic setup
  have h1p' : 0 < 1 - p := h1p
  have hq' : 0 < (q : ℝ) := natCast_pos_of_two_le hq
  have hq1 : (1 : ℝ) < q := natCast_one_lt_of_two_le hq
  have hq_ge1 : (1 : ℝ) ≤ q - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hq1_pos : 0 < (q : ℝ) - 1 := natCast_sub_one_pos_of_two_le hq
  have hq_ne1 : (q : ℝ) ≠ 1 := natCast_ne_one_of_two_le hq
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_real
  -- a = ⌊np⌋, b = n - a
  let a := ⌊(n : ℝ) * p⌋₊
  let b := n - a
  have ha_le : a ≤ n := self_ge_frac_floor n
  have ha_real : (a : ℝ) ≤ n * p := Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (le_of_lt hp.1))
  have ha_real' : (n : ℝ) * p - 1 < a := by
    have := Nat.lt_floor_add_one ((n : ℝ) * p); push_cast at this ⊢; linarith
  have hb_real : (b : ℝ) = n - a := by
    simp only [b]; push_cast [Nat.cast_sub ha_le]; ring_nf
  -- δ = np - a ∈ [0, 1)
  have hδ_nn : (0 : ℝ) ≤ n * p - a := by linarith [ha_real]
  have hδ_lt1 : (n : ℝ) * p - a < 1 := by linarith [ha_real']
  -- n*(1-p) ≥ 2 (from n ≥ N₂)
  have h_n1p_ge2 : (2 : ℝ) ≤ n * (1 - p) := by
    have hn_cast : (N₂ : ℝ) ≤ n := by exact_mod_cast hn_N2
    have hN2_bound : (2 : ℝ) / (p * (1 - p)) ≤ (Nat.ceil (2 / (p * (1 - p))) : ℝ) :=
      Nat.le_ceil _
    have : N₂ = Nat.ceil (2 / (p * (1 - p))) + 1 := rfl
    have hN2_val : (2 : ℝ) / (p * (1 - p)) + 1 ≤ N₂ := by
      push_cast [this]; linarith
    have h_n_lb : (2 : ℝ) / (p * (1 - p)) + 1 ≤ n := le_trans hN2_val hn_cast
    have h_prod_lb : (2 : ℝ) + p * (1 - p) ≤ n * (p * (1 - p)) := by
      have h1 := mul_le_mul_of_nonneg_right h_n_lb (le_of_lt hp1p)
      have h2 : (2 / (p * (1 - p)) + 1) * (p * (1 - p)) = 2 + p * (1 - p) := by
        have hp_ne : p ≠ 0 := ne_of_gt hp.1
        have h1p_ne : (1 - p) ≠ 0 := ne_of_gt h1p
        field_simp [hp_ne, h1p_ne]
      linarith
    nlinarith [mul_le_mul_of_nonneg_right (le_of_lt hp.2) (mul_nonneg (le_of_lt hn_real) (le_of_lt h1p))]
  have hb_ge2 : (2 : ℝ) ≤ b := by
    rw [hb_real]; linarith [ha_real]
  have hb_pos : 0 < b := by
    have : (0 : ℝ) < b := by linarith [hb_ge2]
    exact_mod_cast this
  have hb_real_pos : (0 : ℝ) < b := by exact_mod_cast hb_pos
  have hb_expand : (b : ℝ) = n * (1 - p) + (n * p - a) := by
    rw [hb_real]; linarith [ha_real]
  have h_a_fact_pos : (0 : ℝ) < a.factorial := Nat.cast_pos.mpr (Nat.factorial_pos a)
  have h_b_fact_pos : (0 : ℝ) < b.factorial := Nat.cast_pos.mpr (Nat.factorial_pos b)
  have h_n_fact_pos : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have ha_pos_nat : 0 < a := floor_np_pos hp.1 h1p rfl hn_N2
  have ha_pos_r : (0 : ℝ) < ↑a := by exact_mod_cast ha_pos_nat
  -- Specialize hN at n
  have hN_n : (a.factorial : ℝ) * b.factorial ≤
      c_denom * (|Real.sqrt 2| * |Real.sqrt ↑a| * |Real.sqrt Real.pi| * (↑a / Real.exp 1) ^ a *
        (|Real.sqrt 2| * |Real.sqrt ↑b| * |Real.sqrt Real.pi| * (↑b / Real.exp 1) ^ b)) := by
    have := hN n hn_N; simp only [b, a] at this ⊢; exact this
  -- Strip absolute values (all are nonneg)
  have h_abs_sqrt2 : |Real.sqrt 2| = Real.sqrt 2 := abs_of_nonneg (Real.sqrt_nonneg _)
  have h_abs_sqrta : |Real.sqrt ↑a| = Real.sqrt ↑a := abs_of_nonneg (Real.sqrt_nonneg _)
  have h_abs_sqrtb : |Real.sqrt ↑b| = Real.sqrt ↑b := abs_of_nonneg (Real.sqrt_nonneg _)
  have h_abs_sqrtpi : |Real.sqrt Real.pi| = Real.sqrt Real.pi := abs_of_nonneg (Real.sqrt_nonneg _)
  rw [h_abs_sqrt2, h_abs_sqrta, h_abs_sqrtb, h_abs_sqrtpi] at hN_n
  -- c_denom is positive
  have hc_pos : 0 < c_denom := by
    have h_ab_pos : (0 : ℝ) < a.factorial * b.factorial := mul_pos h_a_fact_pos h_b_fact_pos
    have h_rhs_pos : 0 < c_denom *
        (Real.sqrt 2 * Real.sqrt ↑a * Real.sqrt Real.pi * (↑a / Real.exp 1) ^ a *
         (Real.sqrt 2 * Real.sqrt ↑b * Real.sqrt Real.pi * (↑b / Real.exp 1) ^ b)) :=
      lt_of_lt_of_le h_ab_pos hN_n
    rcases mul_pos_iff.mp h_rhs_pos with ⟨hc, _⟩ | ⟨_, hfact⟩
    · exact hc
    · exfalso
      have hfact_nn : 0 ≤ Real.sqrt 2 * Real.sqrt ↑a * Real.sqrt Real.pi * (↑a / Real.exp 1) ^ a *
          (Real.sqrt 2 * Real.sqrt ↑b * Real.sqrt Real.pi * (↑b / Real.exp 1) ^ b) :=
        mul_nonneg
          (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg ↑a))
            (Real.sqrt_nonneg Real.pi)) (by positivity))
          (mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg ↑b))
            (Real.sqrt_nonneg Real.pi)) (by positivity))
      linarith
  have hε'_const_pos : 0 < c_denom * ((q : ℝ) - 1) * Real.exp 1 ^ 2 * Real.sqrt (Real.pi / 2) / p := by
    apply div_pos
    · apply mul_pos; apply mul_pos; apply mul_pos
      · exact hc_pos
      · exact hq1_pos
      · positivity
      · exact Real.sqrt_pos_of_pos (by positivity)
    · exact hp.1
  have hε_pos : 0 < (n : ℝ) ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hn_real _
  -- Rewrite the goal using rpow algebra
  rw [Nat.cast_choose (K := ℝ) ha_le, Real.rpow_sub hq', Real.rpow_add hq',
      Real.rpow_logb hq' hq_ne1 hε'_const_pos,
      show ε n = Real.logb ↑q ((n : ℝ) ^ ((1:ℝ)/2)) from rfl,
      Real.rpow_logb hq' hq_ne1 hε_pos,
      Real.rpow_mul (le_of_lt hq')]
  have h_entropy_ineq :
      (q : ℝ) ^ (qaryEntropy q p * n) ≤
      (q : ℝ) ^ (qaryEntropy q (↑a / ↑n) * n) * (((q : ℝ) - 1) * Real.exp 1 ^ 2 / p) := by
    have hqm1e2_pos : 0 < ((q : ℝ) - 1) * Real.exp 1 ^ 2 / p :=
      div_pos (mul_pos hq1_pos (by positivity)) hp.1
    rw [show ((q : ℝ) - 1) * Real.exp 1 ^ 2 / p =
        (q : ℝ) ^ Real.logb q (((q : ℝ) - 1) * Real.exp 1 ^ 2 / p) from
      (Real.rpow_logb hq' hq_ne1 hqm1e2_pos).symm,
      ← Real.rpow_add hq']
    apply Real.rpow_le_rpow_of_exponent_le (le_of_lt hq1)
    rw [Real.logb_div (ne_of_gt (mul_pos hq1_pos (by positivity))) (ne_of_gt hp.1),
        Real.logb_mul (ne_of_gt hq1_pos) (by positivity),
        Real.logb_pow]
    suffices h : (n : ℝ) * (qaryEntropy q p - qaryEntropy q (↑a / ↑n)) ≤
        Real.logb q ((q : ℝ) - 1) + 2 * Real.logb q (Real.exp 1) - Real.logb q p by linarith
    simp only [qaryEntropy]
    set δ := (n : ℝ) * p - a
    have hδ_ge : 0 ≤ δ := hδ_nn
    have hδ_lt : δ < 1 := hδ_lt1
    have hbn_pos : 0 < (b : ℝ) / n := div_pos hb_real_pos hn_real
    have ha_pos : 0 < a := ha_pos_nat
    have ha_ne : (a : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast ha_pos)
    have h_decomp : (n : ℝ) * (p * Real.logb ↑q (↑q - 1) - p * Real.logb ↑q p -
        (1 - p) * Real.logb ↑q (1 - p) -
        ((↑a / ↑n) * Real.logb ↑q (↑q - 1) - ↑a / ↑n * Real.logb ↑q (↑a / ↑n) -
         (1 - ↑a / ↑n) * Real.logb ↑q (1 - ↑a / ↑n))) =
        δ * Real.logb ↑q (↑q - 1) +
        (a : ℝ) * Real.logb ↑q ((a : ℝ) / ((n : ℝ) * p)) +
        (b : ℝ) * Real.logb ↑q ((b : ℝ) / ((n : ℝ) * (1 - p))) +
        δ * (Real.logb ↑q (1 - p) - Real.logb ↑q p) := by
      have hbn : (b : ℝ) = n - a := hb_real
      have h1 : (1 : ℝ) - ↑a / ↑n = ↑b / ↑n := by rw [hbn]; field_simp
      have h_logb_an : Real.logb ↑q (↑a / ↑n) = Real.logb ↑q ↑a - Real.logb ↑q ↑n :=
        Real.logb_div ha_ne hn_ne
      have h_logb_bn : Real.logb ↑q (↑b / ↑n) = Real.logb ↑q ↑b - Real.logb ↑q ↑n :=
        Real.logb_div (ne_of_gt hb_real_pos) hn_ne
      have h_logb_anp : Real.logb ↑q ((↑a : ℝ) / (↑n * p)) =
          Real.logb ↑q ↑a - Real.logb ↑q ↑n - Real.logb ↑q p := by
        rw [Real.logb_div ha_ne (mul_ne_zero hn_ne (ne_of_gt hp.1)),
            Real.logb_mul hn_ne (ne_of_gt hp.1)]; ring_nf
      have h_logb_bn1p : Real.logb ↑q ((↑b : ℝ) / (↑n * (1 - p))) =
          Real.logb ↑q ↑b - Real.logb ↑q ↑n - Real.logb ↑q (1 - p) := by
        rw [Real.logb_div (ne_of_gt hb_real_pos) (mul_ne_zero hn_ne (ne_of_gt h1p')),
            Real.logb_mul hn_ne (ne_of_gt h1p')]; ring_nf
      rw [h1, h_logb_an, h_logb_bn, h_logb_anp, h_logb_bn1p]
      have ha_b_n : (a : ℝ) + b = n := by
        have := hb_real; push_cast [Nat.cast_sub ha_le] at this ⊢; linarith
      have hna_eq : (n : ℝ) * (↑a / ↑n) = ↑a := mul_div_cancel₀ ↑a hn_ne
      have hnb_eq : (n : ℝ) * (↑b / ↑n) = ↑b := mul_div_cancel₀ ↑b hn_ne
      linear_combination
        (Real.logb ↑q ↑a - Real.logb ↑q (↑q - 1) - Real.logb ↑q ↑n) * hna_eq +
        (Real.logb ↑q ↑b - Real.logb ↑q ↑n) * hnb_eq +
        Real.logb ↑q (1 - p) * ha_b_n
    rw [h_decomp]
    have h_logq1_nn : 0 ≤ Real.logb ↑q (↑q - 1) :=
      Real.logb_nonneg hq1 (by linarith)
    have h_t1 : δ * Real.logb ↑q (↑q - 1) ≤ Real.logb ↑q (↑q - 1) := by
      have hd_le1 : δ ≤ 1 := le_of_lt hδ_lt
      calc δ * Real.logb ↑q (↑q - 1) ≤ 1 * Real.logb ↑q (↑q - 1) :=
            mul_le_mul_of_nonneg_right hd_le1 h_logq1_nn
        _ = Real.logb ↑q (↑q - 1) := one_mul _
    have h_t2 : (a : ℝ) * Real.logb ↑q ((a : ℝ) / ((n : ℝ) * p)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg a)
        (Real.logb_nonpos hq1
          (div_nonneg (Nat.cast_nonneg a) (mul_nonneg (le_of_lt hn_real) (le_of_lt hp.1)))
          (by rwa [div_le_one (mul_pos hn_real hp.1)]))
    have h_t3 : (b : ℝ) * Real.logb ↑q ((b : ℝ) / ((n : ℝ) * (1 - p))) ≤
        2 * Real.logb ↑q (Real.exp 1) := by
      have h_n1p_pos : 0 < (n : ℝ) * (1 - p) := by linarith [h_n1p_ge2]
      have h_bdiv : (b : ℝ) / ((n : ℝ) * (1 - p)) = 1 + δ / ((n : ℝ) * (1 - p)) := by
        rw [hb_expand, add_div, div_self (ne_of_gt h_n1p_pos)]
      rw [h_bdiv]
      have h1pos : 0 < 1 + δ / ((n : ℝ) * (1 - p)) := by positivity
      have hlog_le : Real.log (1 + δ / ((n : ℝ) * (1 - p))) ≤ δ / ((n : ℝ) * (1 - p)) := by
        have := Real.log_le_sub_one_of_pos (show 0 < 1 + δ / (↑n * (1 - p)) from h1pos)
        linarith
      have hlogq_pos : 0 < Real.log ↑q := Real.log_pos hq1
      have hδ_le1 : δ ≤ 1 := le_of_lt hδ_lt
      have h_n1p_ge1 : (1 : ℝ) ≤ (n : ℝ) * (1 - p) := by linarith [h_n1p_ge2]
      have hstepA : (b : ℝ) * Real.logb ↑q (1 + δ / ((n : ℝ) * (1 - p))) ≤
          (b : ℝ) * δ / ((n : ℝ) * (1 - p)) / Real.log ↑q := by
        rw [Real.logb]
        have hgoal : (b : ℝ) * (Real.log (1 + δ / (↑n * (1 - p))) / Real.log ↑q) ≤
            (b : ℝ) * δ / (↑n * (1 - p)) / Real.log ↑q := by
          rw [show (b : ℝ) * (Real.log (1 + δ / (↑n * (1 - p))) / Real.log ↑q) =
              (b : ℝ) * Real.log (1 + δ / (↑n * (1 - p))) / Real.log ↑q by ring_nf,
              show (b : ℝ) * δ / (↑n * (1 - p)) / Real.log ↑q =
              (b : ℝ) * (δ / (↑n * (1 - p))) / Real.log ↑q by ring_nf]
          apply div_le_div_of_nonneg_right _ hlogq_pos.le
          exact mul_le_mul_of_nonneg_left hlog_le (Nat.cast_nonneg b)
        exact hgoal
      have hstepB : (b : ℝ) * δ / ((n : ℝ) * (1 - p)) ≤ 2 := by
        rw [hb_expand, div_le_iff₀ h_n1p_pos]
        have h_sum_nn : (0 : ℝ) ≤ (n : ℝ) * (1 - p) + δ := by linarith
        calc ((n : ℝ) * (1 - p) + δ) * δ
            ≤ (n * (1 - p) + δ) * 1 := mul_le_mul_of_nonneg_left hδ_le1 h_sum_nn
          _ = n * (1 - p) + δ := mul_one _
          _ ≤ n * (1 - p) + 1 := add_le_add_left hδ_le1 _
          _ ≤ n * (1 - p) + n * (1 - p) := add_le_add_left h_n1p_ge1 _
          _ = 2 * (n * (1 - p)) := by ring_nf
      have hstepC : (2 : ℝ) / Real.log ↑q = 2 * Real.logb ↑q (Real.exp 1) := by
        rw [Real.logb, Real.log_exp]; ring_nf
      have hstepD : (b : ℝ) * δ / ((n : ℝ) * (1 - p)) / Real.log ↑q ≤ 2 / Real.log ↑q :=
        div_le_div_of_nonneg_right hstepB hlogq_pos.le
      linarith
    have h_logp_neg : Real.logb ↑q p ≤ 0 :=
      Real.logb_nonpos hq1 hp.1.le hp.2.le
    have h_log1p_neg : Real.logb ↑q (1 - p) ≤ 0 :=
      Real.logb_nonpos hq1 h1p.le (by linarith)
    have h_t4 : δ * (Real.logb ↑q (1 - p) - Real.logb ↑q p) ≤ -(Real.logb ↑q p) := by
      rcases le_or_gt (Real.logb ↑q (1 - p)) (Real.logb ↑q p) with h_le | h_lt
      · have : δ * (Real.logb ↑q (1 - p) - Real.logb ↑q p) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hδ_ge (by linarith)
        linarith
      · calc δ * (Real.logb ↑q (1 - p) - Real.logb ↑q p)
            ≤ 1 * (Real.logb ↑q (1 - p) - Real.logb ↑q p) :=
              mul_le_mul_of_nonneg_right (le_of_lt hδ_lt) (by linarith)
          _ = Real.logb ↑q (1 - p) - Real.logb ↑q p := one_mul _
          _ ≤ -(Real.logb ↑q p) := by linarith
    linarith

  have h_hab : a + b = n := Nat.add_sub_cancel' ha_le
  have h_comb_bound :
      (n : ℝ) ^ n / ((a : ℝ) ^ a * (b : ℝ) ^ b) / (c_denom * Real.sqrt (Real.pi / 2) * Real.sqrt n) ≤
      (n.factorial : ℝ) / ((a.factorial : ℝ) * b.factorial) :=
    stirling_comb_bound ha_pos_r hb_real_pos hc_pos h_hab hN_n

  have ha_pos : 0 < a := ha_pos_nat
  have h_rpow_mono : ((q : ℝ) - 1) ^ (a : ℝ) ≤ ((q : ℝ) - 1) ^ (p * (n : ℝ)) := by
    have ha_pn : (a : ℝ) ≤ p * (n : ℝ) := mul_comm (n : ℝ) p ▸ ha_real
    exact Real.rpow_le_rpow_of_exponent_le hq_ge1 ha_pn
  have h_comb_bound' : (n : ℝ) ^ (n : ℝ) / ((a : ℝ) ^ (a : ℝ) * (b : ℝ) ^ (b : ℝ)) /
      (c_denom * Real.sqrt (Real.pi / 2) * Real.sqrt ↑n) ≤
      (n.factorial : ℝ) / ((a.factorial : ℝ) * b.factorial) := by
    have hn_rw : (n : ℝ) ^ (n : ℝ) = (n : ℝ) ^ n := Real.rpow_natCast _ _
    have ha_rw : (a : ℝ) ^ (a : ℝ) = (a : ℝ) ^ a := Real.rpow_natCast _ _
    have hb_rw : (b : ℝ) ^ (b : ℝ) = (b : ℝ) ^ b := Real.rpow_natCast _ _
    rw [hn_rw, ha_rw, hb_rw]; exact h_comb_bound
  have hcb' : (n : ℝ) ^ (n : ℝ) / ((a : ℝ) ^ (a : ℝ) * (b : ℝ) ^ (b : ℝ)) ≤
      (n.factorial : ℝ) / ((a.factorial : ℝ) * b.factorial) *
      (c_denom * Real.sqrt (Real.pi / 2) * Real.sqrt ↑n) := by
    have hpos : 0 < c_denom * Real.sqrt (Real.pi / 2) * Real.sqrt ↑n := by positivity
    rwa [div_le_iff₀ hpos] at h_comb_bound'
  have ha_ne : (a : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast ha_pos)
  have h_exact : (↑q : ℝ) ^ (qaryEntropy ↑q (↑a / ↑n) * ↑n) =
      (↑q - 1) ^ (a : ℝ) * ((n : ℝ) ^ (n : ℝ) / ((a : ℝ) ^ (a : ℝ) * (b : ℝ) ^ (b : ℝ))) := by
    simp only [qaryEntropy]
    have h1 : (1 : ℝ) - ↑a / ↑n = ↑b / ↑n := by rw [hb_real]; field_simp
    have h_logb_an : Real.logb ↑q (↑a / ↑n) = Real.logb ↑q ↑a - Real.logb ↑q ↑n :=
      Real.logb_div ha_ne hn_ne
    have h_logb_bn : Real.logb ↑q (↑b / ↑n) = Real.logb ↑q ↑b - Real.logb ↑q ↑n :=
      Real.logb_div (ne_of_gt hb_real_pos) hn_ne
    have h_ab_sum_r : (a : ℝ) + b = n := by exact_mod_cast h_hab
    rw [h1, h_logb_an, h_logb_bn]
    have hexp_eq : (↑a / ↑n * Real.logb ↑q (↑q - 1) -
        ↑a / ↑n * (Real.logb ↑q ↑a - Real.logb ↑q ↑n) -
        ↑b / ↑n * (Real.logb ↑q ↑b - Real.logb ↑q ↑n)) * ↑n =
        ↑a * Real.logb ↑q (↑q - 1) + ↑n * Real.logb ↑q ↑n
          - ↑a * Real.logb ↑q ↑a - ↑b * Real.logb ↑q ↑b := by
      have : Real.logb ↑q ↑n * (↑a + ↑b) = Real.logb ↑q ↑n * ↑n := by
        rw [h_ab_sum_r]
      field_simp [hn_ne]; linarith
    rw [hexp_eq]
    have hval_pos : 0 < (↑q - 1) ^ (↑a : ℝ) * (↑n : ℝ) ^ (↑n : ℝ) /
        ((↑a : ℝ) ^ (↑a : ℝ) * (↑b : ℝ) ^ (↑b : ℝ)) := by positivity
    rw [show ↑a * Real.logb ↑q (↑q - 1) + ↑n * Real.logb ↑q ↑n -
        ↑a * Real.logb ↑q ↑a - ↑b * Real.logb ↑q ↑b =
        Real.logb ↑q ((↑q - 1) ^ (↑a : ℝ) * (↑n : ℝ) ^ (↑n : ℝ) /
          ((↑a : ℝ) ^ (↑a : ℝ) * (↑b : ℝ) ^ (↑b : ℝ))) from by
      rw [Real.logb_div (by positivity) (by positivity),
          Real.logb_mul (by positivity) (by positivity),
          Real.logb_mul (by positivity) (by positivity),
          Real.logb_rpow_eq_mul_logb_of_pos hq1_pos,
          Real.logb_rpow_eq_mul_logb_of_pos hn_real,
          Real.logb_rpow_eq_mul_logb_of_pos ha_pos_r,
          Real.logb_rpow_eq_mul_logb_of_pos hb_real_pos]
      ring_nf]
    rw [Real.rpow_logb hq' hq_ne1 hval_pos]
    ring_nf
  have h_entropy_ineq' : (↑q ^ qaryEntropy ↑q p) ^ (n : ℝ) ≤
      ↑q ^ (qaryEntropy ↑q (↑a / ↑n) * ↑n) * (((↑q : ℝ) - 1) * Real.exp 1 ^ 2 / p) := by
    rw [← Real.rpow_mul (le_of_lt hq')]
    exact h_entropy_ineq
  have h_sqrt_n : Real.sqrt (n : ℝ) = (n : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  have h_denom_pos : 0 < c_denom * ((q : ℝ) - 1) * Real.exp 1 ^ 2 *
      Real.sqrt (Real.pi / 2) / p * (n : ℝ) ^ ((1 : ℝ) / 2) := mul_pos hε'_const_pos hε_pos
  rw [div_le_iff₀ h_denom_pos]
  suffices h : (↑q ^ qaryEntropy ↑q p) ^ (n : ℝ) ≤
      ↑n.factorial / (↑a.factorial * (b.factorial : ℝ)) * ((q : ℝ) - 1) ^ (p * ↑n) *
        (c_denom * ((↑q - 1) * Real.exp 1 ^ 2 * Real.sqrt (Real.pi / 2) / p) *
          (n : ℝ) ^ ((1 : ℝ) / 2)) by
    have hb_fact : (b.factorial : ℝ) = ((n - a).factorial : ℝ) := by norm_cast
    calc (↑q ^ qaryEntropy ↑q p) ^ (n : ℝ)
        ≤ ↑n.factorial / (↑a.factorial * (b.factorial : ℝ)) * ((q : ℝ) - 1) ^ (p * ↑n) *
              (c_denom * ((↑q - 1) * Real.exp 1 ^ 2 * Real.sqrt (Real.pi / 2) / p) *
                (n : ℝ) ^ ((1 : ℝ) / 2)) := h
      _ = ↑n.factorial / (↑a.factorial * ↑(n - a).factorial) * ((q : ℝ) - 1) ^ (p * ↑n) *
              (c_denom * (↑q - 1) * Real.exp 1 ^ 2 * Real.sqrt (Real.pi / 2) / p *
                (n : ℝ) ^ ((1 : ℝ) / 2)) := by rw [← hb_fact]; ring_nf
  have h1_pos : 0 < ((q : ℝ) - 1) ^ (p * (n : ℝ)) := Real.rpow_pos_of_pos hq1_pos _
  have h2_pos : 0 < ((↑q : ℝ) - 1) * Real.exp 1 ^ 2 / p :=
    div_pos (mul_pos hq1_pos (by positivity)) hp.1
  calc (↑q ^ qaryEntropy ↑q p) ^ (n : ℝ)
      ≤ ↑q ^ (qaryEntropy ↑q (↑a / ↑n) * ↑n) * (((↑q : ℝ) - 1) * Real.exp 1 ^ 2 / p) :=
            h_entropy_ineq'
    _ = (↑q - 1) ^ (a : ℝ) * ((n : ℝ) ^ (n : ℝ) / ((a : ℝ) ^ (a : ℝ) * (b : ℝ) ^ (b : ℝ))) *
            (((↑q : ℝ) - 1) * Real.exp 1 ^ 2 / p) := by rw [h_exact]
    _ ≤ ((q : ℝ) - 1) ^ (p * ↑n) * ((n : ℝ) ^ (n : ℝ) / ((a : ℝ) ^ (a : ℝ) * (b : ℝ) ^ (b : ℝ))) *
            (((↑q : ℝ) - 1) * Real.exp 1 ^ 2 / p) := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt h2_pos)
              exact mul_le_mul_of_nonneg_right h_rpow_mono (by positivity)
    _ ≤ ↑(n.factorial) / (↑(a.factorial) * ↑(b.factorial)) * ((q : ℝ) - 1) ^ (p * ↑n) *
            (c_denom * ((↑q - 1) * Real.exp 1 ^ 2 * Real.sqrt (Real.pi / 2) / p) *
              (n : ℝ) ^ ((1 : ℝ) / 2)) := by
              rw [show ((q : ℝ) - 1) ^ (p * ↑n) * ((n : ℝ) ^ (n : ℝ) /
                    ((a : ℝ) ^ (a : ℝ) * (b : ℝ) ^ (b : ℝ))) *
                    (((↑q : ℝ) - 1) * Real.exp 1 ^ 2 / p) =
                  (((q : ℝ) - 1) ^ (p * ↑n) * (((↑q : ℝ) - 1) * Real.exp 1 ^ 2 / p)) *
                    ((n : ℝ) ^ (n : ℝ) / ((a : ℝ) ^ (a : ℝ) * (b : ℝ) ^ (b : ℝ))) by ring_nf]
              rw [show ↑(n.factorial) / (↑(a.factorial) * ↑(b.factorial)) * ((q : ℝ) - 1) ^ (p * ↑n) *
                    (c_denom * ((↑q - 1) * Real.exp 1 ^ 2 * Real.sqrt (Real.pi / 2) / p) *
                     (n : ℝ) ^ ((1 : ℝ) / 2)) =
                  (((q : ℝ) - 1) ^ (p * ↑n) * (((↑q : ℝ) - 1) * Real.exp 1 ^ 2 / p)) *
                    (↑(n.factorial) / (↑(a.factorial) * ↑(b.factorial)) *
                      (c_denom * Real.sqrt (Real.pi / 2) * (n : ℝ) ^ ((1 : ℝ) / 2))) by ring_nf]
              rw [← h_sqrt_n]
              exact mul_le_mul_of_nonneg_left hcb' (mul_pos h1_pos h2_pos).le
}

/-- The q-ary entropy `H_q(p)` is strictly positive for `0 < p ≤ 1 - 1/q`. -/
theorem qary_entropy_pos (q : ℕ) (p : ℝ) (hq : q = (Fintype.card α))
    (hp : 0 < p ∧ p ≤ 1 - 1 / (q : ℝ)) :
    0 < p * Real.logb (q : ℝ) ((q : ℝ) - 1) - p * Real.logb (q : ℝ) p -
        (1 - p) * Real.logb (q : ℝ) (1 - p) := by
  have hq_two : 2 ≤ q := by
    rw [hq]
    exact Nat.succ_le_iff.mpr (by simpa using Fintype.one_lt_card)
  have hq_1 : (1 : ℝ) < (q : ℝ) := natCast_one_lt_of_two_le hq_two
  have hqpos : (0 : ℝ) < (q : ℝ) := natCast_pos_of_two_le hq_two
  have hp_1 : p < 1 := lt_one_of_le_one_sub_inv hqpos hp.2
  have h1p_0 : 0 < 1 - p := one_sub_pos_of_lt_one hp_1
  have h1p_1 : 1 - p < 1 := by linarith
  have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos hq_1

  suffices 0 < p * Real.log ((q : ℝ) - 1) - p * Real.log p - (1 - p) * Real.log (1 - p) by
    have := (div_pos_iff.mpr (Or.inl ⟨this, hlogq_pos⟩))
    simp only [Real.logb, div_eq_mul_inv]
    simp only [div_eq_mul_inv] at this
    have hdistrib : (p * Real.log (↑q - 1) - p * Real.log p - (1 - p) * Real.log (1 - p)) * (Real.log ↑q)⁻¹ = p * (Real.log (↑q - 1) * (Real.log ↑q)⁻¹) - p * (Real.log p * (Real.log ↑q)⁻¹) - (1 - p) * (Real.log (1 - p) * (Real.log ↑q)⁻¹) := by
      simp only [sub_eq_add_neg]
      rw [distrib_three_right]
      simp [mul_assoc]
    rw [hdistrib] at this
    exact this

  have h_ent_pos :
      0 < - p * Real.log p - (1 - p) * Real.log (1 - p) := by
    have hp_neg : 0 < -p * Real.log p := by
      have := mul_neg_of_pos_of_neg hp.1 (Real.log_neg hp.1 hp_1)
      simpa [neg_mul, neg_neg] using this
    have h1p_neg : 0 < -(1 - p) * Real.log (1 - p) := by
      have := mul_neg_of_pos_of_neg h1p_0 (Real.log_neg h1p_0 h1p_1)
      linarith
    linarith

  have hlog_q_sub_one_nonneg : 0 ≤ Real.log ((q : ℝ) - 1) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ (q : ℝ) - 1 := by
      have hq_two_real : (2 : ℝ) ≤ q := by exact_mod_cast hq_two
      linarith
    exact this
  have : 0 < p * Real.log ((q : ℝ) - 1)
                + (- p * Real.log p - (1 - p) * Real.log (1 - p)) := by
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (le_of_lt hp.1) hlog_q_sub_one_nonneg) h_ent_pos
  ring_nf at this ⊢
  exact this

end Codeword
end CodingTheory
