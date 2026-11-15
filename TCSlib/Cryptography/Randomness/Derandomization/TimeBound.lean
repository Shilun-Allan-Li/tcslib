/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TCSlib.Cryptography.Randomness.Derandomization.RootSchedule

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The subexponential seed-enumeration bound

A ceiling-root seed width eventually satisfies `w(n) ≤ n^(1/d)+1`.
For `1/d < ε`, its exponential times any fixed polynomial is eventually
below `2^(n^ε)`. A single natural constant absorbs every earlier length.

## Main results

* `TCSlib.Cryptography.Randomness.Derand.exists_root_degree`: a positive
  integer degree valid for every real `ε > 0`.
* `TCSlib.Cryptography.Randomness.Derand.seed_time_le_subexp`: the global
  time bound, including the finite exceptional lengths.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, §8.2, Theorem 180.1.
-/

namespace TCSlib.Cryptography.Randomness.Derand

open Filter Topology

/-- Every positive real exponent admits a fixed integer degree:
`∃ d ≥ 2, 1 / (d : ℝ) < ε ∧ 1 / (d : ℝ) < 1`.
[PS10, §8.2, Theorem 180.1] -/
theorem exists_root_degree {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℕ, 2 ≤ d ∧ 1 / (d : ℝ) < ε ∧ 1 / (d : ℝ) < 1 := by
  obtain ⟨d, hd⟩ := exists_nat_gt (max (1 / ε) 1)
  have hd1 : (1 : ℝ) < d := (le_max_right _ _).trans_lt hd
  have hdp : (0 : ℝ) < d := lt_trans zero_lt_one hd1
  have hde : 1 / ε < (d : ℝ) := (le_max_left _ _).trans_lt hd
  have hmul := (div_lt_iff₀ hε).mp hde
  refine ⟨d, ?_, (div_lt_iff₀ hdp).mpr (by nlinarith), (div_lt_one hdp).mpr hd1⟩
  have : 1 < d := by exact_mod_cast hd1
  omega

/-- If `w n = ceilRoot d n` from some length onward and `1/d < ε`, then
`2^(w n) * (n+1)^e ≤ C * ⌈2^(n^ε)⌉₊` for one natural `C` and every `n`.
[PS10, §8.2, Theorem 180.1]

**Proof sketch.** Divide the logarithmic upper bound
`(n^(1/d)+1) log 2 + e(log 2 + log n)` by `n^ε`. Its root term tends to zero
as `n^(1/d-ε)`, its constant term does so because `n^ε → ∞`, and its logarithm
term does so by Mathlib's `isLittleO_log_rpow_atTop`. Eventually the quotient
is below `log 2`. For `n ≥ 1`, use `n+1 ≤ 2n`, the ceiling-root bound and
monotonicity of logarithms to bound the actual enumeration time. Exponentiating
gives the desired real bound, and rounding up preserves it. For earlier lengths,
one plus the sum of their time bounds is enough, because the rounded bound
is positive at every length. -/
theorem seed_time_le_subexp {d : ℕ} (hd : 0 < d) {ε : ℝ} (hε : 0 < ε)
    (hr : 1 / (d : ℝ) < ε) (w : ℕ → ℕ) (n₀ : ℕ)
    (hw : ∀ n, n₀ ≤ n → w n = ceilRoot d n) (e : ℕ) :
    ∃ C : ℕ, ∀ n, 2 ^ w n * (n + 1) ^ e ≤
      C * ⌈(2 : ℝ) ^ ((n : ℝ) ^ ε)⌉₊ := by
  let r : ℝ := 1 / (d : ℝ)
  have hratio : Tendsto (fun x : ℝ => x ^ r / x ^ ε) atTop (𝓝 0) := by
    apply (tendsto_rpow_neg_atTop (sub_pos.mpr hr)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [show -(ε - r) = r - ε by ring, Real.rpow_sub hx]
  have hconst : Tendsto (fun x : ℝ => 1 / x ^ ε) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_rpow_atTop hε).inv_tendsto_atTop
  have hlog : Tendsto (fun x : ℝ => Real.log x / x ^ ε) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop hε).tendsto_div_nhds_zero
  have hsum : Tendsto (fun x : ℝ => Real.log 2 * (x ^ r / x ^ ε) +
      (((e : ℝ) + 1) * Real.log 2) * (1 / x ^ ε) +
      (e : ℝ) * (Real.log x / x ^ ε)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add, add_zero] using
      ((hratio.const_mul (Real.log 2)).add
        (hconst.const_mul (((e : ℝ) + 1) * Real.log 2))).add (hlog.const_mul (e : ℝ))
  have hlim : Tendsto (fun x : ℝ =>
      ((x ^ r + 1) * Real.log 2 + (e : ℝ) * (Real.log 2 + Real.log x)) / x ^ ε)
      atTop (𝓝 0) := by
    apply hsum.congr'
    exact Eventually.of_forall fun x => by ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hlim.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hlog2))
  let K := max N (max n₀ 1)
  let f (n : ℕ) := 2 ^ w n * (n + 1) ^ e
  have hevent (n : ℕ) (hn : K ≤ n) : f n ≤ ⌈(2 : ℝ) ^ ((n : ℝ) ^ ε)⌉₊ := by
    have hnN : N ≤ n := (le_max_left _ _).trans hn
    have hnn₀ : n₀ ≤ n := (le_max_left n₀ 1).trans ((le_max_right _ _).trans hn)
    have hn1 : 1 ≤ n := (le_max_right n₀ 1).trans ((le_max_right _ _).trans hn)
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnp : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnr
    have hbudget := (div_lt_iff₀ (Real.rpow_pos_of_pos hnp ε)).mp (hN n hnN)
    have hroot : (w n : ℝ) ≤ (n : ℝ) ^ r + 1 := by
      rw [hw n hnn₀]
      exact ceilRoot_le_real hd n
    have hsucc : Real.log ((n : ℝ) + 1) ≤ Real.log 2 + Real.log (n : ℝ) := by
      calc
        Real.log ((n : ℝ) + 1) ≤ Real.log (2 * (n : ℝ)) :=
          Real.log_le_log (by positivity) (by linarith)
        _ = Real.log 2 + Real.log (n : ℝ) := Real.log_mul (by norm_num) hnp.ne'
    have hactual : Real.log (f n : ℝ) ≤ Real.log 2 * (n : ℝ) ^ ε := by
      calc
        Real.log (f n : ℝ) = (w n : ℝ) * Real.log 2 +
            (e : ℝ) * Real.log ((n : ℝ) + 1) := by
          simp only [f, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
            Nat.cast_ofNat]
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
        _ ≤ ((n : ℝ) ^ r + 1) * Real.log 2 +
            (e : ℝ) * (Real.log 2 + Real.log (n : ℝ)) :=
          add_le_add (mul_le_mul_of_nonneg_right hroot hlog2.le)
            (mul_le_mul_of_nonneg_left hsucc (Nat.cast_nonneg e))
        _ ≤ Real.log 2 * (n : ℝ) ^ ε := hbudget.le
    have hreal : (f n : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) ^ ε) := by
      apply (Real.log_le_log_iff (by dsimp only [f]; positivity)
        (Real.rpow_pos_of_pos (by norm_num) _)).mp
      rw [Real.log_rpow (by norm_num)]
      nlinarith [hactual]
    exact_mod_cast hreal.trans (Nat.le_ceil _)
  let C := 1 + ∑ i ∈ Finset.range K, f i
  refine ⟨C, fun n => ?_⟩
  have hC : 1 ≤ C := by dsimp only [C]; omega
  by_cases hn : K ≤ n
  · exact (hevent n hn).trans (Nat.le_mul_of_pos_left _ hC)
  · have hsmall : f n ≤ ∑ i ∈ Finset.range K, f i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    have hb : 1 ≤ ⌈(2 : ℝ) ^ ((n : ℝ) ^ ε)⌉₊ :=
      Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)
    have hsmallC : f n ≤ C := by
      dsimp only [C]
      omega
    exact hsmallC.trans
      (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left C hb)

end TCSlib.Cryptography.Randomness.Derand
