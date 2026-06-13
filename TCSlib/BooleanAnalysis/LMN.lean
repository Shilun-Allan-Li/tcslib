import TCSlib.BooleanAnalysis.LMN.RestrictionCompose
import TCSlib.BooleanAnalysis.LMN.SwitchingBernoulli
import TCSlib.BooleanAnalysis.LMN.GateSwitching
import TCSlib.BooleanAnalysis.LMN.CircuitCompression
import TCSlib.BooleanAnalysis.LMN.IterativeReduction
import TCSlib.BooleanAnalysis.LMN.CircuitLayerReduction
import TCSlib.BooleanAnalysis.LMN.Depth3Switching
import TCSlib.BooleanAnalysis.LMN.CircuitTreeManip
import TCSlib.BooleanAnalysis.LMN.RestrictionMonotonicity
import Mathlib

/-!
# LMN Theorem Infrastructure

This file provides the infrastructure for the LMN theorem (Lemma 4.28 from
O'Donnell's *Analysis of Boolean Functions*).

## Main results

- `bernoulliRestrProb_mono`: monotonicity of Bernoulli restriction probabilities
- Arithmetic helpers for the `logb`-based parameters
- `switching_bernoulli_dtDepth_dnf` / `cnf`: Bernoulli versions of the switching lemma
  (proved in `LMN.SwitchingBernoulli`)
- `iterative_reduction_bound`: the iterative circuit reduction bound
- `odonnell_lemma_4_28`: the main LMN theorem

## Constant choices

The Bernoulli switching lemma (step 3) requires `p ≤ 1/(40w)` (rather than
the ideal `1/(10w)`) because:
- The counting switching lemma gives `Pr_{R_k}[bad] ≤ (10kw/n)^d`
- Passing through the Bernoulli cost theorem doubles the constant to `(20pw)^d`
- To get `(20pw)^d ≤ (1/2)^d`, we need `p ≤ 1/(40w)`

There is also a Chernoff tail `exp(-np/3)` that vanishes as `n → ∞`.
The overall δ for the LMN theorem is correspondingly adjusted.
-/

open BoolCircuit SwitchingLemma2 SwitchingBernoulli LMN
open Classical in
attribute [local instance] Classical.propDecidable
noncomputable section
namespace LMN
variable {n : ℕ}

set_option maxHeartbeats 400000

/-! ## Arithmetic helper lemmas -/

/-- When `0 < ε ≤ 1` and `0 < s`, we have `l = logb 2 (2s/ε) ≥ 1`. -/
lemma logb_2s_div_eps_pos (s : ℕ) (hs : 0 < s) (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1) :
    1 ≤ Real.logb 2 (2 * ↑s / ε) := by
  have h2 : (1:ℝ) < 2 := by norm_num
  rw [← Real.logb_self_eq_one h2]
  have hs' : (1:ℝ) ≤ ↑s := Nat.one_le_cast.mpr hs
  exact (Real.logb_le_logb h2 (by norm_num : (0:ℝ) < 2) (by positivity)).mpr
    (by rw [le_div_iff₀ hε_pos]; nlinarith)

/-- `logb 2 (2/ε) ≤ logb 2 (2s/ε)` when `s ≥ 1`. -/
lemma logb_2_div_eps_le_l (s : ℕ) (hs : 0 < s)
    (ε : ℝ) (hε_pos : 0 < ε) :
    Real.logb 2 (2 / ε) ≤ Real.logb 2 (2 * ↑s / ε) := by
  have h2 : (1:ℝ) < 2 := by norm_num
  have hs' : (1:ℝ) ≤ ↑s := Nat.one_le_cast.mpr hs
  exact (Real.logb_le_logb h2 (by positivity) (by positivity)).mpr
    (by rw [div_le_div_iff_of_pos_right hε_pos]; nlinarith)

/-- `s * 2^{-l} ≤ ε/2` when `l = logb 2 (2s/ε)`, since `2^{-l} = ε/(2s)`. -/
lemma size_times_two_pow_neg_l_le (s : ℕ) (hs : 0 < s)
    (ε : ℝ) (hε_pos : 0 < ε) :
    (s : ℝ) * (2 : ℝ)⁻¹ ^ Real.logb 2 (2 * ↑s / ε) ≤ ε / 2 := by
  rw [Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2)]
  rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
  have hs' : (0 : ℝ) < ↑s := Nat.cast_pos.mpr hs
  have : (2 * ↑s / ε)⁻¹ = ε / (2 * ↑s) := by field_simp
  rw [this, show ↑s * (ε / (2 * ↑s)) = ε / 2 from by field_simp]

/-- `2⁻¹ ^ logb 2 (2/ε) = ε/2`. -/
lemma two_pow_neg_logb_2_div_eps (ε : ℝ) (hε_pos : 0 < ε) :
    (2 : ℝ)⁻¹ ^ Real.logb 2 (2 / ε) = ε / 2 := by
  rw [Real.inv_rpow (by norm_num : (0:ℝ) ≤ 2)]
  rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
  field_simp

/-! ## Bernoulli switching lemma (proved in SwitchingBernoulli.lean) -/

-- The Bernoulli switching lemma for DNFs and CNFs is now proved in
-- `TCSlib.BooleanAnalysis.LMN.SwitchingBernoulli`:
--
-- theorem SwitchingBernoulli.switching_bernoulli_dtDepth_dnf (f : DNF n) (w : ℕ)
--     (hw : f.width ≤ w) (hw_pos : 0 < w)
--     (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
--     (hnodup : ∀ t ∈ f, t.Nodup)
--     (hn : 0 < n)
--     (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / (40 * ↑w)) (hp1 : p ≤ 1)
--     (t : ℕ) :
--     bernoulliRestrProb p (fun ρ => dtDepth (restrictFn f.eval ρ) > t)
--       ≤ (1/2)^t + exp(-np/3)
--
-- and similarly for CNFs.

/-! ## Iterative circuit reduction bound -/

/-- **Iterative circuit reduction bound (with Chernoff tails).**

For a circuit of depth `d ≥ 2`, size `≤ s`, and width `≤ w`, under a
Bernoulli(`δ`)-random restriction where `δ = composedDelta w l d`,
the probability that the restricted function has decision-tree depth
exceeding `t` is at most:

  `s · (1/2)^l + (1/2)^t + s · exp(−n/(120w)) + (s+1) · exp(−n/(120l))`

The Chernoff tails vanish exponentially as `n → ∞`. -/
lemma iterative_reduction_bound (c : Circuit n)
    (d s w : ℕ) (l t : ℕ)
    (hd : c.depth ≤ d) (hs : c.size ≤ s) (hw : c.maxFanin ≤ w)
    (hd2 : 2 ≤ d) (hs_pos : 0 < s) (hw_pos : 0 < w) (hl_pos : 0 < l)
    (hn : 0 < n) :
    bernoulliRestrProb (composedDelta w (↑l) d)
      (fun ρ => dtDepth (restrictFn (c.eval) ρ) > t) ≤
    ↑s * (1 / 2 : ℝ) ^ l + (1 / 2 : ℝ) ^ t +
    ↑s * Real.exp (-(↑n / (120 * ↑w))) +
    ↑s * Real.exp (-(↑n / (120 * ↑l))) :=
  circuit_reduction_core (c.eval) d s w l t hd2 hs_pos hw_pos hl_pos hn
    ⟨c, hd, hs, hw, fun x => rfl⟩

/-! ## Main theorem -/

/-- **Lemma 4.28** (O'Donnell, *Analysis of Boolean Functions*) — with tails.

    Let `f` be computable by a depth-`d` circuit of size `s` and width `w`.
    Choose natural numbers `l, t` with `s · (1/2)^l ≤ ε/2` and
    `(1/2)^t ≤ ε/2`. Then under a Bernoulli(`composedDelta w l d`)
    restriction `ρ`:

    `Pr[DT(f|_ρ) > t] ≤ ε + s · exp(−n/(120w)) + (s+1) · exp(−n/(120l))`

    The exponential tails vanish as `n → ∞`, giving `Pr ≤ ε` asymptotically. -/
theorem odonnell_lemma_4_28 (c : Circuit n)
    (d s w : ℕ) (l t : ℕ)
    (hd : c.depth ≤ d) (hs : c.size ≤ s) (hw : c.maxFanin ≤ w)
    (hd2 : 2 ≤ d) (hs_pos : 0 < s) (hw_pos : 0 < w) (hl_pos : 0 < l)
    (hn : 0 < n)
    (ε : ℝ) (_hε_pos : 0 < ε)
    (hl_bound : (↑s : ℝ) * (1 / 2 : ℝ) ^ l ≤ ε / 2)
    (ht_bound : (1 / 2 : ℝ) ^ t ≤ ε / 2) :
    bernoulliRestrProb (composedDelta w (↑l) d)
      (fun ρ => dtDepth (restrictFn (c.eval) ρ) > t) ≤
    ε + ↑s * Real.exp (-(↑n / (120 * ↑w))) +
    ↑s * Real.exp (-(↑n / (120 * ↑l))) := by
  have h_iter := iterative_reduction_bound c d s w l t hd hs hw hd2 hs_pos hw_pos hl_pos hn
  linarith

end LMN
end
