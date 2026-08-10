import TCSlib.BooleanAnalysis.LMN.FourierConcentration

/-!
# LMN Fourier Concentration for Circuits at Logarithmic Degree

Composes the two halves of the LMN argument:

* `odonnell_lemma_4_28` (LMN.lean): under a Bernoulli(`composedDelta w l d`)
  restriction, a depth-`d` size-`s` width-`w` circuit collapses to decision
  tree depth `≤ t` except with probability `ε` plus Chernoff tails;
* `odonnell_lemma_4_21` (FourierConcentration.lean): a small probability of
  high decision-tree depth under restriction forces Fourier concentration.

## Main results

* `circuit_fourier_concentration` (parametric): for a circuit `c` with
  `depth ≤ d`, `size ≤ s`, `maxFanin ≤ w` and switching parameters `l, t`,

    `∑_{U : 3(t+1) ≤ δ·|U|} ĉ(U)² ≤ 4·(ε + s·e^{−n/120w} + s·e^{−n/120l})`

  where `δ = composedDelta w l d = (1/40w)·(1/40l)^{d−2}`.

* `composedDelta_mul_card_iff`: the degree threshold unfolded —
  `3(t+1) ≤ δ·|U|` iff `|U| ≥ 3(t+1)·40w·(40l)^{d−2}`, exhibiting the
  threshold as `O(w · log(s/ε)^{d−2} · log(1/ε))`: **logarithmic degree**
  for constant depth (polylogarithmic in `s/ε`).

* `circuit_fourier_concentration_log`: the instantiation
  `l = ⌈log₂(2s/ε)⌉₊`, `t = ⌈log₂(2/ε)⌉₊`, discharging the switching-side
  hypotheses via the `logb` helper lemmas of `LMN.lean`, so the only
  remaining inputs are the circuit bounds and `0 < ε ≤ 1`.

The Chernoff tail terms `s·e^{−n/120w} + s·e^{−n/120l}` are inherited from
`odonnell_lemma_4_28` and vanish as `n → ∞`.
-/

open BooleanAnalysis BoolCircuit SwitchingLemma2 LMN
open Classical

noncomputable section

namespace RestrictionFourier

variable {n : ℕ}

/-! ## The parametric concentration theorem -/

/-- **LMN Fourier concentration (parametric form)**: a circuit of depth `≤ d`,
    size `≤ s`, fan-in `≤ w` has Fourier weight at most
    `4(ε + Chernoff tails)` above degree `3(t+1)/composedDelta w l d`,
    whenever the switching parameters satisfy `s·2⁻ˡ ≤ ε/2` and `2⁻ᵗ ≤ ε/2`. -/
theorem circuit_fourier_concentration (c : Circuit n) (d s w l t : ℕ)
    (hd : c.depth ≤ d) (hs : c.size ≤ s) (hw : c.maxFanin ≤ w)
    (hd2 : 2 ≤ d) (hs_pos : 0 < s) (hw_pos : 0 < w) (hl_pos : 0 < l)
    (hn : 0 < n) (ε : ℝ) (hε_pos : 0 < ε)
    (hl_bound : (↑s : ℝ) * (1 / 2 : ℝ) ^ l ≤ ε / 2)
    (ht_bound : (1 / 2 : ℝ) ^ t ≤ ε / 2) :
    ∑ U : Finset (Fin n),
        (if 3 * ((t + 1 : ℕ) : ℝ) ≤ composedDelta w (↑l) d * U.card
          then fourierCoeff (fun x => boolToSign (c.eval x)) U ^ 2 else 0)
      ≤ 4 * (ε + ↑s * Real.exp (-(↑n / (120 * ↑w)))
              + ↑s * Real.exp (-(↑n / (120 * ↑l)))) := by
  have hl1R : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl_pos
  have hδ0 : 0 ≤ composedDelta w (↑l) d :=
    le_of_lt (composedDelta_pos w (↑l) d hw_pos (by exact_mod_cast hl_pos))
  have hδ1 : composedDelta w (↑l) d ≤ 1 :=
    composedDelta_le_one w (↑l) d hw_pos hl1R hd2
  have h421 := odonnell_lemma_4_21 (c.eval) (composedDelta w (↑l) d) hδ0 hδ1
    (t + 1) (Nat.le_add_left 1 t)
  have hevent : bernoulliRestrProb (composedDelta w (↑l) d)
      (fun ρ => t + 1 ≤ dtDepth (restrictFn (c.eval) ρ))
      = bernoulliRestrProb (composedDelta w (↑l) d)
        (fun ρ => dtDepth (restrictFn (c.eval) ρ) > t) := by
    unfold bernoulliRestrProb
    refine Finset.sum_congr rfl fun ρ _ => ?_
    congr 1
  have h428 := odonnell_lemma_4_28 c d s w l t hd hs hw hd2 hs_pos hw_pos
    hl_pos hn ε hε_pos hl_bound ht_bound
  calc ∑ U : Finset (Fin n),
        (if 3 * ((t + 1 : ℕ) : ℝ) ≤ composedDelta w (↑l) d * U.card
          then fourierCoeff (fun x => boolToSign (c.eval x)) U ^ 2 else 0)
      ≤ 4 * bernoulliRestrProb (composedDelta w (↑l) d)
          (fun ρ => t + 1 ≤ dtDepth (restrictFn (c.eval) ρ)) := h421
    _ = 4 * bernoulliRestrProb (composedDelta w (↑l) d)
          (fun ρ => dtDepth (restrictFn (c.eval) ρ) > t) := by rw [hevent]
    _ ≤ 4 * (ε + ↑s * Real.exp (-(↑n / (120 * ↑w)))
            + ↑s * Real.exp (-(↑n / (120 * ↑l)))) := by linarith

/-! ## The degree threshold, unfolded -/

/-- The concentration threshold in explicit form: `a ≤ composedDelta·|U|`
    iff `|U| ≥ a · 40w · (40l)^{d−2}`. With `a = 3(t+1)`,
    `l ≈ log₂(s/ε)`, `t ≈ log₂(1/ε)` this exhibits the LMN degree bound
    `O(w · log(s/ε)^{d−2} · log(1/ε))`. -/
lemma composedDelta_mul_card_iff (w l d : ℕ) (hw : 0 < w) (hl : 0 < l)
    (a : ℝ) (m : ℕ) :
    a ≤ composedDelta w (↑l) d * ↑m
      ↔ a * (40 * ↑w * (40 * ↑l) ^ (d - 2)) ≤ (m : ℝ) := by
  have hw' : (0 : ℝ) < ↑w := by exact_mod_cast hw
  have hl' : (0 : ℝ) < ↑l := by exact_mod_cast hl
  have hpos : (0 : ℝ) < 40 * ↑w * (40 * ↑l) ^ (d - 2) := by positivity
  unfold composedDelta
  rw [one_div, one_div, inv_pow, ← mul_inv, inv_mul_eq_div, le_div_iff₀ hpos]

/-! ## The logarithmic instantiation -/

/-- **LMN Fourier concentration at logarithmic degree**: choosing
    `l = ⌈log₂(2s/ε)⌉₊` and `t = ⌈log₂(2/ε)⌉₊`, a circuit of depth `≤ d`,
    size `≤ s`, fan-in `≤ w` has Fourier weight at most `4ε` plus vanishing
    Chernoff tails above degree
    `3(⌈log₂(2/ε)⌉₊+1) · 40w · (40⌈log₂(2s/ε)⌉₊)^{d−2}` —
    i.e. `O(w·log(s/ε)^{d−2}·log(1/ε))`. -/
theorem circuit_fourier_concentration_log (c : Circuit n) (d s w : ℕ)
    (hd : c.depth ≤ d) (hs : c.size ≤ s) (hw : c.maxFanin ≤ w)
    (hd2 : 2 ≤ d) (hs_pos : 0 < s) (hw_pos : 0 < w) (hn : 0 < n)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1) :
    ∑ U : Finset (Fin n),
        (if 3 * ((⌈Real.logb 2 (2 / ε)⌉₊ + 1 : ℕ) : ℝ)
            ≤ composedDelta w (↑⌈Real.logb 2 (2 * ↑s / ε)⌉₊) d * U.card
          then fourierCoeff (fun x => boolToSign (c.eval x)) U ^ 2 else 0)
      ≤ 4 * (ε + ↑s * Real.exp (-(↑n / (120 * ↑w)))
              + ↑s * Real.exp (-(↑n / (120 * ↑⌈Real.logb 2 (2 * ↑s / ε)⌉₊)))) := by
  set l : ℕ := ⌈Real.logb 2 (2 * ↑s / ε)⌉₊ with hl_def
  set t : ℕ := ⌈Real.logb 2 (2 / ε)⌉₊ with ht_def
  have hlogl : 1 ≤ Real.logb 2 (2 * ↑s / ε) :=
    logb_2s_div_eps_pos s hs_pos ε hε_pos hε_le
  have hl_pos : 0 < l := Nat.ceil_pos.mpr (by linarith)
  have hl_ge : Real.logb 2 (2 * ↑s / ε) ≤ (l : ℝ) := Nat.le_ceil _
  have ht_ge : Real.logb 2 (2 / ε) ≤ (t : ℝ) := Nat.le_ceil _
  have hhalf_pos : (0 : ℝ) < 2⁻¹ := by norm_num
  have hhalf_le : (2⁻¹ : ℝ) ≤ 1 := by norm_num
  have hl_bound : (↑s : ℝ) * (1 / 2 : ℝ) ^ l ≤ ε / 2 := by
    have hcast : ((2 : ℝ)⁻¹) ^ ((l : ℕ) : ℝ) = ((1 : ℝ) / 2) ^ l := by
      rw [Real.rpow_natCast]
      norm_num
    have hmono : ((2 : ℝ)⁻¹) ^ ((l : ℕ) : ℝ)
        ≤ (2 : ℝ)⁻¹ ^ Real.logb 2 (2 * ↑s / ε) :=
      Real.rpow_le_rpow_of_exponent_ge hhalf_pos hhalf_le hl_ge
    calc (↑s : ℝ) * (1 / 2 : ℝ) ^ l
        = (↑s : ℝ) * ((2 : ℝ)⁻¹) ^ ((l : ℕ) : ℝ) := by rw [hcast]
      _ ≤ (↑s : ℝ) * (2 : ℝ)⁻¹ ^ Real.logb 2 (2 * ↑s / ε) :=
          mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg s)
      _ ≤ ε / 2 := size_times_two_pow_neg_l_le s hs_pos ε hε_pos
  have ht_bound : (1 / 2 : ℝ) ^ t ≤ ε / 2 := by
    have hcast : ((2 : ℝ)⁻¹) ^ ((t : ℕ) : ℝ) = ((1 : ℝ) / 2) ^ t := by
      rw [Real.rpow_natCast]
      norm_num
    have hmono : ((2 : ℝ)⁻¹) ^ ((t : ℕ) : ℝ)
        ≤ (2 : ℝ)⁻¹ ^ Real.logb 2 (2 / ε) :=
      Real.rpow_le_rpow_of_exponent_ge hhalf_pos hhalf_le ht_ge
    calc (1 / 2 : ℝ) ^ t
        = ((2 : ℝ)⁻¹) ^ ((t : ℕ) : ℝ) := hcast.symm
      _ ≤ (2 : ℝ)⁻¹ ^ Real.logb 2 (2 / ε) := hmono
      _ = ε / 2 := two_pow_neg_logb_2_div_eps ε hε_pos
  exact circuit_fourier_concentration c d s w l t hd hs hw hd2 hs_pos hw_pos
    hl_pos hn ε hε_pos hl_bound ht_bound

end RestrictionFourier
