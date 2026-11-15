/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Foundations.Experiments
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Complexity.Randomized.PolyExpr

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probability tools for the composition theorem

The distinguishing-advantage manipulations of the proof of [Gol04, §7.3.1, Theorem 7.3.3]
(`HybridProtocol.hbcSecure_compose`), on uniform seeds and coins (`acceptProb`, `distAdv`):
* the statistical switch: two samplers on one seed space that agree off a bad event are within
  the bad event's probability;
* fixing coordinates: the advantage between two samplers on `σ × τ` is at most the advantage of
  their sections at the worst `a : σ` (the advice of a non-uniform reduction);
* a negligible function times a polynomial is negligible.

Unused seed coordinates are dropped by the published `acceptProb_fst`, `acceptProb_snd`
(`Pseudorandom/Indistinguishability.lean`).

## Main results

* `ComposeProb.abs_uprob_sub_le`, `ComposeProb.distAdv_le_uprob_of_eq`,
  `ComposeProb.exists_abs_sub_le_sections`, `ComposeProb.negligible_polyExpr_mul`.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, §1.2 (negligible functions) and §3.2 (hybrid arguments).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeProb

open Finset Complexity

variable {σ τ υ γ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype υ] [Fintype ρ]

/-- Two events that agree off a third: `|Pr[A] − Pr[B]| ≤ Pr[C]` when `A ↔ B` outside `C`. -/
theorem abs_uprob_sub_le {A B C : υ → Prop} (h : ∀ u, ¬ C u → (A u ↔ B u)) :
    |uprob A - uprob B| ≤ uprob C := by
  have h1 : uprob A ≤ uprob B + uprob C :=
    (uprob_mono fun u ha => by
      by_cases hc : C u
      · exact Or.inr hc
      · exact Or.inl ((h u hc).1 ha)).trans (uprob_or_le B C)
  have h2 : uprob B ≤ uprob A + uprob C :=
    (uprob_mono fun u hb => by
      by_cases hc : C u
      · exact Or.inr hc
      · exact Or.inl ((h u hc).2 hb)).trans (uprob_or_le A C)
  rw [abs_le]
  constructor <;> linarith

/-- **The statistical switch** ("agree off a bad event"): if the samplers `X`, `Y` on one seed
space agree at every seed outside `bad`, then `distAdv X Y D ≤ Pr_s[bad s]`.

**Proof sketch.** The acceptance events on `σ × ρ` agree outside `bad ∘ fst`
(`abs_uprob_sub_le`), whose probability is `Pr[bad]` (`uprob_fst`). -/
theorem distAdv_le_uprob_of_eq [Nonempty ρ] (X Y : σ → γ) (D : γ → ρ → Bool) (bad : σ → Prop)
    (h : ∀ s, ¬ bad s → X s = Y s) : distAdv X Y D ≤ uprob bad := by
  rw [distAdv_def, acceptProb_def, acceptProb_def, ← uprob_fst (β := ρ) bad]
  exact abs_uprob_sub_le fun z hz => by rw [h z.1 hz]

/-- **Acceptance as an average of sections**: `acceptProb X D` is the average over `a : σ` of
the acceptance probability of the section `t ↦ X (a, t)` (`uprob_prod` after reassociating).
`acceptProb X D = uexp fun a => acceptProb (fun t => X (a, t)) D`. -/
theorem acceptProb_eq_uexp_sections (X : σ × τ → γ) (D : γ → ρ → Bool) :
    acceptProb X D = uexp fun a => acceptProb (fun t => X (a, t)) D := by
  rw [acceptProb_def, ← uprob_comp_equiv (Equiv.prodAssoc σ τ ρ).symm, uprob_prod]
  simp only [acceptProb_def]
  rfl

/-- The average of a difference is at most the largest difference: some `a` has
`|uexp f − uexp g| ≤ |f a − g a|` (for nonempty `σ`). -/
theorem exists_abs_uexp_sub_le [Nonempty σ] (f g : σ → ℝ) :
    ∃ a, |uexp f - uexp g| ≤ |f a - g a| := by
  obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ (fun a => |f a - g a|)
    Finset.univ_nonempty
  refine ⟨a, ?_⟩
  have hc : (0 : ℝ) < Fintype.card σ := Nat.cast_pos.2 Fintype.card_pos
  rw [uexp_def, uexp_def, ← sub_div, abs_div, abs_of_pos hc, div_le_iff₀ hc, ← sum_sub_distrib]
  calc |∑ i, (f i - g i)| ≤ ∑ i, |f i - g i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : σ, |f a - g a| := sum_le_sum fun i _ => ha i (mem_univ i)
    _ = |f a - g a| * Fintype.card σ := by rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]

/-- **Fixing coordinates** (the advice of a non-uniform reduction): for samplers `X`, `Y` on
`σ × τ` there is `a : σ` with `|acceptProb X D − acceptProb Y D| ≤
|acceptProb (X (a, ·)) D − acceptProb (Y (a, ·)) D|` (`acceptProb_eq_uexp_sections`,
`exists_abs_uexp_sub_le`). -/
theorem exists_abs_sub_le_sections [Nonempty σ] (X Y : σ × τ → γ) (D : γ → ρ → Bool) :
    ∃ a, |acceptProb X D - acceptProb Y D| ≤
      |acceptProb (fun t => X (a, t)) D - acceptProb (fun t => Y (a, t)) D| := by
  rw [acceptProb_eq_uexp_sections X, acceptProb_eq_uexp_sections Y]
  exact exists_abs_uexp_sub_le _ _

/-- **A negligible function times a polynomial is negligible**: for `p : PolyExpr`,
`n ↦ p(n) · μ(n)` is negligible.
`Negligible fun n => (p.eval n : ℝ) * μ n`.

**Proof sketch.** `p(n) ≤ C (n + 1)^c ≤ C 2^c n^c` for `n ≥ 1` (`PolyExpr.eval_le`), and
`n ↦ (C 2^c) (n^c μ(n))` is negligible (`Negligible.mul_pow`, `Negligible.const_mul`). -/
theorem negligible_polyExpr_mul {μ : ℕ → ℝ} (hμ : Negligible μ) (p : PolyExpr) :
    Negligible fun n => (p.eval n : ℝ) * μ n := by
  obtain ⟨C, c, hC⟩ := p.eval_le
  refine ((hμ.mul_pow c).const_mul ((C : ℝ) * 2 ^ c)).mono ⟨1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (p.eval n : ℝ) ≤ C * 2 ^ c * (n : ℝ) ^ c := by
    have h1 : (p.eval n : ℝ) ≤ C * ((n : ℝ) + 1) ^ c := by exact_mod_cast hC n
    have h2 : ((n : ℝ) + 1) ^ c ≤ (2 * (n : ℝ)) ^ c :=
      pow_le_pow_left₀ (by positivity) (by linarith) c
    rw [mul_pow] at h2
    nlinarith [show (0 : ℝ) ≤ C from Nat.cast_nonneg C]
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (p.eval n)),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ C * 2 ^ c), abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ c), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)

end TCSlib.Cryptography.SecureComputation.ComposeProb
