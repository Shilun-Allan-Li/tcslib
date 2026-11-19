/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.CoinSampling.Buckets
import TCSlib.Cryptography.Asymptotic.ReductionSupport
import TCSlib.Cryptography.Foundations.Subexponential

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Summed failure of coin draws: negligible and subexponentially small

A bucket draw of a modulus `N ≤ 2^b` with `b + t` coins fails with probability at most `2^{-t}`
(`fail_bucket_le`). A game making at most `q(κ)` such draws, with `t(κ)` slack bits each, is
therefore `drawSlack q t κ = q(κ) · 2^{-t(κ)}`-close to its exact version (`Close.bind`,
`Close.simulate`). With `t(κ) ≥ κ` (the default: `s = b + κ` coins per draw) this slack is
negligible, and subexponentially small with every exponent `c < 1`.

## Main definitions

* `CoinSampling.drawSlack q t`: `κ ↦ q(κ) · 2^{-t(κ)}`.

## Main results

* `CoinSampling.negligible_drawSlack`: `Negligible (drawSlack q t)` for `t(κ) ≥ κ`.
* `CoinSampling.subexpSmall_polyExpr_mul`: a polynomial times a `SubexpSmall c` function is
  `SubexpSmall c'` for every `c' < c`.
* `CoinSampling.subexpSmall_drawSlack`: `SubexpSmall c (drawSlack q t)` for `0 < c < 1`.
* `CoinSampling.fail_bucket_schedule_le`: the per-draw bound along a modulus schedule.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from Well-Founded
  Assumptions*, J. ACM 73(1), Article 1, 2026, Definition 2.1 (subexponential
  indistinguishability, `ε(λ) = 2^{-λ^c}`).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, §1.2 (negligible functions and their closure under polynomial factors).

**Disclosed overlap.** The majorant `p(n) ≤ C · 2^d · n^d` for `n ≥ 1`
(`polyExpr_eval_le_mul_pow`) is the same estimate as the inline step of
`Negligible.polyExpr_mul` (`Asymptotic/ReductionSupport.lean`), published here as a lemma so
that the subexponential analogue can use it; the negligible case reuses
`Negligible.polyExpr_mul` itself.
-/

namespace TCSlib.Cryptography.CoinSampling

open Complexity

/-- **The normal-form majorant of a syntactic polynomial**: there are `C, d` with
`p(n) ≤ C · 2^d · n^d` for every `n ≥ 1` (`PolyExpr.eval_le` and `(n + 1)^d ≤ (2n)^d`). Glue;
disclosed overlap with the inline step of `Negligible.polyExpr_mul`. -/
theorem polyExpr_eval_le_mul_pow (p : PolyExpr) :
    ∃ C d : ℕ, ∀ n : ℕ, 1 ≤ n → (p.eval n : ℝ) ≤ (C : ℝ) * 2 ^ d * (n : ℝ) ^ d := by
  obtain ⟨C, d, hC⟩ := p.eval_le
  refine ⟨C, d, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (p.eval n : ℝ) ≤ C * ((n : ℝ) + 1) ^ d := by exact_mod_cast hC n
  have h2 : ((n : ℝ) + 1) ^ d ≤ (2 * (n : ℝ)) ^ d :=
    pow_le_pow_left₀ (by positivity) (by linarith) d
  calc (p.eval n : ℝ) ≤ C * ((n : ℝ) + 1) ^ d := h1
    _ ≤ C * (2 * (n : ℝ)) ^ d := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
    _ = (C : ℝ) * 2 ^ d * (n : ℝ) ^ d := by rw [_root_.mul_pow, mul_assoc]

/-- **A polynomial times a subexponentially small function** is subexponentially small with
every smaller exponent: `SubexpSmall c μ`, `0 < c`, `c' < c` give
`SubexpSmall c' (n ↦ p(n) · μ n)` [JLS26, Definition 2.1] (the closure that lets a polynomial
number of losses be absorbed).

**Proof sketch.** With the majorant `p(n) ≤ C 2^d n^d` (`polyExpr_eval_le_mul_pow`), pass through
the intermediate exponent `c'' = (c + max c' 0)/2`: `n^d μ` is `SubexpSmall c''`
(`SubexpSmall.mul_pow`), the constant multiple is `SubexpSmall c'` (`SubexpSmall.const_mul`),
and it dominates `|p(n) μ n|` for `n ≥ 1` (`SubexpSmall.mono`). -/
theorem subexpSmall_polyExpr_mul {c c' : ℝ} {μ : ℕ → ℝ} (hμ : SubexpSmall c μ) (hc : 0 < c)
    (h : c' < c) (p : PolyExpr) : SubexpSmall c' fun n => (p.eval n : ℝ) * μ n := by
  obtain ⟨C, d, hp⟩ := polyExpr_eval_le_mul_pow p
  have hm0 : 0 ≤ max c' 0 := le_max_right _ _
  have hm1 : c' ≤ max c' 0 := le_max_left _ _
  have hmc : max c' 0 < c := max_lt h hc
  have h1 := (hμ.mul_pow hc (show (c + max c' 0) / 2 < c by linarith) d).const_mul
    (by linarith) (show c' < (c + max c' 0) / 2 by linarith) ((C : ℝ) * 2 ^ d)
  refine h1.mono ⟨1, fun n hn => ?_⟩
  have hpn := hp n hn
  calc |(p.eval n : ℝ) * μ n| = (p.eval n : ℝ) * |μ n| := by rw [abs_mul, Nat.abs_cast]
    _ ≤ (C : ℝ) * 2 ^ d * (n : ℝ) ^ d * |μ n| := mul_le_mul_of_nonneg_right hpn (abs_nonneg _)
    _ = |(C : ℝ) * 2 ^ d * ((n : ℝ) ^ d * μ n)| := by
        rw [abs_mul ((C : ℝ) * 2 ^ d) ((n : ℝ) ^ d * μ n), abs_mul ((n : ℝ) ^ d) (μ n),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (C : ℝ) * 2 ^ d),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ d), mul_assoc]

/-- **The slack of `q(κ)` coin draws with `t(κ)` slack bits each**: `q(κ) · 2^{-t(κ)}`. By
`fail_bucket_le`, a bucket draw of a modulus `N ≤ 2^b` with `b + t` coins costs at most
`2^{-t}`, so the summed failure bound of a game making at most `q(κ)` draws is
`drawSlack q t κ`. Glue. -/
noncomputable def drawSlack (q t : PolyExpr) (κ : ℕ) : ℝ :=
  (q.eval κ : ℝ) * (2 : ℝ)⁻¹ ^ t.eval κ

/-- `drawSlack q t κ = q(κ) · (2⁻¹)^{t(κ)}`. -/
theorem drawSlack_eq (q t : PolyExpr) (κ : ℕ) :
    drawSlack q t κ = (q.eval κ : ℝ) * (2 : ℝ)⁻¹ ^ t.eval κ := rfl

/-- `2^{-t(κ)} ≤ 2^{-κ}` when `κ ≤ t(κ)`, in absolute values. Glue. -/
theorem abs_two_inv_pow_le {t : PolyExpr} (ht : ∀ κ, κ ≤ t.eval κ) (κ : ℕ) :
    |(2 : ℝ)⁻¹ ^ t.eval κ| ≤ |(2 : ℝ)⁻¹ ^ κ| := by
  rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (ht κ)

/-- **The slack is negligible** when `t(κ) ≥ κ` [Gar26, §1.2]: `negligible_two_pow_neg`, moved
to `t` by monotonicity (`Negligible.mono`), times the polynomial `q`
(`Negligible.polyExpr_mul`). -/
theorem negligible_drawSlack (q t : PolyExpr) (ht : ∀ κ, κ ≤ t.eval κ) :
    Negligible (drawSlack q t) :=
  (negligible_two_pow_neg.mono ⟨0, fun κ _ => abs_two_inv_pow_le ht κ⟩).polyExpr_mul q

/-- **The slack is subexponentially small** for every exponent `0 < c < 1` when `t(κ) ≥ κ`
[JLS26, Definition 2.1]: `subexpSmall_two_pow_neg` (exponent `1`), moved to `t`
(`SubexpSmall.mono`), times the polynomial `q` (`subexpSmall_polyExpr_mul`, which lowers the
exponent strictly). (`0 < c` is not needed by the proof; it is the source's requirement.) -/
theorem subexpSmall_drawSlack (q t : PolyExpr) (ht : ∀ κ, κ ≤ t.eval κ) {c : ℝ} (_hc0 : 0 < c)
    (hc1 : c < 1) : SubexpSmall c (drawSlack q t) :=
  subexpSmall_polyExpr_mul (subexpSmall_two_pow_neg.mono ⟨0, fun κ _ => abs_two_inv_pow_le ht κ⟩)
    one_pos hc1 q

/-- **Per-draw bound along a modulus schedule**: if `0 < N(κ) ≤ 2^{b(κ)}`, the bucket sampler
with `b(κ) + t(κ)` coins fails with probability at most `2^{-t(κ)}` (`fail_bucket_le`). The
modulus is a value here (a law parameter), not a hard-wired program constant: the program reads
it from its input (`bucketSampler`, `CoinSampling.Efficiency`). Glue. -/
theorem fail_bucket_schedule_le (N : ℕ → ℕ) (b t : PolyExpr) (hN0 : ∀ κ, 0 < N κ)
    (hN : ∀ κ, N κ ≤ 2 ^ b.eval κ) (κ : ℕ) :
    (bucket (N κ) ((b.add t).eval κ)).fail ≤ (2 : ℝ)⁻¹ ^ t.eval κ := by
  rw [PolyExpr.eval_add]
  exact fail_bucket_le (hN0 κ) (hN κ) (t.eval κ)

/-- **The summed slack of a schedule of draws**: if each of the at most `q(κ)` draws of a game
fails with probability at most `2^{-t(κ)}`, their summed failure is at most `drawSlack q t κ`.
Glue: the arithmetic `m · f ≤ q(κ) · 2^{-t(κ)}` for `m ≤ q(κ)` and `0 ≤ f ≤ 2^{-t(κ)}`, the shape
in which `Close.simulate` (`m · fail`) meets the asymptotic lemmas. -/
theorem mul_fail_le_drawSlack (q t : PolyExpr) (κ m : ℕ) (hm : m ≤ q.eval κ) {f : ℝ}
    (hf0 : 0 ≤ f) (hf : f ≤ (2 : ℝ)⁻¹ ^ t.eval κ) : (m : ℝ) * f ≤ drawSlack q t κ := by
  rw [drawSlack_eq]
  exact mul_le_mul (by exact_mod_cast hm) hf hf0 (Nat.cast_nonneg _)

end TCSlib.Cryptography.CoinSampling
