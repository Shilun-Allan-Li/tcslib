/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PolyExpr
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.HardcoreBit.Basic
import TCSlib.Cryptography.OneWayFunctions.Basic
import TCSlib.Cryptography.Pseudorandom.Functions.Defs
import TCSlib.Cryptography.Pseudorandom.Functions.LazySampling
import Mathlib.Data.Nat.Choose.Bounds

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probability and coin relabelling for PRF encryption

## Main definitions

The lemmas use the existing uniform expectations and finite oracle adversaries.

## Main results

* `MultiMsg.abs_uexp_sub_le_uprob` bounds the difference of two expectations by the
  probability of the event on which the functions can disagree.
* `MultiMsg.card_filter_lt_pairs` counts the pairs of distinct query indices in increasing order.
* `MultiMsg.negligible_choose_div_two_pow` proves negligibility of the collision term.
* `MultiMsg.prfAdv_congr_equiv` transports the PRF advantage along a bijection of coins
  when the two adversaries agree on every oracle.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.7, Definition 93.1, and §3.9, Algorithm 99.1 and Theorem 99.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (oracle adversaries and PRF advantage).
-/

namespace TCSlib.Cryptography.MultiMsg

open Complexity Turing Finset

/-! ### Probability: coupling, pair counting, the collision term -/

/-- The absolute value of an average is at most the average of the absolute values. -/
theorem abs_uexp_le_uexp_abs {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    |uexp f| ≤ uexp fun ω => |f ω| := by
  rw [uexp_def, uexp_def]
  rw [abs_div, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

/-- **The coupling bound**: two `[0,1]`-valued functions on a finite sample space that agree
outside the event `E` have averages at most `Pr[E]` apart (the "two experiments that agree
on an event `E` have advantage `≤ Pr[¬E]`" step of [PS10, Theorem 99.2, proof, `H²` vs `H³`]).

**Proof sketch.** `|E a − E b| = |E (a − b)| ≤ E |a − b|` (`abs_uexp_le_uexp_abs`), and
pointwise `|a − b| ≤ [E]` since the difference vanishes off `E` and is at most `1` on it. -/
theorem abs_uexp_sub_le_uprob {Ω : Type*} [Fintype Ω] (a b : Ω → ℝ) (E : Ω → Prop)
    [DecidablePred E] (ha : ∀ ω, 0 ≤ a ω ∧ a ω ≤ 1) (hb : ∀ ω, 0 ≤ b ω ∧ b ω ≤ 1)
    (heq : ∀ ω, ¬ E ω → a ω = b ω) :
    |uexp a - uexp b| ≤ uprob E := by
  rw [← HardcoreBit.uexp_sub, uprob_eq_uexp]
  refine (abs_uexp_le_uexp_abs _).trans (HardcoreBit.uexp_mono fun ω => ?_)
  by_cases hE : E ω
  · rw [if_pos hE]
    obtain ⟨h1, h2⟩ := ha ω
    obtain ⟨h3, h4⟩ := hb ω
    exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  · rw [if_neg hE, heq ω hE, sub_self, abs_zero]

/-- **Counting the pairs `i < j`**: there are `C(k, 2)` pairs `(i, j)` with `i < j` in
`Fin k × Fin k` (the `C(q(n)+1, 2)` of the birthday bound of [PS10, Theorem 99.2]).

**Proof sketch.** The pairs `i < j` and their swaps partition the off-diagonal of
`Fin k × Fin k`, which has `k² − k` elements (`Finset.offDiag_card`); the swap is injective,
so `2 · #{i < j} = k(k − 1)` and `Nat.choose_two_right` finishes. -/
theorem card_filter_lt_pairs (k : ℕ) :
    ((univ : Finset (Fin k × Fin k)).filter fun p => p.1 < p.2).card = k.choose 2 := by
  set S := (univ : Finset (Fin k × Fin k)).filter fun p => p.1 < p.2 with hS
  have hunion : S ∪ S.image Prod.swap = (univ : Finset (Fin k)).offDiag := by
    ext ⟨i, j⟩
    simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.mem_offDiag, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
    constructor
    · rintro (h | ⟨a, b, hab, rfl, rfl⟩)
      · exact ne_of_lt h
      · exact ne_of_gt hab
    · intro hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl h
      · exact Or.inr ⟨j, i, h, rfl, rfl⟩
  have hdisj : Disjoint S (S.image Prod.swap) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ hij hji
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hij
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.exists,
      Prod.swap_prod_mk, Prod.mk.injEq] at hji
    obtain ⟨a, b, hab, rfl, rfl⟩ := hji
    exact absurd hij (not_lt.2 hab.le)
  have hcard := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ Prod.swap_injective,
    Finset.offDiag_card, Finset.card_univ, Fintype.card_fin] at hcard
  rw [Nat.choose_two_right, Nat.mul_sub_one]
  omega

/-- Two independent uniform elements of a nonempty finite type coincide with probability
`1 / |α|` (Fubini and `OneWay.uprob_eq_one_div_card`). -/
theorem uprob_eq_pair {α : Type*} [Fintype α] [Nonempty α] :
    uprob (fun z : α × α => z.1 = z.2) = 1 / Fintype.card α := by
  rw [uprob_prod]
  have h : ∀ a : α, uprob (fun b : α => a = b) = 1 / Fintype.card α := by
    intro a
    rw [← OneWay.uprob_eq_one_div_card a]
    exact uprob_congr fun b => eq_comm
  simp_rw [h]
  exact HardcoreBit.uexp_const _

/-- **The collision term is negligible**: `n ↦ C(q(n)+1, 2) / 2^n` is negligible for every
syntactic polynomial `q` ([PS10, Theorem 99.2, proof: the collision probability is
negligible]).

**Proof sketch.** `C(k, 2) ≤ k²` (`Nat.choose_le_pow`) and `q(n) + 1 ≤ (C+1)(n+1)^c ≤
(C+1) 2^c n^c` for `n ≥ 1` (`PolyExpr.eval_le`), so the term is at most a constant times
`n^{2c} · 2^{−n}`, negligible by `negligible_two_pow_neg`, `Negligible.mul_pow` and
`Negligible.const_mul`; conclude with `Negligible.mono`. -/
theorem negligible_choose_div_two_pow (q : PolyExpr) :
    Negligible fun n => (Nat.choose (q.eval n + 1) 2 : ℝ) / 2 ^ n := by
  obtain ⟨C, c, hC⟩ := q.eval_le
  have hν : Negligible fun n =>
      ((((C + 1) * 2 ^ c) ^ 2 : ℕ) : ℝ) * ((n : ℝ) ^ (2 * c) * (2 : ℝ)⁻¹ ^ n) :=
    (negligible_two_pow_neg.mul_pow (2 * c)).const_mul _
  refine hν.mono ⟨1, fun n hn => ?_⟩
  have hnat : Nat.choose (q.eval n + 1) 2 ≤ ((C + 1) * 2 ^ c) ^ 2 * n ^ (2 * c) := by
    have h1 : q.eval n + 1 ≤ (C + 1) * (n + 1) ^ c := by
      have := hC n
      have hp : 1 ≤ (n + 1) ^ c := Nat.one_le_pow _ _ (Nat.succ_pos n)
      nlinarith
    have h2 : (n + 1) ^ c ≤ (2 * n) ^ c := Nat.pow_le_pow_left (by omega) c
    calc Nat.choose (q.eval n + 1) 2 ≤ (q.eval n + 1) ^ 2 := Nat.choose_le_pow _ _
      _ ≤ ((C + 1) * (2 * n) ^ c) ^ 2 :=
          Nat.pow_le_pow_left (h1.trans (Nat.mul_le_mul_left _ h2)) 2
      _ = ((C + 1) * 2 ^ c) ^ 2 * n ^ (2 * c) := by ring
  have hR : (Nat.choose (q.eval n + 1) 2 : ℝ) ≤
      ((((C + 1) * 2 ^ c) ^ 2 : ℕ) : ℝ) * (n : ℝ) ^ (2 * c) := by
    exact_mod_cast hnat
  have hinv : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity), div_eq_mul_inv, ← inv_pow]
  calc (Nat.choose (q.eval n + 1) 2 : ℝ) * (2 : ℝ)⁻¹ ^ n
      ≤ ((((C + 1) * 2 ^ c) ^ 2 : ℕ) : ℝ) * (n : ℝ) ^ (2 * c) * (2 : ℝ)⁻¹ ^ n :=
        mul_le_mul_of_nonneg_right hR hinv
    _ = _ := by ring

/-! ### Oracle adversaries: coin relabelling -/

/-- Relabelling the coins of an oracle adversary by a bijection preserves its acceptance
probability against every oracle sampler, provided the two trees agree on every oracle. -/
theorem acceptProb_oracleDist_congr_equiv {σ : Type*} {I O : Type} {ρ ρ' : Type*} [Fintype σ] [Fintype ρ]
    [Fintype ρ'] (X : σ → I → O) (A : OracleAdversary ρ I O) (A' : OracleAdversary ρ' I O)
    (φ : ρ' ≃ ρ) (h : ∀ (g : I → O) (w : ρ'), (A (φ w)).eval g = (A' w).eval g) :
    acceptProb X (oracleDist A) = acceptProb X (oracleDist A') := by
  simp only [acceptProb_def, oracleDist_apply]
  rw [← uprob_comp_equiv ((Equiv.refl σ).prodCongr φ)]
  congr 1
  funext z
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply, h]

/-- **Coin relabelling preserves the PRF advantage**: oracle adversaries whose trees agree on
every oracle after a bijective relabelling of the coins have the same `prfAdv`. -/
theorem prfAdv_congr_equiv {K : Type*} {I O : Type} {ρ ρ' : Type*} [Fintype K] [Fintype I] [DecidableEq I]
    [Fintype O] [Fintype ρ] [Fintype ρ'] (F : K → I → O) (A : OracleAdversary ρ I O)
    (A' : OracleAdversary ρ' I O) (φ : ρ' ≃ ρ)
    (h : ∀ (g : I → O) (w : ρ'), (A (φ w)).eval g = (A' w).eval g) :
    prfAdv F A = prfAdv F A' := by
  have hF := acceptProb_oracleDist_congr_equiv F A A' φ h
  have hR := acceptProb_oracleDist_congr_equiv (id : (I → O) → I → O) A A' φ h
  simp only [acceptProb_def, oracleDist_apply, id_eq] at hF hR
  rw [prfAdv_eq, prfAdv_eq, hF, hR]

end TCSlib.Cryptography.MultiMsg
