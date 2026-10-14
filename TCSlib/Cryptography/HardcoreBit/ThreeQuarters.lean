/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.HardcoreBit.InnerProduct
import TCSlib.Cryptography.HardcoreBit.PairwiseIndependence

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Goldreich–Levin: the simple case (prediction at least `3/4 + ε`)

[Gar26, Theorem 2.3, simple case]: if `A` predicts `⟨x, r⟩` from `f(x) ‖ r` with
probability at least `3/4 + ε`, the inverter of [Gar26, Figure 2.4] inverts
`g(x, r) = f(x) ‖ r` with probability at least `ε / 4`. For each bit `i` it runs `T`
independent trials `A(f(x) ‖ s) ⊕ A(f(x) ‖ s ⊕ eᵢ)` with fresh `s` and fresh coins, and
takes the majority.

The number of trials `T` is an explicit parameter with the hypothesis `n ≤ 2 ε² T`,
which is what the source's choice `T = n / (2 ε²)` is used for (each majority then fails
with probability at most `1/(2n)`).

## Main definitions

* `trialBit A y i w`: one trial `A(y ‖ s) ⊕ A(y ‖ s ⊕ eᵢ)` with `w = (s, coins, coins)`.
* `majorityRecover A T`, `majorityInverter A T`: the inverter of [Gar26, Figure 2.4].

## Main results

* `trialBit_correct`: for a good `x`, a trial is right with probability `≥ 1/2 + ε`.
* `uprob_majorityRecover_ne_le`: for a good `x`, each majority is wrong with probability
  at most `1 / (4 ε² T)`.
* `invProb_majorityInverter`: [Gar26, Theorem 2.3, simple case].

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5.1, Theorem 2.3 (simple case) and Figure 2.4.
-/

namespace TCSlib.Cryptography.HardcoreBit

open Finset TCSlib.Cryptography

variable {n : ℕ} {β ρ : Type*} [Fintype ρ]

/-- One trial of [Gar26, Figure 2.4] for bit `i`: with `w = (s, c₁, c₂)` it is
`A(y ‖ s; c₁) ⊕ A(y ‖ s ⊕ eᵢ; c₂)`, two calls to `A` with fresh coins, one XOR of
strings and one XOR of bits. -/
def trialBit (A : β × (Fin n → Bool) → ρ → Bool) (y : β) (i : Fin n)
    (w : (Fin n → Bool) × ρ × ρ) : Bool :=
  A (y, w.1) w.2.1 + A (y, w.1 + Pi.single i true) w.2.2

/-- The recovery procedure of [Gar26, Figure 2.4]: bit `i` is the majority of `T` trials
`trialBit A y i (c i t)`, each with its own fresh `s` and coins. In total it makes `2 n T`
calls to `A`, samples `n T` strings of `n` bits and `2 n T` coin strings, and computes
`n T` string XORs, `n T` bit XORs and `n` majorities of `T` bits. -/
def majorityRecover (A : β × (Fin n → Bool) → ρ → Bool) (T : ℕ) (y : β)
    (c : Fin n → Fin T → (Fin n → Bool) × ρ × ρ) : Fin n → Bool :=
  fun i => majority fun t => trialBit A y i (c i t)

/-- The inverter of [Gar26, Figure 2.4]: on `f(x) ‖ r` it outputs
`majorityRecover A T (f(x)) ‖ r`. -/
def majorityInverter (A : β × (Fin n → Bool) → ρ → Bool) (T : ℕ) :
    β × (Fin n → Bool) → (Fin n → Fin T → (Fin n → Bool) × ρ × ρ) →
      (Fin n → Bool) × (Fin n → Bool) :=
  glInverter (majorityRecover A T)

/-- For a good `x`, one with `secProb f A x ≥ 3/4 + ε/2`, a single trial outputs `xᵢ` with
probability at least `1/2 + ε`. [Gar26, §2.5.1, simple case], the single-iteration bound.

**Proof sketch.** If both calls are right the trial gives
`⟨x, s⟩ ⊕ ⟨x, s ⊕ eᵢ⟩ = ⟨x, eᵢ⟩ = xᵢ`. The first query `s` and the second `s ⊕ eᵢ` are
each uniform with fresh coins, so each call is wrong with probability at most
`1/4 - ε/2`; by the union bound both are right with probability at least `1/2 + ε`. -/
theorem trialBit_correct [Nonempty ρ] (f : (Fin n → Bool) → β)
    (A : β × (Fin n → Bool) → ρ → Bool) (x : Fin n → Bool) (i : Fin n) {ε : ℝ}
    (hx : 3 / 4 + ε / 2 ≤ secProb f A x) :
    1 / 2 + ε ≤ uprob (fun w : (Fin n → Bool) × ρ × ρ => trialBit A (f x) i w = x i) := by
  -- each call is right with probability `secProb f A x`
  have h1 : uprob (fun w : (Fin n → Bool) × ρ × ρ => A (f x, w.1) w.2.1 = ip x w.1) =
      secProb f A x :=
    ((pushesUniform_id (Ω := Fin n → Bool)).prodMap
      (pushesUniform_fst (α := ρ) (β := ρ))).uprob_eq
      (fun z : (Fin n → Bool) × ρ => A (f x, z.1) z.2 = ip x z.1)
  have h2 : uprob (fun w : (Fin n → Bool) × ρ × ρ =>
      A (f x, w.1 + Pi.single i true) w.2.2 = ip x (w.1 + Pi.single i true)) =
      secProb f A x :=
    ((pushesUniform_xor (Pi.single i true)).prodMap
      (pushesUniform_snd (α := ρ) (β := ρ))).uprob_eq
      (fun z : (Fin n → Bool) × ρ => A (f x, z.1) z.2 = ip x z.1)
  -- both calls right implies the trial is right
  have hboth : ∀ w : (Fin n → Bool) × ρ × ρ, A (f x, w.1) w.2.1 = ip x w.1 →
      A (f x, w.1 + Pi.single i true) w.2.2 = ip x (w.1 + Pi.single i true) →
      trialBit A (f x) i w = x i := by
    intro w hw1 hw2
    simp only [trialBit]
    rw [hw1, hw2, ip_add, ip_single]
    cases ip x w.1 <;> cases x i <;> rfl
  -- union bound on the two failure events
  have hfail : uprob (fun w : (Fin n → Bool) × ρ × ρ => ¬ trialBit A (f x) i w = x i) ≤
      uprob (fun w : (Fin n → Bool) × ρ × ρ => ¬ A (f x, w.1) w.2.1 = ip x w.1) +
      uprob (fun w : (Fin n → Bool) × ρ × ρ =>
        ¬ A (f x, w.1 + Pi.single i true) w.2.2 = ip x (w.1 + Pi.single i true)) := by
    refine le_trans (uprob_mono fun w hw => ?_) (uprob_or_le _ _)
    by_contra h
    push_neg at h
    exact hw (hboth w h.1 h.2)
  rw [uprob_not, uprob_not, uprob_not, h1, h2] at hfail
  linarith

/-- For a good `x` (`secProb f A x ≥ 3/4 + ε/2`, `ε > 0`) and `T ≥ 1`, the majority for
bit `i` is wrong with probability at most `1 / (4 ε² T)`. [Gar26, §2.5.1, simple case],
the bound `Pr[x'ᵢ ≠ xᵢ] ≤ 1/(4 ε(n)² T)`.

**Proof sketch.** The trials for bit `i` are functions of the coordinates `c i t` of a
uniform tuple, hence pairwise independent (the source uses full independence; pairwise
suffices), and each is right with probability at least `1/2 + ε`. A wrong majority means
at most half the trials are right, which Chebyshev bounds by `1/(4 ε² T)`. -/
theorem uprob_majorityRecover_ne_le [Nonempty ρ] (f : (Fin n → Bool) → β)
    (A : β × (Fin n → Bool) → ρ → Bool) {T : ℕ} (hT : 0 < T) (x : Fin n → Bool)
    (i : Fin n) {ε : ℝ} (hε : 0 < ε) (hx : 3 / 4 + ε / 2 ≤ secProb f A x) :
    uprob (fun c : Fin n → Fin T → (Fin n → Bool) × ρ × ρ =>
      majorityRecover A T (f x) c i ≠ x i) ≤ 1 / (4 * ε ^ 2 * T) := by
  have hpu : PairwiseUniform (fun (t : Fin T) (c : Fin n → Fin T → (Fin n → Bool) × ρ × ρ) =>
      c i t) :=
    pairwiseUniform_eval.comp_right (pushesUniform_eval i)
  have hY := hpu.pairwiseIndep (fun _ w => decide (trialBit A (f x) i w = x i))
  have hp : ∀ t : Fin T, 1 / 2 + ε ≤ uprob (fun c : Fin n → Fin T → (Fin n → Bool) × ρ × ρ =>
      decide (trialBit A (f x) i (c i t) = x i) = true) := by
    intro t
    have := (hpu.marginal t).uprob_eq (fun w => decide (trialBit A (f x) i w = x i) = true)
    rw [this]
    simpa only [decide_eq_true_eq] using trialBit_correct f A x i hx
  have hb := uprob_majority_fails_le hY hε (by simpa using hT) hp
  simp only [Fintype.card_fin] at hb
  refine le_trans (uprob_mono fun c hc => ?_) hb
  have := two_mul_card_le_of_majority_ne _ _ hc
  simpa only [decide_eq_true_eq, Fintype.card_fin] using this

/-- The simple case of Goldreich–Levin: if `A` predicts `B(x, r) = ⟨x, r⟩` from
`g(x, r) = f(x) ‖ r` with probability at least `3/4 + ε`, `ε > 0`, and the number of
trials satisfies `n ≤ 2 ε² T`, then `majorityInverter A T` inverts `g` with probability
at least `ε / 4`. [Gar26, Theorem 2.3, simple case], with `T = n / (2 ε²)` replaced by
the hypothesis `n ≤ 2 ε² T` on an explicit natural number `T`.

**Proof sketch.** The good set `G = {x | Pr_r[E] ≥ 3/4 + ε/2}` has probability at least
`ε / 2`. For `x ∈ G`, each of the `n` majorities is wrong with probability at most
`1/(4 ε² T) ≤ 1/(2n)`, so by the union bound all bits are right with probability at least
`1/2`. Hence the inverter succeeds with probability at least `ε/2 · 1/2`. -/
theorem invProb_majorityInverter [Nonempty ρ] (f : (Fin n → Bool) → β)
    (A : β × (Fin n → Bool) → ρ → Bool) {T : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hT : (n : ℝ) ≤ 2 * ε ^ 2 * T) (h : 3 / 4 + ε ≤ predProb (glPad f) glBit A) :
    ε / 4 ≤ invProb (glPad f) (majorityInverter A T) := by
  have hG := half_le_uprob_good f A (by norm_num) hε.le h
  have key := le_invProb_of_good f (majorityRecover A T) hG (by norm_num : (0 : ℝ) ≤ 1 / 2)
    fun x hx => by
      refine le_trans ?_ (one_sub_sum_le_uprob_eq (fun c => majorityRecover A T (f x) c) x)
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; norm_num
      have hT0 : 0 < T := by
        rcases Nat.eq_zero_or_pos T with h0 | h0
        · subst h0
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn
          simp only [Nat.cast_zero, mul_zero] at hT
          linarith
        · exact h0
      have hsum : ∑ i : Fin n, uprob (fun c : Fin n → Fin T → (Fin n → Bool) × ρ × ρ =>
          majorityRecover A T (f x) c i ≠ x i) ≤ ∑ _i : Fin n, 1 / (4 * ε ^ 2 * T) :=
        sum_le_sum fun i _ => uprob_majorityRecover_ne_le f A hT0 x i hε hx
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
      have hT' : (0 : ℝ) < T := by exact_mod_cast hT0
      have : (n : ℝ) * (1 / (4 * ε ^ 2 * T)) ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ (by positivity)]
        linarith
      linarith
  unfold majorityInverter
  linarith

end TCSlib.Cryptography.HardcoreBit
