/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.SpaceAmplifyRun
import TCSlib.Complexity.Randomized.PTMEquiv
import Mathlib.Algebra.Order.Archimedean.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The constant `2/3` in `BPTIME(T(n))` is arbitrary

[AB09, §7.1, p. 125]: "the constant 2/3 is arbitrary in the sense that it can be replaced with
any other constant greater than half without changing the classes `BPTIME(T(n))` and `BPP`".
The `BPP` half is `Randomized.BPP_PTMWith_const_eq_BPP_PTM`; this file proves the
`BPTIME(T(n))` half. The machine is the repetition machine `Randomized.Amplify.amp` of
[AB09, §7.7] (`r + 1` runs of `N` on fresh blocks of work tapes, rewinding the input head
between runs, majority vote in the finite control). Its existing analysis bounds a rewind by
`|x| + 2` steps; here a rewind is bounded by the input-head position, which a run of `t` steps
keeps at most `t + 1` (`Randomized.Amplify.halts_comp_pos`), so `2n + 1` runs take `O(n · t)`
steps with no condition on `T`.

## Main definitions

* `Randomized.BPTIMEWith` — `BPTIME(T)` with success threshold `ρ` in place of `2/3`.

## Main results

* `Randomized.Amplify.amp_haltsWithin_pos` — the repetition machine halts within
  `t + r (2t + 3) + 1`.
* `Turing.FinNDTM.BPDecidesInTimeWith.amp` — majority of `2n + 1` runs: success `1/2 + ε`
  becomes `1 - 2 (1 - 4ε²)^n`, in time `t + 2n (2t + 3) + 1`.
* `Randomized.BPTIMEWith_eq_BPTIME` — for every constant `ρ ∈ (1/2, 1)`,
  `BPTIMEWith ρ T = BPTIME T`, for every `T`. [AB09, p. 125]

## Divergences

* The book makes the claim precise only for `BPP` (§7.4.1). For `BPTIME(T(n))` no hypothesis
  on `T` (time-constructibility, `T(n) ≥ n`) is needed: the repetition reruns `N` under its
  own halting, and a decider in time `c · T` forces `c · T(n) ≥ 1`.
* `ρ < 1` is required: `ρ > 1` gives the empty class, and `ρ = 1` demands zero error, which
  majority votes cannot reach. The threshold `ρ` ranges over `ℚ` rather than `ℝ`; this is
  class-preserving, since every real `ρ ∈ (1/2, 1)` lies between two rationals in `(1/2, 1)`
  and the class is antitone in `ρ`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized.Amplify

open Turing

/-! ### Halting of the repetition machine -/

variable {N : FinNDTM Bool} {r : ℕ} {dec : ℕ → Bool} {x : List Bool} {t : ℕ}

/-- From a rewinding configuration after run `j`, with `i = r - j` runs left and the input head
at most `t + 1`, every branch halts within `i (2t + 3) + 1` steps.

**Proof sketch.** As `Randomized.Amplify.rewind_halts`, but the rewind takes `p + 2 ≤ t + 3`
steps (`rewind_run_pos`, `Turing.FinTM.moveInputPos_neg_val`), and `halts_comp_pos` passes the
bound `t + 1` on the input head of a halted run of length at most `t` started at cell `1`. -/
theorem rewind_halts_pos (ht : N.tm.HaltsWithin x t) :
    ∀ (i : ℕ) (j : Fin (r + 1)), j.val + i = r → ∀ (c : Fin (r + 2)) (C : ACfg N r x),
      RewindAt C j c → C.inputPos.val ≤ t + 1 →
        ∀ w : List Bool, w.length = i * (2 * t + 3) + 1 →
          ((amp N r dec).tm.runWith w C).state = none := by
  intro i
  induction i with
  | zero =>
    intro j hj c C hC _ w hw
    obtain ⟨b, w', rfl⟩ : ∃ b w', w = b :: w' := by
      cases w with
      | nil => simp at hw
      | cons b w' => exact ⟨b, w', rfl⟩
    have hlast : ¬ j.val < r := by omega
    cases b
    · rw [(rewind_last hC.1 hlast w').2]; rfl
    · rw [(rewind_last hC.1 hlast w').1]; rfl
  | succ i ih =>
    intro j hj c C hC hpos w hw
    have hjr : j.val < r := by omega
    set p := (moveInputPos C.inputPos (-1)).val with hp
    have hp' : p ≤ t + 1 := by
      rw [hp, ← SignType.neg_eq_neg_one, FinTM.moveInputPos_neg_val]
      omega
    have hrun := (rewind_run_pos (dec := dec) hC.1 hjr).2
    have hE := restart_eq_emb C ⟨j.val + 1, by omega⟩ c
      (fun t ht => hC.2.2 t (by rw [ht]; exact Nat.lt_succ_self _)) hC.2.1
    have hF : Fresh (restart C ⟨j.val + 1, by omega⟩ c) (j.val + 1) :=
      fun t ht => hC.2.2 t (by omega)
    have hcomp := halts_comp_pos (B := t + 1)
      (fun u b hu => step_emb (dec := dec) (restart C ⟨j.val + 1, by omega⟩ c)
        ⟨j.val + 1, by omega⟩ c u b hu)
      (fun u hu hu' w hw => ih ⟨j.val + 1, by omega⟩ (by show j.val + 1 + i = r; omega) _ _
        (rewindAt_emb c hu hF) hu' w hw) t (N.tm.initCfg x) (by simp; omega) ht
    have hmul : (i + 1) * (2 * t + 3) = i * (2 * t + 3) + (2 * t + 3) := by ring
    rw [← List.take_append_drop (p + 2) w, NDTM.runWith_append,
      hrun _ (List.length_take_of_le (by omega)), hE]
    exact halted_of_le hcomp (by simp only [List.length_drop]; omega)

/-- **The repetition machine halts in `O(r t)` steps**: if `N` halts on `x` within `t` on every
branch, then `amp N r dec` halts within `t + r (2t + 3) + 1`, whatever `|x|` is.
[AB09, §7.7, p. 139] -/
theorem amp_haltsWithin_pos (ht : N.tm.HaltsWithin x t) :
    (amp N r dec).tm.HaltsWithin x (t + (r * (2 * t + 3) + 1)) := by
  intro w hw
  rw [init_eq_emb]
  exact halts_comp_pos (B := t + 1) (fun u b hu => step_emb _ 0 0 u b hu)
    (fun u hu hu' w hw => rewind_halts_pos ht r 0 (by simp) _ _ (rewindAt_emb 0 hu fresh_init)
      hu' w hw) t (N.tm.initCfg x) (by simp; omega) ht w hw

/-- The output distribution of `amp N r dec` at the time bound of `amp_haltsWithin_pos`. -/
theorem amp_outputProb_pos (ht : N.tm.HaltsWithin x t) (v : Bool) :
    (amp N r dec).outputProb x (t + (r * (2 * t + 3) + 1)) [v] =
      randProb ((r + 1) * t) (fun l => dec (blockCount t (r + 1) (acc N x) l) = v) := by
  rw [← amp_outputProb ht v,
    ← FinNDTM.outputProb_eq_of_haltsWithin (amp_haltsWithin_pos ht)
      (le_max_left _ (t + (r * (t + x.length + 2) + 1))),
    FinNDTM.outputProb_eq_of_haltsWithin (amp_haltsWithin ht) (le_max_right _ _)]

end Randomized.Amplify

namespace Turing.FinNDTM

open Randomized

/-- Threshold-`p` deciding is monotone in the time bound and antitone in the threshold. -/
theorem BPDecidesInTimeWith.mono {N : FinNDTM Bool} {L : Language Bool} {T₁ T₂ : ℕ → ℕ}
    {p q : ℕ → ℚ} (h : N.BPDecidesInTimeWith L T₁ p) (hT : ∀ n, T₁ n ≤ T₂ n)
    (hp : ∀ n, q n ≤ p n) : N.BPDecidesInTimeWith L T₂ q := by
  intro x
  obtain ⟨hhalt, hprob⟩ := h x
  refine ⟨hhalt.mono (hT _), ?_⟩
  rw [outputProb_eq_of_haltsWithin hhalt (hT _)]
  exact (hp _).trans hprob

/-- A decider in time `T` has `T(n) ≥ 1` for every `n`: no branch is halted at time `0`. -/
theorem BPDecidesInTimeWith.one_le {N : FinNDTM Bool} {L : Language Bool} {T : ℕ → ℕ}
    {p : ℕ → ℚ} (h : N.BPDecidesInTimeWith L T p) (n : ℕ) : 1 ≤ T n := by
  by_contra h0
  have hT : T (List.replicate n false).length = 0 := by simp only [List.length_replicate]; omega
  have := (h (List.replicate n false)).1 [] (by rw [hT]; rfl)
  simp at this

/-- **Majority of `2n + 1` runs** [AB09, §7.4.1]: a decider with success `1/2 + ε` in time `t`
gives one with success `1 - 2 (1 - 4ε²)^n` in time `t + 2n (2t + 3) + 1`.

The runs of `Amplify.amp` are independent blocks (`Amplify.amp_outputProb_pos`), whose
majority is correct with that probability (`Amplify.majority_randProb_ge`). -/
theorem BPDecidesInTimeWith.amp {N : FinNDTM Bool} {L : Language Bool} {t : ℕ → ℕ} {ε : ℚ}
    (hε : 0 ≤ ε) (h : N.BPDecidesInTimeWith L t fun _ => 1/2 + ε) (n : ℕ) :
    (Amplify.amp N (2 * n) fun m => decide (2 * n + 1 < 2 * m)).BPDecidesInTimeWith L
      (fun l => t l + (2 * n * (2 * t l + 3) + 1)) fun _ => 1 - 2 * (1 - 4 * ε ^ 2) ^ n := by
  intro x
  set T := t x.length
  set dec : ℕ → Bool := fun m => decide (2 * n + 1 < 2 * m)
  obtain ⟨hT, hp⟩ := h x
  refine ⟨Amplify.amp_haltsWithin_pos hT, ?_⟩
  show _ ≤ (Amplify.amp N (2 * n) dec).outputProb x (T + (2 * n * (2 * T + 3) + 1)) _
  rw [Amplify.amp_outputProb_pos hT]
  exact Amplify.majority_randProb_ge hε _ hp

end Turing.FinNDTM

namespace Randomized

open Turing

/-- `BPTIME(T)` with success threshold `ρ`: the languages decided by some PTM in time `c · T`
with `Pr[M(x) = L(x)] ≥ ρ`. [AB09, Def 7.2 and p. 125] -/
def BPTIMEWith (ρ : ℚ) (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (N : FinNDTM Bool), N.BPDecidesInTimeWith L (fun n => c * T n) fun _ => ρ}

/-- `BPTIME` is the threshold-`2/3` case. -/
theorem BPTIMEWith_two_thirds (T : ℕ → ℕ) : BPTIMEWith (2/3) T = BPTIME T := rfl

/-- Lowering the threshold enlarges the class. -/
theorem BPTIMEWith_anti {ρ ρ' : ℚ} (h : ρ' ≤ ρ) (T : ℕ → ℕ) :
    BPTIMEWith ρ T ⊆ BPTIMEWith ρ' T := by
  rintro L ⟨c, N, hN⟩
  exact ⟨c, N, hN.mono (fun _ => le_rfl) fun _ => h⟩

/-- Success `1/2 + ε` can be raised to `1 - η` within `BPTIME(T)`, given `n` with
`2 (1 - 4ε²)^n ≤ η`: majority of `2n + 1` runs, in time `(10n + 2) c · T`. [AB09, §7.4.1] -/
theorem BPTIMEWith_subset_of_amp {ε η : ℚ} (hε : 0 ≤ ε) {n : ℕ}
    (hn : 2 * (1 - 4 * ε ^ 2) ^ n ≤ η) (T : ℕ → ℕ) :
    BPTIMEWith (1/2 + ε) T ⊆ BPTIMEWith (1 - η) T := by
  rintro L ⟨c, N, hN⟩
  refine ⟨(10 * n + 2) * c, _, (hN.amp hε n).mono (fun l => ?_) fun _ => by linarith⟩
  have h1 := hN.one_le l
  nlinarith

/-- **The constant `2/3` in `BPTIME(T(n))` is arbitrary** [AB09, §7.1, p. 125]: for every
constant `ρ ∈ (1/2, 1)` and every `T`, `BPTIMEWith ρ T = BPTIME T`.

**Proof sketch.** Both inclusions are `BPTIMEWith_subset_of_amp` followed by
`BPTIMEWith_anti`: from `ρ = 1/2 + (ρ - 1/2)` to `2/3`, and from `2/3 = 1/2 + 1/6` to `ρ`,
choosing `n` with `(1 - 4ε²)^n` small (`exists_pow_lt_of_lt_one`). -/
theorem BPTIMEWith_eq_BPTIME {ρ : ℚ} (h1 : 1/2 < ρ) (h2 : ρ < 1) (T : ℕ → ℕ) :
    BPTIMEWith ρ T = BPTIME T := by
  rw [← BPTIMEWith_two_thirds]
  refine Set.Subset.antisymm ?_ ?_
  · set ε := ρ - 1/2 with hε
    have hq : 1 - 4 * ε ^ 2 < 1 := by nlinarith
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℚ) < 1/6 by norm_num) hq
    have h := BPTIMEWith_subset_of_amp (n := n) (ε := ε) (η := 1/3) (by linarith) (by linarith) T
    rw [show 1/2 + ε = ρ by ring] at h
    exact h.trans (BPTIMEWith_anti (by norm_num) T)
  · have hq : 1 - 4 * (1/6 : ℚ) ^ 2 < 1 := by norm_num
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℚ) < (1 - ρ) / 2 by linarith) hq
    have h := BPTIMEWith_subset_of_amp (n := n) (ε := 1/6) (η := 1 - ρ) (by norm_num)
      (by linarith) T
    rw [show (1/2 : ℚ) + 1/6 = 2/3 by norm_num] at h
    exact h.trans (BPTIMEWith_anti (by linarith) T)

end Randomized
