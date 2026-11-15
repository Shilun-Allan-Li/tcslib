/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.ExpectedTime
import TCSlib.Complexity.Randomized.PTMEquiv

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Expected running time gives the same RP and coRP

[AB09, §7.4.2]: "When defining `RTIME(T(n))` and `BPTIME(T(n))` … we could have used expected
running time instead … this yields an equivalent definition." The `BPTIME` half is
`Randomized.BPP_ExpPTM_eq_BPP_PTM`; this file proves the `RTIME` half at the level of the
polynomial classes, and its consequence for `coRP`.

## Main definitions

* `Turing.FinNDTM.RDecidesInExpTime`, `Randomized.RP_ExpPTM`, `Randomized.coRP_ExpPTM` —
  one-sided error in expected polynomial time [AB09, §7.4.2].

## Main results

* `Randomized.InRPWith.inRP_of_const` — a constant number of `OR` votes lifts any constant
  acceptance threshold to `2/3`.
* `Randomized.RP_ExpPTM_eq_RP_PTM`, `Randomized.coRP_ExpPTM_eq_coRP_PTM` — [AB09, §7.4.2].

## Divergences

* As for `Randomized.BPP_ExpPTM`, "`Pr[M(x) = 1] ≥ 2/3`" for a machine that need not halt is
  read as a supremum over time: `∀ ε > 0, ∃ t, 2/3 − ε ≤ Pr[halted within t steps with 1]`.
  "`x ∉ L ⇒ Pr[M(x) = 1] = 0`" is read, as in `Turing.FinNDTM.RDecidesInTime` and
  `Turing.FinNDTM.ZDecidesInTime`, as "every halted branch outputs `[0]`".
* The book truncates at `100·T(n)` steps and loses `1/100`. For one-sided error the timeout
  output must be `0`: cutting at `Q ≥ 100·T` keeps non-members at acceptance `0` and members at
  `≥ 2/3 − 1/100 ≥ 5/8`, and two `OR` votes restore `2/3`. The cut is taken on the certificate
  side (`Complexity.exists_choiceVerifier_mem_P` accepts exactly the coin words on which the
  machine has halted with output `[1]`), so no explicit counter machine is built.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Turing.FinNDTM

/-- `N` decides `L` with one-sided error in expected time `T`: `E[T_{N,x}] ≤ T(|x|)`; on
members the probability of halting with output `[1]` (as a supremum over time) is at least
`2/3`; on non-members every halted branch outputs `[0]`. [AB09, Def 7.6 and §7.4.2] -/
def RDecidesInExpTime (N : FinNDTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, N.ExpTimeLe x (T x.length) ∧
    (x ∈ L → ∀ ε : ℚ, 0 < ε → ∃ t : ℕ,
      2 / 3 - ε ≤ Randomized.randProb t (fun w => N.haltRun x w = some [true])) ∧
    (x ∉ L → ∀ w : List Bool, (N.tm.runWith w (N.tm.initCfg x)).state = none →
      N.outputWith x w = [false])

end Turing.FinNDTM

namespace Randomized

open Complexity Turing

/-- `RP` with expected running time: `⋃_e {L | some PTM decides L with one-sided error in
expected time c·(n^e + 1)}`. [AB09, §7.4.2] -/
def RP_ExpPTM : Set (Language Bool) :=
  ⋃ e : ℕ, {L | ∃ (c : ℕ) (N : FinNDTM Bool), N.RDecidesInExpTime L fun n => c * (n ^ e + 1)}

/-- `coRP` with expected running time: `{L | Lᶜ ∈ RP_ExpPTM}`. [AB09, §7.3 and §7.4.2] -/
def coRP_ExpPTM : Set (Language Bool) := {L | Lᶜ ∈ RP_ExpPTM}

/-- **Constant-threshold `RP` amplification**: if a polynomial-time verifier accepts members
with probability at least the constant `ρ ≤ 1` and never accepts non-members, then `K`
independent runs combined by `OR` give `InRP`, whenever `(1 − ρ)^K ≤ 1/3`.

**Proof sketch.** As `rp_error_reduction` with `K` blocks: the `OR` rejects exactly when the
vote count is `0`, of probability `(1 − s)^K ≤ (1 − ρ)^K` (`randProb_blockCount`); each block
of a non-member's coins is a genuine coin word, hence rejected. `rp_error_reduction` itself
does not apply: `InRPWeak c` demands acceptance `min (2/3) ((n+1)^{-c}) = 2/3` at `n = 0`,
which a constant `ρ < 2/3` need not meet. -/
theorem InRPWith.inRP_of_const {ρ : ℚ} {K : ℕ} (hK : (1 - ρ) ^ K ≤ 1/3)
    {L : Language Bool} (h : InRPWith (fun _ => ρ) L) : InRP polyTimeModel L := by
  obtain ⟨M, a, k, hM, hprop⟩ := h
  refine ⟨anyVerifier M (polyLen a k) (polyLen K 0), K * a, k,
    polyTimeModel_closedUnderAny M a k K 0 hM, fun x => ?_⟩
  have hlen : polyLen (K * a) k x.length = polyLen K 0 x.length * polyLen a k x.length := by
    unfold polyLen
    ring
  rw [hlen]
  set q := polyLen a k x.length with hq
  set K' := polyLen K 0 x.length with hK'
  have hKK : K' = K := by simp [hK', polyLen]
  constructor
  · intro hx
    set s := randProb q (fun l => M x l = true) with hs
    have hacc : randProb (K' * q)
        (fun l => anyVerifier M (polyLen a k) (polyLen K 0) x l = true) = 1 - (1 - s) ^ K' := by
      have h0 := randProb_blockCount q (M x) K' 0 (Nat.zero_le _)
      simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul,
        Nat.sub_zero] at h0
      rw [randProb_congr (B := fun l => ¬ (blockCount q K' (M x) l = 0)) fun r => by
        simp only [anyVerifier, blockCount, List.any_eq_true, ← Nat.pos_iff_ne_zero,
          List.countP_pos_iff, hq, hK'], randProb_not, h0]
    rw [hacc, hKK]
    have hs1 : s ≤ 1 := randProb_le_one
    have hsρ : ρ ≤ s := (hprop x).1 hx
    have hpow : (1 - s) ^ K ≤ (1 - ρ) ^ K := pow_le_pow_left₀ (by linarith) (by linarith) K
    linarith
  · intro hx r
    have hl : (List.ofFn r).length = K' * q := List.length_ofFn
    unfold anyVerifier
    rw [List.any_eq_false]
    intro i hi
    rw [List.mem_range, ← hK'] at hi
    have hiq : i * q + q ≤ K' * q := by
      have := Nat.mul_le_mul_right q (Nat.succ_le_of_lt hi)
      rwa [Nat.succ_mul] at this
    have hb : (((List.ofFn r).drop (i * q)).take q).length = q := by
      rw [List.length_take, List.length_drop, hl]
      omega
    obtain ⟨r', hr'⟩ := exists_ofFn_eq hb
    rw [← hq, hr', (hprop x).2 hx r']
    decide

/-- **Expected time ⇒ `RP`** [AB09, §7.4.2]: a one-sided-error PTM with expected time
`c(n^e + 1)` gives an `InRP polyTimeModel` verifier.

**Proof sketch.** With `B = c(|x|^e + 1)` and `Q = 200c(|x|+1)^e ≥ 100 B`, the choice-word
verifier for `[1]` at length `Q` accepts exactly the coin words on which `N` has halted with
output `[1]`. On non-members no halted branch outputs `[1]`, so it never accepts; on members
Markov truncation (`haltProb_le_truncate`, `haltProb_mono`) gives acceptance
`≥ 2/3 − 1/100 ≥ 5/8`. Two `OR` votes (`InRPWith.inRP_of_const`, `(3/8)² ≤ 1/3`) restore
`2/3`. -/
theorem inRP_of_mem_RP_ExpPTM {L : Language Bool} (h : L ∈ RP_ExpPTM) :
    InRP polyTimeModel L := by
  classical
  obtain ⟨e, c, N, hN⟩ := Set.mem_iUnion.mp h
  obtain ⟨V, hVP, hV⟩ := exists_choiceVerifier_mem_P N (200 * c) e
  refine InRPWith.inRP_of_const (ρ := 5/8) (K := 2) (by norm_num)
    ⟨fun x r => MultiTapeTM.indicator V (x ++ r), 200 * c, e, eff_append_mem hVP, fun x => ?_⟩
  have hNx := hN x
  dsimp only at hNx
  obtain ⟨hexp, hin, hout⟩ := hNx
  set B := c * (x.length ^ e + 1)
  set Q := polyLen (200 * c) e x.length
  have hBQ : 100 * B ≤ Q := by
    have := choiceBudget_le (100 * c) e x.length
    simp only [Q, B, polyLen] at this ⊢
    nlinarith [this]
  have hacc : ∀ r : Fin Q → Bool, MultiTapeTM.indicator V (x ++ List.ofFn r) = true ↔
      N.haltRun x (List.ofFn r) = some [true] := fun r => by
    rw [indicator_eq_true_iff]
    exact (hV x _ List.length_ofFn).trans FinNDTM.haltRun_eq_some_iff.symm
  refine ⟨fun hx => ?_, fun hx r => ?_⟩
  · have hge : 5 / 8 ≤ randProb Q (fun w => N.haltRun x w = some [true]) := by
      by_contra hlt
      push_neg at hlt
      obtain ⟨t, ht⟩ := hin hx (2 / 3 - 1 / 100 - 5 / 8) (by norm_num)
      have h1 := FinNDTM.haltProb_le_truncate hexp [true] t
      have h2 := FinNDTM.haltProb_mono (N := N) (x := x) [true] hBQ
      linarith
    exact le_trans hge (randProb_mono fun r hr => (hacc r).mpr hr)
  · show MultiTapeTM.indicator V (x ++ List.ofFn r) = false
    cases hi : MultiTapeTM.indicator V (x ++ List.ofFn r)
    · rfl
    · obtain ⟨hhalt, htrue⟩ := FinNDTM.haltRun_eq_some_iff.mp ((hacc r).mp hi)
      rw [hout hx _ hhalt] at htrue
      exact absurd htrue (by decide)

/-- A worst-case one-sided-error PTM is an expected-time one. [AB09, §7.4.2]

**Proof sketch.** Halting within `T` gives `E[T_{N,x}] ≤ T` (`expTimeLe_of_haltsWithin`) and
`Pr_T[halted with 1] = Pr[N(x) = 1]`. A halted branch `w` of a non-member keeps its output
when padded to length `≥ T` (`haltRun_isPrefixStable`), and that output is the one of the
first `T` coins, which is `[0]`. -/
theorem RP_PTM_subset_RP_ExpPTM : RP_PTM ⊆ RP_ExpPTM := by
  intro L h
  obtain ⟨e, c, N, hN⟩ := Set.mem_iUnion.mp h
  refine Set.mem_iUnion.mpr ⟨e, c, N, fun x => ?_⟩
  have hNx := hN x
  dsimp only at hNx
  obtain ⟨hhalt, hin, hout⟩ := hNx
  set T := c * (x.length ^ e + 1)
  refine ⟨FinNDTM.expTimeLe_of_haltsWithin hhalt, fun hx ε hε => ⟨T, ?_⟩, fun hx w hw => ?_⟩
  · have heq : randProb T (fun w => N.haltRun x w = some [true]) = N.outputProb x T [true] :=
      randProb_congr fun r => by
        rw [FinNDTM.haltRun_eq_some_iff]
        exact ⟨fun h => h.2, fun h => ⟨hhalt _ List.length_ofFn, h⟩⟩
    rw [heq]
    linarith [hin hx]
  · have hw' : N.haltRun x w = some (N.outputWith x w) :=
      FinNDTM.haltRun_eq_some_iff.mpr ⟨hw, rfl⟩
    set u := w ++ List.replicate (T - w.length) false with hu_def
    have hu := FinNDTM.haltRun_eq_some_iff.mp
      (N.haltRun_isPrefixStable x w (List.replicate (T - w.length) false) _ hw')
    have hTu : T ≤ u.length := by
      simp only [u, List.length_append, List.length_replicate]
      omega
    have htake : N.outputWith x u = N.outputWith x (u.take T) := by
      unfold FinNDTM.outputWith
      rw [FinNDTM.runWith_eq_runWith_take hhalt hTu]
    rw [← hu.2, htake]
    exact hout hx _ (List.length_take_of_le hTu)

/-- **Expected time gives the same `RP`** [AB09, §7.4.2]. -/
theorem RP_ExpPTM_eq_RP_PTM : RP_ExpPTM = RP_PTM :=
  Set.Subset.antisymm (fun L h => (mem_RP_PTM_iff L).mpr (inRP_of_mem_RP_ExpPTM h))
    RP_PTM_subset_RP_ExpPTM

/-- **Expected time gives the same `coRP`** [AB09, §7.4.2]. -/
theorem coRP_ExpPTM_eq_coRP_PTM : coRP_ExpPTM = coRP_PTM :=
  Set.ext fun L => show Lᶜ ∈ RP_ExpPTM ↔ Lᶜ ∈ RP_PTM by rw [RP_ExpPTM_eq_RP_PTM]

end Randomized
