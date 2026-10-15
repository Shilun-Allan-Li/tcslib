/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.Space
import TCSlib.Complexity.Randomized.RandomBits
import Mathlib.Data.Fintype.Pigeonhole

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Acceptance probabilities of log-space PTMs by dynamic programming

The counting half of [AB09, Exercise 7.9] (`BPL ⊆ P`). Fix a PTM `N` using space `sp`, an
input `x` and a window radius `s ≥ sp(|x|)`, so that every configuration on every branch has a
code (`Complexity.Codec.cfgCode`) below `V ≥ 2 ^ (codeK N · (s + logSpace |x| + 1))`. The table
`dpVal t c` is computed from the code languages alone: `dpVal 0 c` is `1` on accepting codes
and `0` elsewhere, and `dpVal (t + 1) c` sums `dpVal t c'` over the codes `c' < V` that `c`
steps to under coin `0` and under coin `1`. On the code of a reachable configuration it is
`2^t` times the probability of acceptance within `t` further coins, and a halting log-space
PTM halts within `V` steps on every branch, so `dpVal V` at the initial code is `2^V` times the
acceptance probability.

## Main definitions

* `Randomized.BPLInP.fixCoin` — the PTM whose two transition functions are both `tr b`.
* `Randomized.BPLInP.dpVal` — the dynamic-programming table.

## Main results

* `Randomized.BPLInP.haltsWithin_of_codes` — a halting space-bounded PTM halts within the
  number of codes on every branch.
* `Randomized.BPLInP.dpVal_eq` — the table counts accepting coin words.
* `Randomized.BPLInP.dpVal_init` — at the initial code after `V` rounds it is
  `2^V · Pr[M(x) = 1]`.
* `Randomized.BPLInP.dpVal_le` — its entries are below `(2V)^t`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized.BPLInP

open Complexity Complexity.Codec Turing
open Complexity.LogProg (bitsVal)

/-- The PTM `N` with the coin fixed to `b`: both transition functions are `N.tm.tr b`. Its
configuration-graph edges are the coin-`b` steps of `N`. It is definitionally
`(⟨N.k, N.State, N.tm.fixChoice b⟩ : FinTM Bool).toFinNDTM`. -/
def fixCoin (N : FinNDTM Bool) (b : Bool) : FinNDTM Bool where
  k := N.k
  State := N.State
  tm := ⟨N.tm.q₀, fun _ => N.tm.tr b⟩

/-- A step of `fixCoin N b` under any coin is a coin-`b` step of `N`. -/
theorem stepWith_fixCoin (N : FinNDTM Bool) (b b' : Bool) {x : List Bool}
    (C : Cfg (fixCoin N b).k Bool (fixCoin N b).State x) :
    (fixCoin N b).tm.stepWith b' C = N.tm.stepWith b C := by
  cases h : C.state <;> simp [NDTM.stepWith, h, fixCoin]

variable (N : FinNDTM Bool) (x : List Bool) (s V : ℕ)

open Classical in
/-- The dynamic-programming table over codes `c < V` at radius `s`: `dpVal 0 c` is `1` iff `c`
is an accepting code, and `dpVal (t + 1) c` sums `dpVal t c'` over the codes `c'` that `c` steps
to under coin `0` and under coin `1`. -/
noncomputable def dpVal : ℕ → ℕ → ℕ
  | 0, c => if pairEncode x (pairEncode (Nat.bits c) (Nat.bits s)) ∈ acceptLang N then 1 else 0
  | t + 1, c => ∑ c' ∈ Finset.range V,
      ((if StepRel (fixCoin N false) x s c c' then dpVal t c' else 0) +
        (if StepRel (fixCoin N true) x s c c' then dpVal t c' else 0))

open Classical in
/-- The entries of the table after `t` rounds are at most `(2V)^t`. -/
theorem dpVal_le (t c : ℕ) : dpVal N x s V t c ≤ (2 * V) ^ t := by
  induction t generalizing c with
  | zero => simp only [dpVal, pow_zero]; split_ifs <;> omega
  | succ t ih =>
    simp only [dpVal]
    calc ∑ c' ∈ Finset.range V, ((if StepRel (fixCoin N false) x s c c' then
            dpVal N x s V t c' else 0) + (if StepRel (fixCoin N true) x s c c' then
            dpVal N x s V t c' else 0))
        ≤ ∑ _c' ∈ Finset.range V, 2 * (2 * V) ^ t := by
          refine Finset.sum_le_sum fun c' _ => ?_
          have := ih c'
          split_ifs <;> omega
      _ = (2 * V) ^ (t + 1) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring

variable {N x s V}

/-- The configuration after the coin word `w`. -/
local notation "run" w => N.tm.runWith w (N.tm.initCfg x)

/-- Configurations reached on a branch of a space-`sp` PTM lie in the window of radius
`s ≥ sp(|x|)`. -/
theorem inWin_run {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ s) (w : List Bool) :
    InWin N s (run w) := by
  simpa using inWin_runWith_take w ((hN x w).trans hs) w.length

/-- Equal codes of window-bounded configurations give equal vertices. -/
theorem coreSum_eq_of_code_eq {C D : Cfg N.k Bool N.State x} (hC : InWin N s C)
    (hD : InWin N s D) (h : cfgCode s C = cfgCode s D) : NDTM.coreSum C = NDTM.coreSum D :=
  coreSum_eq_of_cfgWord_eq hC hD (by rw [← bits_cfgCode, ← bits_cfgCode, h])

/-- From a reachable code, the coin-`b` step relation points exactly at the code of the
coin-`b` successor. -/
theorem stepRel_iff {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ s) (v : List Bool)
    (b : Bool) (c' : ℕ) :
    StepRel (fixCoin N b) x s (cfgCode s (run v)) c' ↔ c' = cfgCode s (run (v ++ [b])) := by
  have hstep : (run (v ++ [b])) = N.tm.stepWith b (run v) := by
    rw [NDTM.runWith_append, NDTM.runWith_cons, NDTM.runWith_nil]
  constructor
  · intro h
    obtain ⟨C, hC, hcC, C', ⟨b', hb'⟩, -, hcC'⟩ := (mem_stepLang (fixCoin N b) x _ _ s).mp h
    have hcore : NDTM.coreSum C = NDTM.coreSum (run v) :=
      coreSum_eq_of_code_eq hC (inWin_run hN hs v) hcC
    rw [← hcC', ← hb']
    change cfgCode s ((fixCoin N b).tm.stepWith b' C) = _
    rw [stepWith_fixCoin, hstep]
    exact congrArg bitsVal (cfgWord_congr (NDTM.coreSum_stepWith N.tm b hcore))
  · rintro rfl
    refine (mem_stepLang (fixCoin N b) x _ _ s).mpr ⟨run v, inWin_run hN hs v, rfl,
      run (v ++ [b]), ⟨b, ?_⟩, inWin_run hN hs _, rfl⟩
    change (fixCoin N b).tm.stepWith b (run v) = _
    rw [stepWith_fixCoin, hstep]

/-- A reachable code is accepting iff its configuration is halted with output `[true]`. -/
theorem acceptLang_iff {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ s)
    (v : List Bool) :
    pairEncode x (pairEncode (Nat.bits (cfgCode s (run v))) (Nat.bits s)) ∈ acceptLang N ↔
      (run v).state = none ∧ (run v).output = [true] := by
  rw [mem_acceptLang]
  constructor
  · rintro ⟨C, hC, hcC, hst, hout⟩
    have hcore := coreSum_eq_of_code_eq hC (inWin_run hN hs v) hcC
    have h1 := congrArg (fun z => z.1.1) hcore
    have h2 := congrArg Prod.snd hcore
    simp only [NDTM.coreSum, MultiTapeTM.ConfigCount.core] at h1 h2
    rw [hout] at h2
    exact ⟨h1 ▸ hst, (outSummary_eq_accept_iff _).mp h2.symm⟩
  · rintro ⟨hst, hout⟩
    exact ⟨run v, inWin_run hN hs v, rfl, hst, hout⟩

/-- A probability over zero coins is the truth value of the event at the empty word. -/
theorem randProb_zero (A : List Bool → Prop) [DecidablePred A] :
    randProb 0 A = if A [] then 1 else 0 := by
  unfold randProb
  by_cases h : A [] <;> simp [h, Finset.filter_true_of_mem, Finset.filter_false_of_mem]

/-- **The table counts accepting coin words**: on the code of the configuration after `v`, the
table after `t` rounds is `2^t` times the probability that `t` further coins end halted with
output `[true]`.

**Proof sketch.** Induction on `t`. At `t = 0` the accepting-code test is the acceptance of the
configuration (`acceptLang_iff`). At `t + 1` the coin-`b` step relation from the code points
only at the code of the coin-`b` successor (`stepRel_iff`), which is below `V` (`cfgCode_lt`),
so the sum over `c' < V` collapses to the two successors; by induction and conditioning on
the first coin (`randProb_succ`) this is `2^{t+1}` times the probability. -/
theorem dpVal_eq {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ s)
    (hV : 2 ^ (codeK N * (s + logSpace x.length + 1)) ≤ V) (t : ℕ) (v : List Bool) :
    (dpVal N x s V t (cfgCode s (run v)) : ℚ) = 2 ^ t * randProb t (fun u =>
      (run (v ++ u)).state = none ∧ (run (v ++ u)).output = [true]) := by
  classical
  induction t generalizing v with
  | zero =>
    rw [randProb_zero]
    simp only [List.append_nil, pow_zero, one_mul]
    by_cases h : (run v).state = none ∧ (run v).output = [true]
    · simp only [dpVal, if_pos h, if_pos ((acceptLang_iff hN hs v).mpr h), Nat.cast_one]
    · simp only [dpVal, if_neg h, if_neg (mt (acceptLang_iff hN hs v).mp h), Nat.cast_zero]
  | succ t ih =>
    have hcol : ∀ b : Bool, ∑ c' ∈ Finset.range V,
        (if StepRel (fixCoin N b) x s (cfgCode s (run v)) c' then dpVal N x s V t c' else 0) =
          dpVal N x s V t (cfgCode s (run (v ++ [b]))) := fun b => by
      rw [Finset.sum_eq_single (cfgCode s (run (v ++ [b])))]
      · rw [if_pos ((stepRel_iff hN hs v b _).mpr rfl)]
      · intro c' _ hne
        rw [if_neg fun h => hne ((stepRel_iff hN hs v b c').mp h)]
      · intro hnot
        exact absurd (Finset.mem_range.mpr ((cfgCode_lt s _).trans_le hV)) hnot
    simp only [dpVal]
    rw [Finset.sum_add_distrib, hcol, hcol, Nat.cast_add, ih, ih, randProb_succ]
    simp only [List.append_assoc, List.singleton_append]
    ring

/-- **A halting log-space PTM halts within the number of codes**: if every branch on `x` halts
within some `T`, every branch halts within `V` steps. [AB09, §4.1.1, Claim 4.4(1)]

**Proof sketch.** Suppose a branch `w` of length `V` has not halted. The `V + 1` configurations
after its prefixes have codes below `V`, so two prefixes `i < j` share a code, hence a vertex
(`coreSum_eq_of_code_eq`). Repeating the segment between them keeps the vertex
(`Turing.NDTM.coreSum_runWith`), so `w.take i` followed by `T` copies of the segment is a
branch of length at least `T` whose state is that of `w.take i`, not halted (else `w` would
have halted), contradicting halting within `T`. -/
theorem haltsWithin_of_codes {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ s)
    (hV : 2 ^ (codeK N * (s + logSpace x.length + 1)) ≤ V) {T : ℕ}
    (hT : N.tm.HaltsWithin x T) : N.tm.HaltsWithin x V := by
  intro w hw
  by_contra hne
  let f : Fin (V + 1) → Fin V := fun j =>
    ⟨cfgCode s (run (w.take j)), (cfgCode_lt s _).trans_le hV⟩
  obtain ⟨i₀, j₀, hij, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have key : ∀ i j : ℕ, i < j → j ≤ V →
      cfgCode s (run (w.take i)) = cfgCode s (run (w.take j)) → False := by
    intro i j hij hjV hcode
    set u := w.take i
    set v := (w.take j).drop i
    have huv : u ++ v = w.take j := by
      simp only [u, v]
      conv_rhs => rw [← List.take_append_drop i (w.take j)]
      rw [List.take_take, min_eq_left hij.le]
    have hvlen : v.length = j - i := by simp [v, hw]; omega
    have hcore : NDTM.coreSum (run (u ++ v)) = NDTM.coreSum (run u) := by
      rw [huv]
      exact (coreSum_eq_of_code_eq (inWin_run hN hs _) (inWin_run hN hs _) hcode).symm
    have pump : ∀ m : ℕ, NDTM.coreSum (run (u ++ (List.replicate m v).flatten)) =
        NDTM.coreSum (run u) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [List.replicate_succ', List.flatten_append, List.flatten_singleton,
          ← List.append_assoc, NDTM.runWith_append, NDTM.coreSum_runWith N.tm v ih,
          ← NDTM.runWith_append, hcore]
    have hu : (run u).state ≠ none := by
      intro hu
      apply hne
      rw [← List.take_append_drop i w, NDTM.runWith_append, NDTM.runWith_of_halt _ hu]
      exact hu
    have hlen : T ≤ (u ++ (List.replicate T v).flatten).length := by
      simp only [List.length_append, List.length_flatten, List.map_replicate,
        List.sum_replicate, smul_eq_mul, hvlen]
      have : T ≤ T * (j - i) := Nat.le_mul_of_pos_right T (by omega)
      omega
    have hstate := congrArg (fun z => z.1.1) (pump T)
    simp only [NDTM.coreSum, MultiTapeTM.ConfigCount.core] at hstate
    exact hu (hstate ▸ (hT.mono hlen) _ rfl)
  have hval : cfgCode s (run (w.take i₀)) = cfgCode s (run (w.take j₀)) :=
    congrArg Fin.val hf
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · exact key i₀ j₀ h (Nat.lt_succ_iff.mp j₀.isLt) hval
  · exact key j₀ i₀ h (Nat.lt_succ_iff.mp i₀.isLt) hval.symm

/-- **The table computes the acceptance probability**: if every branch on `x` halts within some
`T`, then after `V` rounds the table at the initial code is `2^V · Pr[M(x) = 1]` over `V`
coins. -/
theorem dpVal_init {sp : ℕ → ℕ} (hN : N.UsesSpace sp) (hs : sp x.length ≤ s)
    (hV : 2 ^ (codeK N * (s + logSpace x.length + 1)) ≤ V) {T : ℕ}
    (hT : N.tm.HaltsWithin x T) :
    (dpVal N x s V V (cfgCode s (N.tm.initCfg x)) : ℚ) = 2 ^ V * N.outputProb x V [true] := by
  have h := dpVal_eq hN hs hV V []
  simp only [NDTM.runWith_nil, List.nil_append] at h
  rw [h, FinNDTM.outputProb]
  congr 1
  refine randProb_congr fun r => ?_
  have hhalt := haltsWithin_of_codes hN hs hV hT _ (List.length_ofFn (f := r))
  simp only [FinNDTM.outputWith, hhalt, true_and]

end Randomized.BPLInP
