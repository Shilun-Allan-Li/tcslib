import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.TuringMachine.ChoiceReplay
import TCSlib.Complexity.TuringMachine.Build.StepClock
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.ClassP.TimeConstructible
import TCSlib.Complexity.ClassNP.NDNormalForm
import TCSlib.Complexity.TuringMachine.Build.NDHost
import TCSlib.Complexity.TuringMachine.NDCodeSimulator
import TCSlib.Complexity.TuringMachine.UniversalStartup
import TCSlib.Complexity.ClassNP.TMSAT
import Lean.Util.FoldConsts

-- the patched ClassNP/ExhaustiveReplay (inlined)
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The exhaustive replay of a fixed NDTM

[AB09, §3.2, proof of Theorem 3.2]: the complement of a nondeterministic language is decidable
deterministically in exponential time "by examining all the possibilities for the machine's
nondeterministic choices", and that simulation suffices for the nondeterministic time
hierarchy. `Turing.FinNDTM.exists_exhaustiveDecider` is that simulation
for a fixed NDTM, as a public generic theorem (user decision 2 of 2026-10-13): on every input on
which all branches halt within `T`, a deterministic machine decides acceptance within
`C·2^{C·(T + 1)}`, with no input-length term. The exponential decider of the hierarchy is then
`BF := E(UN)`, the exhaustive replay of the universal NDTM; its statement is derived here
(`Turing.ndAcceptsWithin_decider_of_universal`, proved).

## Main definitions

No new definitions: the exhaustive replay and `BF` are existential contracts.

## Main results

* `Turing.FinNDTM.exists_exhaustiveDecider` — the exhaustive replay `E` (sorried).
* `Turing.ndAcceptsWithin_decider_of_universal` — `BF := E(UN)` (proved).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.2, proof of Theorem 3.2.)
-/

namespace Turing

/-! ### C1-E fill infrastructure (the `xr_` privates)

The semantic and arithmetic parts of the exhaustive replay, read through the published ND
semantics only: no branch halts at depth `0`; a branch of length `|w|` stays within the
radius-`|w|` window; at an all-halting depth `L ≤ T` acceptance within `L` and within `T`
agree; the first all-halting depth exists; the ledger's shape. Then two generic tools for the
machine: the translation of work tapes (a branch started on blank tapes at displaced heads is
the branch from `initCfg`, translated), and the first arrival at a stationary anchor (the
phase host's guard for every leaf row of this file). -/

/-- No branch of length `0` has halted: `Cfg.init` is live. -/
private theorem xr_not_haltsWithin_zero (N : FinNDTM Bool) (z : List Bool) :
    ¬ N.tm.HaltsWithin z 0 := by
  intro h
  have h0 := NDTM.haltsWithin_iff.mp h [] rfl
  rw [NDTM.runWith_nil, NDTM.initCfg_eq, Cfg.init_state] at h0
  exact Option.some_ne_none _ h0

/-- One step from the radius-`s` window stays in the radius-`s + 1` window, with the output
growing by at most one symbol. -/
private theorem xr_window_stepWith {k : ℕ} {S : Type} {x : List Bool} (tm : NDTM k Bool S)
    (b : Bool) (c : Cfg k Bool S x) (s : ℕ)
    (hpos : ∀ i, |c.workTapePos i| ≤ (s : ℤ))
    (hblank : ∀ i (p : ℤ), (s : ℤ) < |p| → c.workTapes i p = none)
    (hout : c.output.length ≤ s) :
    (∀ i, |(tm.stepWith b c).workTapePos i| ≤ ((s + 1 : ℕ) : ℤ)) ∧
    (∀ i (p : ℤ), ((s + 1 : ℕ) : ℤ) < |p| → (tm.stepWith b c).workTapes i p = none) ∧
    (tm.stepWith b c).output.length ≤ s + 1 := by
  cases hq : c.state with
  | none =>
    rw [NDTM.stepWith_of_halt hq]
    refine ⟨fun i => (hpos i).trans (by push_cast; omega), fun i p hp => hblank i p ?_, by omega⟩
    push_cast at hp; linarith
  | some q =>
    rw [NDTM.stepWith_of_some hq]
    refine ⟨fun i => ?_, fun i p hp => ?_, ?_⟩
    · have h1 := workTapePos_apply_le (tm.tr b q c.inputSymbol c.workTapeSymbols) c i
      have h2 := hpos i
      rw [abs_le] at h1 h2 ⊢
      push_cast
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · rw [Action.apply_workTapes]
      have h2 := hpos i
      have hp' : (s : ℤ) < |p| := by push_cast at hp; linarith
      have hne : p ≠ c.workTapePos i := by
        rintro rfl
        exact absurd h2 (not_le.mpr hp')
      rw [Function.update_of_ne hne]
      exact hblank i p hp'
    · rw [Action.apply_output, List.length_append]
      have : (tm.tr b q c.inputSymbol c.workTapeSymbols).output.toList.length ≤ 1 := by
        cases (tm.tr b q c.inputSymbol c.workTapeSymbols).output <;> simp
      omega

/-- After a branch of length `|w|` from the initial configuration, every work head lies within
`|w|` of its origin, every cell beyond radius `|w|` is blank, and the output has length at most
`|w|`: the window the clear must blank. -/
private theorem xr_window_runWith {k : ℕ} {S : Type} (tm : NDTM k Bool S) (z w : List Bool) :
    (∀ i, |(tm.runWith w (tm.initCfg z)).workTapePos i| ≤ (w.length : ℤ)) ∧
    (∀ i (p : ℤ), (w.length : ℤ) < |p| → (tm.runWith w (tm.initCfg z)).workTapes i p = none) ∧
    (tm.runWith w (tm.initCfg z)).output.length ≤ w.length := by
  suffices H : ∀ (w : List Bool) (c : Cfg k Bool S z) (s : ℕ),
      (∀ i, |c.workTapePos i| ≤ (s : ℤ)) →
      (∀ i (p : ℤ), (s : ℤ) < |p| → c.workTapes i p = none) →
      c.output.length ≤ s →
      (∀ i, |(tm.runWith w c).workTapePos i| ≤ ((s + w.length : ℕ) : ℤ)) ∧
      (∀ i (p : ℤ), ((s + w.length : ℕ) : ℤ) < |p| → (tm.runWith w c).workTapes i p = none) ∧
      (tm.runWith w c).output.length ≤ s + w.length by
    have h := H w (tm.initCfg z) 0
      (fun i => by rw [NDTM.initCfg_eq, Cfg.init_workTapePos]; simp)
      (fun i p _ => by rw [NDTM.initCfg_eq, Cfg.init_workTapes])
      (by rw [NDTM.initCfg_eq, Cfg.init_output]; simp)
    simpa only [Nat.zero_add] using h
  intro w
  induction w with
  | nil =>
    intro c s h1 h2 h3
    simp only [NDTM.runWith_nil, List.length_nil, Nat.add_zero]
    exact ⟨h1, h2, h3⟩
  | cons b w ih =>
    intro c s h1 h2 h3
    obtain ⟨g1, g2, g3⟩ := xr_window_stepWith tm b c s h1 h2 h3
    have := ih (tm.stepWith b c) (s + 1) g1 g2 g3
    rw [NDTM.runWith_cons]
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using this

/-- At an all-halting depth `L ≤ T`, acceptance within `L` and within `T` agree: one direction
is monotonicity, the other truncates an accepting word of length `T` at `L`. -/
private theorem xr_accepts_iff_of_halts (N : FinNDTM Bool) (z : List Bool) {L T : ℕ}
    (hL : N.tm.HaltsWithin z L) (hLT : L ≤ T) :
    N.AcceptsWithin z L ↔ N.AcceptsWithin z T := by
  refine ⟨fun h => h.mono hLT, fun h => ?_⟩
  obtain ⟨w, hw, hhalt, hout⟩ := FinNDTM.acceptsWithin_iff.mp h
  have htake : (w.take L).length = L := by rw [List.length_take, hw]; omega
  have hstop := NDTM.haltsWithin_iff.mp hL (w.take L) htake
  have hsplit : N.tm.runWith w (N.tm.initCfg z) = N.tm.runWith (w.take L) (N.tm.initCfg z) := by
    conv_lhs => rw [← List.take_append_drop L w]
    rw [NDTM.runWith_append, NDTM.runWith_of_halt _ hstop]
  rw [hsplit] at hout
  exact FinNDTM.acceptsWithin_iff.mpr ⟨w.take L, htake, hstop, hout⟩

/-- The first all-halting depth exists below any all-halting bound, is positive, and answers
as the bound does: the deepening terminates by depth `T`, never at depth `0`. -/
private theorem xr_first_depth (N : FinNDTM Bool) (z : List Bool) (T : ℕ)
    (hT : N.tm.HaltsWithin z T) :
    ∃ L, 0 < L ∧ L ≤ T ∧ N.tm.HaltsWithin z L ∧ (∀ L' < L, ¬ N.tm.HaltsWithin z L') ∧
      (N.AcceptsWithin z L ↔ N.AcceptsWithin z T) := by
  classical
  have hex : ∃ L, N.tm.HaltsWithin z L := ⟨T, hT⟩
  refine ⟨Nat.find hex, ?_, Nat.find_min' hex hT, Nat.find_spec hex,
    fun L' hL' => Nat.find_min hex hL', xr_accepts_iff_of_halts N z (Nat.find_spec hex)
      (Nat.find_min' hex hT)⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
  · exact absurd (h0 ▸ Nat.find_spec hex) (xr_not_haltsWithin_zero N z)
  · exact h0

/-- The ledger's shape, with two steps of slack for the dispatch and the answer:
`Σ_{L ≤ T} 2^L · A(L + 1) + 2 ≤ (A + 3)·2^{(A + 3)(T + 1)}`. -/
private theorem xr_ledger (A T : ℕ) :
    ∑ L ∈ Finset.range (T + 1), 2 ^ L * (A * (L + 1)) + 2 ≤
      (A + 3) * 2 ^ ((A + 3) * (T + 1)) := by
  have hterm : ∀ L ∈ Finset.range (T + 1), 2 ^ L * (A * (L + 1)) ≤ 2 ^ T * (A * (T + 1)) := by
    intro L hL
    rw [Finset.mem_range] at hL
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (by omega))
      (Nat.mul_le_mul_left A (by omega))
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range] at hsum
  change _ ≤ (T + 1) * (2 ^ T * (A * (T + 1))) at hsum
  have hlin : T + 1 ≤ 2 ^ (T + 1) := (Nat.lt_two_pow_self).le
  have h2 : 2 ^ T ≤ 2 ^ (T + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hpow : 2 ^ (T + 1) * 2 ^ (T + 1) * 2 ^ (T + 1) ≤ 2 ^ ((A + 3) * (T + 1)) := by
    rw [← pow_add, ← pow_add]
    exact Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hone : 1 ≤ 2 ^ ((A + 3) * (T + 1)) := Nat.one_le_two_pow
  calc ∑ L ∈ Finset.range (T + 1), 2 ^ L * (A * (L + 1)) + 2
      ≤ (T + 1) * (2 ^ T * (A * (T + 1))) + 2 := Nat.add_le_add_right hsum 2
    _ = A * ((T + 1) * 2 ^ T * (T + 1)) + 2 := by ring
    _ ≤ A * (2 ^ (T + 1) * 2 ^ (T + 1) * 2 ^ (T + 1)) + 2 :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_left A (Nat.mul_le_mul (Nat.mul_le_mul hlin h2) hlin)) 2
    _ ≤ A * 2 ^ ((A + 3) * (T + 1)) + 2 := Nat.add_le_add_right (Nat.mul_le_mul_left A hpow) 2
    _ ≤ (A + 3) * 2 ^ ((A + 3) * (T + 1)) := by nlinarith [hone]

/-! #### Translation of work tapes -/

/-- The configuration `c` with work tape `i` translated by `δ i`: cell `p` holds what cell
`p - δ i` held, and the head moves by `δ i`; the state, input head and output are `c`'s. -/
private def xr_shift {k : ℕ} {S : Type} {x : List Bool} (δ : Fin k → ℤ) (c : Cfg k Bool S x) :
    Cfg k Bool S x :=
  ⟨c.state, c.inputPos, fun i p => c.workTapes i (p - δ i), fun i => c.workTapePos i + δ i,
    c.output⟩

/-- Two configurations with the same input head read the same input symbol. -/
private theorem xr_inputSymbol_congr {k k' : ℕ} {S S' : Type} {x : List Bool}
    (c : Cfg k Bool S x) (c' : Cfg k' Bool S' x) (h : c.inputPos.val = c'.inputPos.val) :
    c.inputSymbol = c'.inputSymbol := by
  by_cases h0 : c.inputPos.val = 0
  · have hc : c.inputPos = 0 := by
      apply Fin.ext
      rw [h0]
      simp
    have hc' : c'.inputPos = 0 := by
      apply Fin.ext
      rw [← h, h0]
      simp
    rw [Cfg.inputSymbol_of_zero hc, Cfg.inputSymbol_of_zero hc']
  · by_cases hend : c.inputPos.val = x.length + 1
    · rw [Cfg.inputSymbol_of_end hend, Cfg.inputSymbol_of_end (by omega)]
    · have hlt : c.inputPos.val - 1 < x.length := by have := c.inputPos.isLt; omega
      rw [inputSymbolInner (c.inputPos.val - 1) (by omega) hlt,
        inputSymbolInner (c.inputPos.val - 1) (by omega) hlt]

/-- A translated configuration reads the same work symbols. -/
private theorem xr_workTapeSymbols_shift {k : ℕ} {S : Type} {x : List Bool} (δ : Fin k → ℤ)
    (c : Cfg k Bool S x) : (xr_shift δ c).workTapeSymbols = c.workTapeSymbols := by
  funext i
  rw [Cfg.workTapeSymbols_eq, Cfg.workTapeSymbols_eq]
  show c.workTapes i (c.workTapePos i + δ i - δ i) = _
  rw [add_sub_cancel_right]

/-- Applying an action commutes with translation. -/
private theorem xr_apply_shift {k : ℕ} {S : Type} {x : List Bool} (δ : Fin k → ℤ)
    (a : Action k Bool S) (c : Cfg k Bool S x) :
    a.apply (xr_shift δ c) = xr_shift δ (a.apply c) := by
  apply Cfg.ext
  · show (a.apply (xr_shift δ c)).state = (a.apply c).state
    rw [Action.apply_state, Action.apply_state]
  · show (a.apply (xr_shift δ c)).inputPos = (a.apply c).inputPos
    rw [Action.apply_inputPos, Action.apply_inputPos]
    rfl
  · funext i p
    show (a.apply (xr_shift δ c)).workTapes i p = (a.apply c).workTapes i (p - δ i)
    rw [Action.apply_workTapes, Action.apply_workTapes, xr_workTapeSymbols_shift]
    show Function.update (fun p => c.workTapes i (p - δ i)) (c.workTapePos i + δ i) _ p = _
    by_cases hp : p = c.workTapePos i + δ i
    · subst hp
      rw [Function.update_self, add_sub_cancel_right, Function.update_self]
    · rw [Function.update_of_ne hp, Function.update_of_ne (by omega)]
  · funext i
    show (a.apply (xr_shift δ c)).workTapePos i = (a.apply c).workTapePos i + δ i
    rw [Action.apply_workTapePos, Action.apply_workTapePos]
    show c.workTapePos i + δ i + _ = c.workTapePos i + _ + δ i
    ring
  · show (a.apply (xr_shift δ c)).output = (a.apply c).output
    rw [Action.apply_output, Action.apply_output]
    rfl

/-- One nondeterministic step commutes with translation. -/
private theorem xr_stepWith_shift {k : ℕ} {S : Type} {x : List Bool} (N : NDTM k Bool S)
    (δ : Fin k → ℤ) (b : Bool) (c : Cfg k Bool S x) :
    N.stepWith b (xr_shift δ c) = xr_shift δ (N.stepWith b c) := by
  cases hq : c.state with
  | none =>
    rw [NDTM.stepWith_of_halt hq, NDTM.stepWith_of_halt (show (xr_shift δ c).state = none from hq)]
  | some q =>
    rw [NDTM.stepWith_of_some hq,
      NDTM.stepWith_of_some (show (xr_shift δ c).state = some q from hq),
      xr_inputSymbol_congr (xr_shift δ c) c rfl, xr_workTapeSymbols_shift, xr_apply_shift]

/-- A branch commutes with translation: the branch along `w` from a translated configuration
is the translated branch. -/
private theorem xr_runWith_shift {k : ℕ} {S : Type} {x : List Bool} (N : NDTM k Bool S)
    (δ : Fin k → ℤ) (w : List Bool) (c : Cfg k Bool S x) :
    N.runWith w (xr_shift δ c) = xr_shift δ (N.runWith w c) := by
  induction w generalizing c with
  | nil => rw [NDTM.runWith_nil, NDTM.runWith_nil]
  | cons b w ih => rw [NDTM.runWith_cons, NDTM.runWith_cons, xr_stepWith_shift, ih]

/-! #### The first arrival at a stationary anchor -/

/-- A configuration fixed by one step is fixed by every run. -/
private theorem xr_runFrom_fixed {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S)
    (d : Cfg k Bool S x) (hd : tm.step d = d) (n : ℕ) : tm.runFrom d n = d := by
  induction n with
  | zero => exact MultiTapeTM.runFrom_zero
  | succ n ih => rw [MultiTapeTM.runFrom_succ_eq_step', ih, hd]

open MultiTapeTM in
/-- One step of a run. -/
private theorem xr_runFrom_one {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S)
    (d : Cfg k Bool S x) : tm.runFrom d 1 = tm.step d := by
  rw [runFrom_succ_eq_step', runFrom_zero]

/-- Two steps of a run. -/
private theorem xr_runFrom_two {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S)
    (d : Cfg k Bool S x) : tm.runFrom d 2 = tm.step (tm.step d) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, MultiTapeTM.runFrom_add, xr_runFrom_one, xr_runFrom_one]

/-- **The first arrival at a stationary anchor.** If a run reaches `c'` in state `a` at time `T`
and `a` is stationary, the first time the state is `a` is at most `T`, reaches `c'` too, and no
earlier state is `a`: the phase host's guard, for free, from an exact-time run lemma. -/
private theorem xr_firstArrival {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S)
    (a : S) (hstat : ∀ d : Cfg k Bool S x, d.state = some a → tm.step d = d)
    {c c' : Cfg k Bool S x} {T : ℕ} (h : tm.runFrom c T = c') (hc' : c'.state = some a) :
    ∃ T' ≤ T, tm.runFrom c T' = c' ∧ ∀ u < T', (tm.runFrom c u).state ≠ some a := by
  classical
  have hT' : (tm.runFrom c T).state = some a := by rw [h]; exact hc'
  have hex : ∃ u, (tm.runFrom c u).state = some a := ⟨T, hT'⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hT', ?_, fun u hu => Nat.find_min hex hu⟩
  have hsplit : tm.runFrom c T = tm.runFrom (tm.runFrom c (Nat.find hex)) (T - Nat.find hex) := by
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_cancel' (Nat.find_min' hex hT')]
  rw [xr_runFrom_fixed tm _ (hstat _ (Nat.find_spec hex))] at hsplit
  exact hsplit.symm.trans h
/-! #### The leaf rows

This file's own rows, on `Bool` tapes, each exiting at a stationary anchor `done b`: the
ruler-driven pass (the window clear's engine), the head rewind to a word's origin, the extension
of a word by one `false`, the capture test (which also clears the captured output), the input
rewind and the answer. Their run lemmas give exact times and exact configurations; the phase
host's guard comes from `xr_firstArrival`. -/

/-- The control of the leaf rows. -/
private inductive xr_St where
  | start
  | run
  | aux
  | back (b : Bool)
  | done (b : Bool)
  deriving DecidableEq, Fintype

/-- A silent action: no input move and no emission. -/
private def xr_act {K : ℕ} (mv : Fin K → Option (Option Bool) × SignType) (q : Option xr_St) :
    Action K Bool xr_St := ⟨0, mv, none, q⟩

/-- Write `wr` and move `m` on tape `r` only. -/
private def xr_mv1 {K : ℕ} (r : Fin K) (wr : Option (Option Bool)) (m : SignType) :
    Fin K → Option (Option Bool) × SignType :=
  fun i => if i = r then (wr, m) else (none, 0)

/-- Write `wr` and move `m` on tape `j`, move `m'` on tape `r`. -/
private def xr_mv2 {K : ℕ} (j r : Fin K) (wr : Option (Option Bool)) (m m' : SignType) :
    Fin K → Option (Option Bool) × SignType :=
  fun i => if i = j then (wr, m) else if i = r then (none, m') else (none, 0)

/-- The stationary action at `q`. -/
private def xr_stay {K : ℕ} (q : xr_St) : Action K Bool xr_St :=
  xr_act (fun _ => (none, 0)) (some q)

private theorem xr_cast_pos : ((SignType.pos : SignType) : ℤ) = 1 := rfl
private theorem xr_cast_neg : ((SignType.neg : SignType) : ℤ) = -1 := rfl

/-- A silent action's effect: the state, the writes under the heads, the head moves. -/
private theorem xr_act_apply {K : ℕ} {x : List Bool}
    (mv : Fin K → Option (Option Bool) × SignType) (q : Option xr_St) (d : Cfg K Bool xr_St x) :
    (xr_act mv q).apply d =
      ⟨q, d.inputPos,
        fun i => Function.update (d.workTapes i) (d.workTapePos i)
          ((mv i).1.getD (d.workTapes i (d.workTapePos i))),
        fun i => d.workTapePos i + ((mv i).2 : ℤ), d.output⟩ := by
  apply Cfg.ext
  · exact Action.apply_state _ _
  · exact (Action.apply_inputPos _ _).trans (moveInputPos_zero _)
  · funext i
    rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
    rfl
  · funext i
    exact Action.apply_workTapePos _ _ _
  · exact (Action.apply_output _ _).trans (List.append_nil _)

/-- A one-tape write-and-move. -/
private theorem xr_mv1_apply {K : ℕ} {x : List Bool} (r : Fin K) (wr : Option (Option Bool))
    (m : SignType) (q : Option xr_St) (d : Cfg K Bool xr_St x) :
    (xr_act (xr_mv1 r wr m) q).apply d =
      ⟨q, d.inputPos,
        Function.update d.workTapes r (Function.update (d.workTapes r) (d.workTapePos r)
          (wr.getD (d.workTapes r (d.workTapePos r)))),
        Function.update d.workTapePos r (d.workTapePos r + (m : ℤ)), d.output⟩ := by
  rw [xr_act_apply]
  congr 1
  · funext i
    by_cases hi : i = r
    · rw [hi]
      simp [xr_mv1]
    · simp [xr_mv1, hi]
  · funext i
    by_cases hi : i = r
    · rw [hi]
      simp [xr_mv1]
    · simp [xr_mv1, hi]

/-- A one-tape move without a write. -/
private theorem xr_mv1_apply_none {K : ℕ} {x : List Bool} (r : Fin K) (m : SignType)
    (q : Option xr_St) (d : Cfg K Bool xr_St x) :
    (xr_act (xr_mv1 r none m) q).apply d =
      ⟨q, d.inputPos, d.workTapes,
        Function.update d.workTapePos r (d.workTapePos r + (m : ℤ)), d.output⟩ := by
  rw [xr_mv1_apply]
  congr 1
  simp

/-- A two-tape move: a write-and-move on `j`, a move on `r`. -/
private theorem xr_mv2_apply {K : ℕ} {x : List Bool} (j r : Fin K) (hjr : j ≠ r)
    (wr : Option (Option Bool)) (m m' : SignType) (q : Option xr_St) (d : Cfg K Bool xr_St x) :
    (xr_act (xr_mv2 j r wr m m') q).apply d =
      ⟨q, d.inputPos,
        Function.update d.workTapes j (Function.update (d.workTapes j) (d.workTapePos j)
          (wr.getD (d.workTapes j (d.workTapePos j)))),
        fun i => if i = j then d.workTapePos j + (m : ℤ)
          else if i = r then d.workTapePos r + (m' : ℤ) else d.workTapePos i, d.output⟩ := by
  rw [xr_act_apply]
  congr 1
  · funext i
    by_cases hij : i = j
    · rw [hij]
      simp [xr_mv2]
    · by_cases hir : i = r
      · rw [hir]
        simp [xr_mv2, Ne.symm hjr]
      · simp [xr_mv2, hij, hir]
  · funext i
    by_cases hij : i = j
    · rw [hij]
      simp [xr_mv2]
    · by_cases hir : i = r
      · rw [hir]
        simp [xr_mv2, Ne.symm hjr]
      · simp [xr_mv2, hij, hir]

/-- A state whose table is the stationary action fixes every configuration in that state. -/
private theorem xr_stay_step {K : ℕ} {x : List Bool} (tm : MultiTapeTM K Bool xr_St) (q : xr_St)
    (htr : ∀ inp w, tm.tr q inp w = xr_stay q) (d : Cfg K Bool xr_St x) (hd : d.state = some q) :
    tm.step d = d := by
  rw [MultiTapeTM.step_of_some hd, htr, xr_stay, xr_act_apply]
  apply Cfg.ext
  · exact hd.symm
  · rfl
  · funext i
    simp
  · funext i
    simp
  · rfl

/-- **The return pass** of the leaf rows. From `back b` with the head on the rightmost of the `m`
non-blank cells `o, …, o + m - 1` and a blank at `o - 1`, `m + 1` steps write `wb` on those `m`
cells, return the head to `o`, and stop at `done b`. -/
private theorem xr_back_run {K : ℕ} {x : List Bool} (tm : MultiTapeTM K Bool xr_St) (r : Fin K)
    (wb : Option (Option Bool))
    (hsome : ∀ (b : Bool) inp w s, w r = some s →
      tm.tr (.back b) inp w = xr_act (xr_mv1 r wb SignType.neg) (some (.back b)))
    (hnone : ∀ (b : Bool) inp w, w r = none →
      tm.tr (.back b) inp w = xr_act (xr_mv1 r none SignType.pos) (some (.done b)))
    (b : Bool) (o : ℤ) (m : ℕ) :
    ∀ d : Cfg K Bool xr_St x, d.state = some (.back b) → d.workTapePos r = o + m - 1 →
      (∀ i : ℕ, i < m → d.workTapes r (o + i) ≠ none) → d.workTapes r (o - 1) = none →
      tm.runFrom d (m + 1) =
        ⟨some (.done b), d.inputPos,
          Function.update d.workTapes r
            (fun p => if o ≤ p ∧ p < o + m then wb.getD (d.workTapes r p) else d.workTapes r p),
          Function.update d.workTapePos r o, d.output⟩ := by
  induction m with
  | zero =>
    intro d hd hpos _ hleft
    have hread : d.workTapeSymbols r = none := by
      rw [Cfg.workTapeSymbols_eq, hpos]
      simpa using hleft
    rw [show (0 : ℕ) + 1 = 1 from rfl, xr_runFrom_one, MultiTapeTM.step_of_some hd,
      hnone b _ _ hread, xr_mv1_apply_none]
    congr 1
    · symm
      rw [Function.update_eq_self_iff]
      funext p
      split_ifs with h
      · exfalso
        push_cast at h
        omega
      · rfl
    · rw [hpos, xr_cast_pos]
      congr 1
      push_cast
      ring
  | succ m ih =>
    intro d hd hpos hcells hleft
    have hcur : d.workTapes r (o + m) ≠ none := hcells m (by omega)
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hcur
    have hpos' : d.workTapePos r = o + m := by rw [hpos]; push_cast; ring
    have hread : d.workTapeSymbols r = some s := by
      rw [Cfg.workTapeSymbols_eq, hpos', hs]
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.step_of_some hd, hsome b _ _ s hread,
      xr_mv1_apply, hpos', xr_cast_neg]
    have hX : ∀ p : ℤ, p ≠ o + m →
        Function.update (d.workTapes r) (o + m) (wb.getD (d.workTapes r (o + m))) p =
          d.workTapes r p := fun p hp => Function.update_of_ne hp _ _
    rw [ih _ rfl ?_ ?_ ?_]
    · dsimp only
      simp only [Function.update_self, Function.update_idem]
      congr 1
      refine congrArg (Function.update d.workTapes r) (funext fun p => ?_)
      dsimp only
      by_cases hp : p = o + m
      · rw [hp, Function.update_self, if_neg (fun h => lt_irrefl _ h.2),
          if_pos ⟨by omega, by push_cast; omega⟩]
      · rw [hX p hp]
        by_cases h1 : o ≤ p ∧ p < o + m
        · rw [if_pos h1, if_pos ⟨h1.1, by push_cast; omega⟩]
        · rw [if_neg h1, if_neg (by push_cast at h1 ⊢; omega)]
    · dsimp only
      rw [Function.update_self]
      omega
    · intro i hi
      dsimp only
      rw [Function.update_self, hX _ (by omega)]
      exact hcells i (by omega)
    · dsimp only
      rw [Function.update_self, hX _ (by omega)]
      exact hleft

/-- **The forward scan** of the leaf rows: from `run` with the head at `o` and `m` non-blank
cells ahead, `m` steps move the head to `o + m` and change nothing else. -/
private theorem xr_fwd_run {K : ℕ} {x : List Bool} (tm : MultiTapeTM K Bool xr_St) (r : Fin K)
    (hsome : ∀ inp w s, w r = some s →
      tm.tr .run inp w = xr_act (xr_mv1 r none SignType.pos) (some .run))
    (m : ℕ) :
    ∀ (o : ℤ) (d : Cfg K Bool xr_St x), d.state = some .run → d.workTapePos r = o →
      (∀ i : ℕ, i < m → d.workTapes r (o + i) ≠ none) →
      tm.runFrom d m =
        ⟨some .run, d.inputPos, d.workTapes, Function.update d.workTapePos r (o + m),
          d.output⟩ := by
  induction m with
  | zero =>
    intro o d hd hpos _
    rw [MultiTapeTM.runFrom_zero]
    apply Cfg.ext
    · exact hd
    · rfl
    · rfl
    · funext i
      dsimp only
      by_cases hi : i = r
      · rw [hi, Function.update_self, hpos]
        simp
      · rw [Function.update_of_ne hi]
    · rfl
  | succ m ih =>
    intro o d hd hpos hcells
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp (hcells 0 (by omega))
    have hread : d.workTapeSymbols r = some s := by
      rw [Cfg.workTapeSymbols_eq, hpos]
      simpa using hs
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.step_of_some hd, hsome _ _ s hread,
      xr_mv1_apply_none, hpos, xr_cast_pos]
    rw [ih (o + 1) _ rfl (by dsimp only; rw [Function.update_self]) ?_]
    · dsimp only
      rw [Function.update_idem]
      congr 2
      push_cast
      ring
    · intro i hi
      dsimp only
      have := hcells (i + 1) (by omega)
      push_cast at this ⊢
      convert this using 2
      ring

/-- **The rewind**: one step left, then left while reading a symbol, then one step right at the
blank. -/
private def xr_rewindTM (K : ℕ) (r : Fin K) : MultiTapeTM K Bool xr_St where
  q₀ := .start
  tr := fun q _ w =>
    match q with
    | .start => xr_act (xr_mv1 r none SignType.neg) (some (.back true))
    | .back b =>
      match w r with
      | some _ => xr_act (xr_mv1 r none SignType.neg) (some (.back b))
      | none => xr_act (xr_mv1 r none SignType.pos) (some (.done b))
    | q => xr_stay q

/-- From any head position `p₀ ≤ |u|` on the word `u` at the origin, the rewind returns the head
to `0` in `p₀ + 2` steps, changes nothing else, and stops at `done true`. -/
private theorem xr_rewindTM_run {K : ℕ} {x : List Bool} (r : Fin K) (u : List Bool) (p₀ : ℕ)
    (hp₀ : p₀ ≤ u.length) (d : Cfg K Bool xr_St x) (hd : d.state = some .start)
    (hr : d.workTapes r = FinTM.bufferTape u) (hpos : d.workTapePos r = p₀) :
    (xr_rewindTM K r).runFrom d (p₀ + 2) =
      ⟨some (.done true), d.inputPos, d.workTapes, Function.update d.workTapePos r 0,
        d.output⟩ := by
  rw [show p₀ + 2 = (p₀ + 1) + 1 from rfl, MultiTapeTM.runFrom_succ_eq_step,
    MultiTapeTM.step_of_some hd,
    show (xr_rewindTM K r).tr .start _ _ =
      xr_act (xr_mv1 r none SignType.neg) (some (.back true)) from rfl,
    xr_mv1_apply_none, hpos, xr_cast_neg]
  rw [xr_back_run (xr_rewindTM K r) r none
    (fun b inp w s hs => by simp [xr_rewindTM, hs]) (fun b inp w hw => by simp [xr_rewindTM, hw])
    true 0 p₀ _ rfl ?_ ?_ ?_]
  · dsimp only
    rw [Function.update_idem]
    congr 1
    rw [Function.update_eq_self_iff]
    funext p
    simp
  · dsimp only
    rw [Function.update_self]
    ring
  · intro i hi
    dsimp only
    rw [zero_add, hr, FinTM.bufferTape_nat, ne_eq, List.getElem?_eq_none_iff]
    omega
  · dsimp only
    rw [hr]
    simp

/-- **The extension**: right while reading a symbol, write `false` at the blank and turn, return
to the origin: the word grows by one `false`. -/
private def xr_extendTM (K : ℕ) (r : Fin K) : MultiTapeTM K Bool xr_St where
  q₀ := .run
  tr := fun q _ w =>
    match q with
    | .run =>
      match w r with
      | some _ => xr_act (xr_mv1 r none SignType.pos) (some .run)
      | none => xr_act (xr_mv1 r (some (some false)) SignType.neg) (some (.back true))
    | .back b =>
      match w r with
      | some _ => xr_act (xr_mv1 r none SignType.neg) (some (.back b))
      | none => xr_act (xr_mv1 r none SignType.pos) (some (.done b))
    | q => xr_stay q

/-- From the origin of the word `u`, the extension writes `u ++ [false]` in `2|u| + 2` steps,
returns the head to `0`, changes nothing else, and stops at `done true`. -/
private theorem xr_extendTM_run {K : ℕ} {x : List Bool} (r : Fin K) (u : List Bool)
    (d : Cfg K Bool xr_St x) (hd : d.state = some .run)
    (hr : d.workTapes r = FinTM.bufferTape u) (hpos : d.workTapePos r = 0) :
    (xr_extendTM K r).runFrom d (2 * u.length + 2) =
      ⟨some (.done true), d.inputPos,
        Function.update d.workTapes r (FinTM.bufferTape (u ++ [false])),
        Function.update d.workTapePos r 0, d.output⟩ := by
  have hcells : ∀ i : ℕ, i < u.length → d.workTapes r ((0 : ℤ) + i) ≠ none := by
    intro i hi
    rw [zero_add, hr, FinTM.bufferTape_nat, ne_eq, List.getElem?_eq_none_iff]
    omega
  have h1 : (xr_extendTM K r).runFrom d u.length = ⟨some .run, d.inputPos, d.workTapes,
      Function.update d.workTapePos r (u.length : ℤ), d.output⟩ := by
    rw [xr_fwd_run (xr_extendTM K r) r (fun inp w s hs => by simp [xr_extendTM, hs])
      u.length 0 d hd hpos hcells, zero_add]
  have hend : (⟨some .run, d.inputPos, d.workTapes,
      Function.update d.workTapePos r (u.length : ℤ), d.output⟩ :
      Cfg K Bool xr_St x).workTapeSymbols r = none := by
    rw [Cfg.workTapeSymbols_eq]
    dsimp only
    rw [Function.update_self, hr, FinTM.bufferTape_nat]
    simp
  have h2 : (xr_extendTM K r).step ⟨some .run, d.inputPos, d.workTapes,
      Function.update d.workTapePos r (u.length : ℤ), d.output⟩ =
      ⟨some (.back true), d.inputPos,
        Function.update d.workTapes r (FinTM.bufferTape (u ++ [false])),
        Function.update d.workTapePos r ((u.length : ℤ) + -1), d.output⟩ := by
    rw [MultiTapeTM.step_of_some rfl,
      show (xr_extendTM K r).tr .run _ _ =
        xr_act (xr_mv1 r (some (some false)) SignType.neg) (some (.back true)) by
          simp only [xr_extendTM]
          rw [hend],
      xr_mv1_apply, xr_cast_neg]
    dsimp only
    rw [Function.update_self, Function.update_idem, Option.getD_some, hr,
      ← FinTM.bufferTape_append]
  have h3 := xr_back_run (xr_extendTM K r) r none
    (fun b inp w s hs => by simp [xr_extendTM, hs]) (fun b inp w hw => by simp [xr_extendTM, hw])
    true 0 u.length
    ⟨some (.back true), d.inputPos, Function.update d.workTapes r (FinTM.bufferTape (u ++ [false])),
      Function.update d.workTapePos r ((u.length : ℤ) + -1), d.output⟩ rfl
    (by dsimp only; rw [Function.update_self]; ring)
    (by
      intro i hi
      dsimp only
      rw [Function.update_self, zero_add, FinTM.bufferTape_nat, ne_eq, List.getElem?_eq_none_iff]
      simp only [List.length_append, List.length_singleton]
      omega)
    (by dsimp only; rw [Function.update_self]; simp)
  have hsplit : (xr_extendTM K r).runFrom d (2 * u.length + 2) =
      (xr_extendTM K r).runFrom ((xr_extendTM K r).step ((xr_extendTM K r).runFrom d u.length))
        (u.length + 1) := by
    rw [show 2 * u.length + 2 = (u.length + 1) + (u.length + 1) by ring,
      MultiTapeTM.runFrom_add, ← MultiTapeTM.runFrom_succ_eq_step']
  rw [hsplit, h1, h2, h3]
  dsimp only
  simp only [Function.update_self, Function.update_idem]
  congr 1
  refine congrArg (Function.update d.workTapes r) (funext fun p => ?_)
  dsimp only
  simp only [Option.getD_none, ite_self]

/-! #### Buffer-tape facts needed by the rows (from the published equations only) -/

/-- A stored word is blank at every negative cell. -/
private theorem xr_bufferTape_neg (v : List Bool) (p : ℤ) (hp : p < 0) :
    FinTM.bufferTape v p = none := by
  induction v using List.reverseRecOn with
  | nil => rw [FinTM.bufferTape_nil]
  | append_singleton L b ih =>
    rw [FinTM.bufferTape_append, Function.update_of_ne (by omega)]
    exact ih

/-- A stored word is blank at and beyond its length. -/
private theorem xr_bufferTape_ge (v : List Bool) (p : ℤ) (hp : (v.length : ℤ) ≤ p) :
    FinTM.bufferTape v p = none := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, by omega⟩
  rw [FinTM.bufferTape_nat, List.getElem?_eq_none_iff]
  omega

/-- A stored word is blank exactly off `[0, |v|)`. -/
private theorem xr_bufferTape_eq_none_iff (v : List Bool) (p : ℤ) :
    FinTM.bufferTape v p = none ↔ p < 0 ∨ (v.length : ℤ) ≤ p := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, by omega⟩
    rw [FinTM.bufferTape_nat, List.getElem?_eq_none_iff] at h
    omega
  · rintro (h | h)
    · exact xr_bufferTape_neg v p h
    · exact xr_bufferTape_ge v p h

/-- A stored word is non-blank on `[0, |v|)`. -/
private theorem xr_bufferTape_ne_none (v : List Bool) (i : ℕ) (hi : i < v.length) :
    FinTM.bufferTape v i ≠ none := by
  rw [ne_eq, xr_bufferTape_eq_none_iff]
  omega

/-- Blanking the last symbol of a stored word stores its prefix. -/
private theorem xr_bufferTape_pop (L : List Bool) (b : Bool) :
    Function.update (FinTM.bufferTape (L ++ [b])) (L.length : ℤ) none = FinTM.bufferTape L := by
  rw [FinTM.bufferTape_append, Function.update_idem, Function.update_eq_self_iff,
    FinTM.bufferTape_nat]
  exact (List.getElem?_eq_none_iff.mpr le_rfl).symm

/-- The return pass over a stored word with the blanking write clears it entirely. -/
private theorem xr_clear_fun (v : List Bool) :
    (fun p : ℤ => if 0 ≤ p ∧ p < 0 + (v.length : ℤ) then (some none).getD (FinTM.bufferTape v p)
      else FinTM.bufferTape v p) = fun _ => none := by
  funext p
  split_ifs with h
  · rfl
  · rw [xr_bufferTape_eq_none_iff]
    omega

/-! #### The pass, the capture test, the input rewind and the answer -/

/-- **The pass** (the window clear's engine). While the ruler tape `r` reads a symbol, blank the
cell under head `j`, move `j` by `dir` and `r` right; at the ruler's blank, blank once more under
`j` without moving it and start the ruler's return; return the ruler head to its origin. -/
private def xr_passTM (K : ℕ) (j r : Fin K) (dir : SignType) : MultiTapeTM K Bool xr_St where
  q₀ := .run
  tr := fun q _ w =>
    match q with
    | .run =>
      match w r with
      | some _ => xr_act (xr_mv2 j r (some none) dir SignType.pos) (some .run)
      | none => xr_act (xr_mv2 j r (some none) 0 SignType.neg) (some (.back true))
    | .back b =>
      match w r with
      | some _ => xr_act (xr_mv1 r none SignType.neg) (some (.back b))
      | none => xr_act (xr_mv1 r none SignType.pos) (some (.done b))
    | q => xr_stay q

/-- The pass's forward phase: after `m ≤ |u|` steps, head `j` has moved `m` cells along `dir`,
blanking the cells it left, and the ruler head is at `m`. -/
private theorem xr_pass_fwd {K : ℕ} {x : List Bool} (j r : Fin K) (hjr : j ≠ r) (dir : SignType)
    (u : List Bool) (d : Cfg K Bool xr_St x) (hd : d.state = some .run)
    (hr : d.workTapes r = FinTM.bufferTape u) (hpos : d.workTapePos r = 0) (m : ℕ)
    (hm : m ≤ u.length) :
    ∃ f : ℤ → Option Bool,
      (xr_passTM K j r dir).runFrom d m =
        ⟨some .run, d.inputPos, Function.update d.workTapes j f,
          fun i => if i = j then d.workTapePos j + m * (dir : ℤ)
            else if i = r then (m : ℤ) else d.workTapePos i, d.output⟩ ∧
      (∀ p : ℤ, (∃ i : ℕ, i < m ∧ p = d.workTapePos j + i * (dir : ℤ)) → f p = none) ∧
      (∀ p : ℤ, (∀ i : ℕ, i < m → p ≠ d.workTapePos j + i * (dir : ℤ)) →
        f p = d.workTapes j p) := by
  induction m with
  | zero =>
    refine ⟨d.workTapes j, ?_, fun p ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i), fun p _ => rfl⟩
    rw [MultiTapeTM.runFrom_zero]
    apply Cfg.ext
    · exact hd
    · rfl
    · exact (Function.update_eq_self _ _).symm
    · funext i
      dsimp only
      by_cases hij : i = j
      · rw [if_pos hij, hij]
        simp
      · rw [if_neg hij]
        by_cases hir : i = r
        · rw [if_pos hir, hir, hpos]
          simp
        · rw [if_neg hir]
    · rfl
  | succ m ih =>
    obtain ⟨f, hrun, hblank, hkeep⟩ := ih (by omega)
    have hread : (⟨some .run, d.inputPos, Function.update d.workTapes j f,
        fun i => if i = j then d.workTapePos j + m * (dir : ℤ)
          else if i = r then (m : ℤ) else d.workTapePos i, d.output⟩ :
        Cfg K Bool xr_St x).workTapeSymbols r = some (u[m]'(by omega)) := by
      rw [Cfg.workTapeSymbols_eq]
      dsimp only
      rw [if_neg (Ne.symm hjr), if_pos rfl, Function.update_of_ne (Ne.symm hjr), hr,
        FinTM.bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    refine ⟨Function.update f (d.workTapePos j + m * (dir : ℤ)) none, ?_, ?_, ?_⟩
    · rw [MultiTapeTM.runFrom_succ_eq_step', hrun, MultiTapeTM.step_of_some rfl,
        show (xr_passTM K j r dir).tr .run _ _ =
          xr_act (xr_mv2 j r (some none) dir SignType.pos) (some .run) by
            simp only [xr_passTM]
            rw [hread],
        xr_mv2_apply j r hjr]
      dsimp only
      simp only [Function.update_self, Function.update_idem, Option.getD_some,
        if_neg (Ne.symm hjr), xr_cast_pos, ite_true]
      congr 1
      funext i
      by_cases hij : i = j
      · simp only [if_pos hij]
        push_cast
        ring
      · by_cases hir : i = r
        · simp only [if_neg hij, if_pos hir]
          push_cast
          ring
        · simp only [if_neg hij, if_neg hir]
    · rintro p ⟨i, hi, rfl⟩
      by_cases hp : d.workTapePos j + i * (dir : ℤ) = d.workTapePos j + m * (dir : ℤ)
      · rw [hp, Function.update_self]
      · rw [Function.update_of_ne hp]
        refine hblank _ ⟨i, ?_, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact h
        · exact absurd (by rw [h]) hp
    · intro p hp
      rw [Function.update_of_ne (hp m (by omega))]
      exact hkeep p (fun i hi => hp i (by omega))

/-- **The pass's contract.** From the origin of the ruler word `u`, `2|u| + 2` steps move head `j`
by `|u|` cells along `dir`, blank the `|u| + 1` cells it visited, return the ruler head to `0`,
change nothing else, and stop at `done true`. -/
private theorem xr_passTM_run {K : ℕ} {x : List Bool} (j r : Fin K) (hjr : j ≠ r) (dir : SignType)
    (u : List Bool) (d : Cfg K Bool xr_St x) (hd : d.state = some .run)
    (hr : d.workTapes r = FinTM.bufferTape u) (hpos : d.workTapePos r = 0) :
    ∃ f : ℤ → Option Bool,
      (xr_passTM K j r dir).runFrom d (2 * u.length + 2) =
        ⟨some (.done true), d.inputPos, Function.update d.workTapes j f,
          Function.update d.workTapePos j (d.workTapePos j + u.length * (dir : ℤ)), d.output⟩ ∧
      (∀ p : ℤ, (∃ i : ℕ, i ≤ u.length ∧ p = d.workTapePos j + i * (dir : ℤ)) → f p = none) ∧
      (∀ p : ℤ, (∀ i : ℕ, i ≤ u.length → p ≠ d.workTapePos j + i * (dir : ℤ)) →
        f p = d.workTapes j p) := by
  obtain ⟨f, hrun, hblank, hkeep⟩ := xr_pass_fwd j r hjr dir u d hd hr hpos u.length le_rfl
  set c₁ : Cfg K Bool xr_St x := ⟨some .run, d.inputPos, Function.update d.workTapes j f,
    fun i => if i = j then d.workTapePos j + u.length * (dir : ℤ)
      else if i = r then (u.length : ℤ) else d.workTapePos i, d.output⟩ with hc₁
  have hread : c₁.workTapeSymbols r = none := by
    rw [Cfg.workTapeSymbols_eq, hc₁]
    dsimp only
    rw [if_neg (Ne.symm hjr), if_pos rfl, Function.update_of_ne (Ne.symm hjr), hr,
      FinTM.bufferTape_nat, List.getElem?_eq_none_iff]
  set f' : ℤ → Option Bool := Function.update f (d.workTapePos j + u.length * (dir : ℤ)) none
    with hf'
  have h2 : (xr_passTM K j r dir).step c₁ =
      ⟨some (.back true), d.inputPos, Function.update d.workTapes j f',
        fun i => if i = j then d.workTapePos j + u.length * (dir : ℤ)
          else if i = r then (u.length : ℤ) + -1 else d.workTapePos i, d.output⟩ := by
    rw [MultiTapeTM.step_of_some rfl,
      show (xr_passTM K j r dir).tr .run _ _ =
        xr_act (xr_mv2 j r (some none) 0 SignType.neg) (some (.back true)) by
          simp only [xr_passTM]
          rw [hread],
      xr_mv2_apply j r hjr, hc₁]
    dsimp only
    simp only [Function.update_self, Function.update_idem, Option.getD_some,
      if_neg (Ne.symm hjr), SignType.coe_zero, add_zero, ite_true]
    congr 1
    funext i
    by_cases hij : i = j
    · simp [hij]
    · by_cases hir : i = r
      · simp [hir]
      · simp [hij, hir]
  have h3 := xr_back_run (xr_passTM K j r dir) r none
    (fun b inp w s hs => by simp [xr_passTM, hs]) (fun b inp w hw => by simp [xr_passTM, hw])
    true 0 u.length
    ⟨some (.back true), d.inputPos, Function.update d.workTapes j f',
      fun i => if i = j then d.workTapePos j + u.length * (dir : ℤ)
        else if i = r then (u.length : ℤ) + -1 else d.workTapePos i, d.output⟩ rfl
    (by dsimp only; rw [if_neg (Ne.symm hjr), if_pos rfl]; ring)
    (by
      intro i hi
      dsimp only
      rw [Function.update_of_ne (Ne.symm hjr), zero_add, hr]
      exact xr_bufferTape_ne_none u i hi)
    (by
      dsimp only
      rw [Function.update_of_ne (Ne.symm hjr), hr]
      exact xr_bufferTape_neg u _ (by omega))
  refine ⟨f', ?_, ?_, ?_⟩
  · have hsplit : (xr_passTM K j r dir).runFrom d (2 * u.length + 2) =
        (xr_passTM K j r dir).runFrom
          ((xr_passTM K j r dir).step ((xr_passTM K j r dir).runFrom d u.length))
          (u.length + 1) := by
      rw [show 2 * u.length + 2 = (u.length + 1) + (u.length + 1) by ring,
        MultiTapeTM.runFrom_add, ← MultiTapeTM.runFrom_succ_eq_step']
    rw [hsplit, hrun, h2, h3]
    dsimp only
    congr 1
    · have hG : Function.update (Function.update d.workTapes j f') r
          (fun p => if 0 ≤ p ∧ p < 0 + (u.length : ℤ)
            then none.getD (Function.update d.workTapes j f' r p)
            else Function.update d.workTapes j f' r p) = Function.update d.workTapes j f' := by
        rw [Function.update_eq_self_iff, Function.update_of_ne (Ne.symm hjr)]
        funext p
        simp only [Option.getD_none, ite_self]
      exact hG
    · funext i
      by_cases hij : i = j
      · rw [hij, Function.update_of_ne hjr, if_pos rfl, Function.update_self]
      · by_cases hir : i = r
        · rw [hir, Function.update_self, Function.update_of_ne (Ne.symm hjr), hpos]
        · rw [Function.update_of_ne hir, if_neg hij, if_neg hir, Function.update_of_ne hij]
  · rintro p ⟨i, hi, rfl⟩
    by_cases hp : d.workTapePos j + i * (dir : ℤ) = d.workTapePos j + u.length * (dir : ℤ)
    · rw [hp, hf', Function.update_self]
    · rw [hf', Function.update_of_ne hp]
      refine hblank _ ⟨i, ?_, rfl⟩
      rcases Nat.lt_or_eq_of_le hi with h | h
      · exact h
      · exact absurd (by rw [h]) hp
  · intro p hp
    rw [hf', Function.update_of_ne (hp u.length le_rfl)]
    exact hkeep p (fun i hi => hp i hi.le)

/-- **The capture test.** From the end of the captured output, step left and read the last symbol:
blank (an empty output) exits `done false`; `true` steps left once more and exits `done true` at
a blank there (the output was exactly `[true]`); anything else exits `done false`. Every exit
clears the captured output and returns the head to its origin. -/
private def xr_testTM (K : ℕ) (r : Fin K) : MultiTapeTM K Bool xr_St where
  q₀ := .start
  tr := fun q _ w =>
    match q with
    | .start => xr_act (xr_mv1 r none SignType.neg) (some .run)
    | .run =>
      match w r with
      | none => xr_act (xr_mv1 r none SignType.pos) (some (.done false))
      | some true => xr_act (xr_mv1 r (some none) SignType.neg) (some .aux)
      | some false => xr_act (xr_mv1 r (some none) SignType.neg) (some (.back false))
    | .aux =>
      match w r with
      | none => xr_act (xr_mv1 r none SignType.pos) (some (.done true))
      | some _ => xr_act (xr_mv1 r (some none) SignType.neg) (some (.back false))
    | .back b =>
      match w r with
      | some _ => xr_act (xr_mv1 r (some none) SignType.neg) (some (.back b))
      | none => xr_act (xr_mv1 r none SignType.pos) (some (.done b))
    | q => xr_stay q

/-- The test's clearing tail: from `back false` at the end of the stored word `v`, `|v| + 1` steps
blank it, return the head to `0`, and stop at `done false`. -/
private theorem xr_test_tail {K : ℕ} {x : List Bool} (r : Fin K) (v : List Bool)
    (d : Cfg K Bool xr_St x) (hd : d.state = some (.back false))
    (hr : d.workTapes r = FinTM.bufferTape v) (hpos : d.workTapePos r = (v.length : ℤ) - 1) :
    (xr_testTM K r).runFrom d (v.length + 1) =
      ⟨some (.done false), d.inputPos, Function.update d.workTapes r (fun _ => none),
        Function.update d.workTapePos r 0, d.output⟩ := by
  rw [xr_back_run (xr_testTM K r) r (some none)
    (fun b inp w s hs => by simp [xr_testTM, hs]) (fun b inp w hw => by simp [xr_testTM, hw])
    false 0 v.length d hd (by rw [hpos]; ring)
    (fun i hi => by rw [zero_add, hr]; exact xr_bufferTape_ne_none v i hi)
    (by rw [hr]; exact xr_bufferTape_neg v _ (by omega)), hr, xr_clear_fun]

/-- **The capture test's contract.** With the output `out` stored at the origin and the head at
its end, `|out| + 2` steps clear it, return the head to `0`, change nothing else, and stop at
`done true` exactly when `out = [true]`. -/
private theorem xr_testTM_run {K : ℕ} {x : List Bool} (r : Fin K) (out : List Bool)
    (d : Cfg K Bool xr_St x) (hd : d.state = some .start)
    (hr : d.workTapes r = FinTM.bufferTape out) (hpos : d.workTapePos r = out.length) :
    (xr_testTM K r).runFrom d (out.length + 2) =
      ⟨some (.done (decide (out = [true]))), d.inputPos,
        Function.update d.workTapes r (fun _ => none), Function.update d.workTapePos r 0,
        d.output⟩ := by
  have hstart : (xr_testTM K r).step d = ⟨some .run, d.inputPos, d.workTapes,
      Function.update d.workTapePos r ((out.length : ℤ) + -1), d.output⟩ := by
    rw [MultiTapeTM.step_of_some hd,
      show (xr_testTM K r).tr .start _ _ = xr_act (xr_mv1 r none SignType.neg) (some .run)
        from rfl, xr_mv1_apply_none, xr_cast_neg, hpos]
  rcases List.eq_nil_or_concat out with rfl | ⟨L, b, hout⟩
  · -- the empty output: two steps
    have hdec : decide (([] : List Bool) = [true]) = false := rfl
    have hread : (⟨some .run, d.inputPos, d.workTapes,
        Function.update d.workTapePos r ((([] : List Bool).length : ℤ) + -1), d.output⟩ :
        Cfg K Bool xr_St x).workTapeSymbols r = none := by
      rw [Cfg.workTapeSymbols_eq]
      dsimp only
      rw [Function.update_self, hr, FinTM.bufferTape_nil]
    rw [show ([] : List Bool).length + 2 = 2 from rfl, xr_runFrom_two, hstart,
      MultiTapeTM.step_of_some rfl,
      show (xr_testTM K r).tr .run _ _ = xr_act (xr_mv1 r none SignType.pos) (some (.done false))
        by simp only [xr_testTM]; rw [hread],
      xr_mv1_apply_none, hdec]
    dsimp only
    rw [Function.update_self, Function.update_idem, xr_cast_pos]
    apply Cfg.ext
    · rfl
    · rfl
    · symm
      rw [Function.update_eq_self_iff, hr, FinTM.bufferTape_nil]
    · simp
    · rfl
  · -- a non-empty output `L ++ [b]`: the first read sees `b`
    rw [List.concat_eq_append] at hout
    subst hout
    have hlen : (L ++ [b]).length = L.length + 1 := by simp
    have hread : (⟨some .run, d.inputPos, d.workTapes,
        Function.update d.workTapePos r (((L ++ [b]).length : ℤ) + -1), d.output⟩ :
        Cfg K Bool xr_St x).workTapeSymbols r = some b := by
      rw [Cfg.workTapeSymbols_eq]
      dsimp only
      rw [Function.update_self, hr, hlen, FinTM.bufferTape_append]
      push_cast
      rw [add_neg_cancel_right, Function.update_self]
    rcases b with _ | _
    · -- last symbol `false`: blank it and clear the rest
      have hstep2 : (xr_testTM K r).step ⟨some .run, d.inputPos, d.workTapes,
          Function.update d.workTapePos r (((L ++ [false]).length : ℤ) + -1), d.output⟩ =
          ⟨some (.back false), d.inputPos, Function.update d.workTapes r (FinTM.bufferTape L),
            Function.update d.workTapePos r ((L.length : ℤ) - 1), d.output⟩ := by
        rw [MultiTapeTM.step_of_some rfl,
          show (xr_testTM K r).tr .run _ _ =
            xr_act (xr_mv1 r (some none) SignType.neg) (some (.back false)) by
              simp only [xr_testTM]; rw [hread],
          xr_mv1_apply, xr_cast_neg]
        dsimp only
        rw [Function.update_self, Function.update_idem, Option.getD_some, hr, hlen]
        congr 1
        · congr 1
          push_cast
          rw [add_neg_cancel_right, xr_bufferTape_pop]
        · congr 1
          push_cast
          ring
      have hdec : decide (L ++ [false] = [true]) = false := by
        rw [decide_eq_false_iff_not]
        intro h
        have := List.append_inj_right' (h.trans (List.nil_append [true]).symm) rfl
        simp at this
      rw [hlen, show L.length + 1 + 2 = 2 + (L.length + 1) by omega,
        MultiTapeTM.runFrom_add (tm := xr_testTM K r) d 2 (L.length + 1), xr_runFrom_two, hstart,
        hstep2, xr_test_tail r L _ rfl (by dsimp only; rw [Function.update_self])
          (by dsimp only; rw [Function.update_self]), hdec]
      dsimp only
      rw [Function.update_idem, Function.update_idem]
    · -- last symbol `true`: blank it, then look at the symbol before it
      have hstep2 : (xr_testTM K r).step ⟨some .run, d.inputPos, d.workTapes,
          Function.update d.workTapePos r (((L ++ [true]).length : ℤ) + -1), d.output⟩ =
          ⟨some .aux, d.inputPos, Function.update d.workTapes r (FinTM.bufferTape L),
            Function.update d.workTapePos r ((L.length : ℤ) - 1), d.output⟩ := by
        rw [MultiTapeTM.step_of_some rfl,
          show (xr_testTM K r).tr .run _ _ =
            xr_act (xr_mv1 r (some none) SignType.neg) (some .aux) by
              simp only [xr_testTM]; rw [hread],
          xr_mv1_apply, xr_cast_neg]
        dsimp only
        rw [Function.update_self, Function.update_idem, Option.getD_some, hr, hlen]
        congr 1
        · congr 1
          push_cast
          rw [add_neg_cancel_right, xr_bufferTape_pop]
        · congr 1
          push_cast
          ring
      rcases List.eq_nil_or_concat L with rfl | ⟨L', b', hL⟩
      · -- the output was `[true]`
        have hdec : decide (([] : List Bool) ++ [true] = [true]) = true := rfl
        have hread3 : (⟨some .aux, d.inputPos, Function.update d.workTapes r (FinTM.bufferTape []),
            Function.update d.workTapePos r ((([] : List Bool).length : ℤ) - 1), d.output⟩ :
            Cfg K Bool xr_St x).workTapeSymbols r = none := by
          rw [Cfg.workTapeSymbols_eq]
          dsimp only
          rw [Function.update_self, Function.update_self, FinTM.bufferTape_nil]
        rw [show (([] : List Bool) ++ [true]).length + 2 = 2 + 1 from rfl,
          MultiTapeTM.runFrom_add (tm := xr_testTM K r) d 2 1, xr_runFrom_two, xr_runFrom_one,
          hstart, hstep2, MultiTapeTM.step_of_some rfl,
          show (xr_testTM K r).tr .aux _ _ =
            xr_act (xr_mv1 r none SignType.pos) (some (.done true)) by
              simp only [xr_testTM]; rw [hread3],
          xr_mv1_apply_none, xr_cast_pos, hdec]
        dsimp only
        rw [Function.update_self, Function.update_idem, FinTM.bufferTape_nil]
        apply Cfg.ext
        · rfl
        · rfl
        · rfl
        · simp
        · rfl
      · -- an output of length at least two
        rw [List.concat_eq_append] at hL
        subst hL
        have hlen' : (L' ++ [b']).length = L'.length + 1 := by simp
        have hread3 : (⟨some .aux, d.inputPos,
            Function.update d.workTapes r (FinTM.bufferTape (L' ++ [b'])),
            Function.update d.workTapePos r (((L' ++ [b']).length : ℤ) - 1), d.output⟩ :
            Cfg K Bool xr_St x).workTapeSymbols r = some b' := by
          rw [Cfg.workTapeSymbols_eq]
          dsimp only
          rw [Function.update_self, Function.update_self, hlen', FinTM.bufferTape_append]
          push_cast
          rw [add_sub_cancel_right, Function.update_self]
        have hstep3 : (xr_testTM K r).step ⟨some .aux, d.inputPos,
            Function.update d.workTapes r (FinTM.bufferTape (L' ++ [b'])),
            Function.update d.workTapePos r (((L' ++ [b']).length : ℤ) - 1), d.output⟩ =
            ⟨some (.back false), d.inputPos, Function.update d.workTapes r (FinTM.bufferTape L'),
              Function.update d.workTapePos r ((L'.length : ℤ) - 1), d.output⟩ := by
          rw [MultiTapeTM.step_of_some rfl,
            show (xr_testTM K r).tr .aux _ _ =
              xr_act (xr_mv1 r (some none) SignType.neg) (some (.back false)) by
                simp only [xr_testTM]; rw [hread3],
            xr_mv1_apply, xr_cast_neg]
          dsimp only
          rw [Function.update_self, Function.update_self, Function.update_idem,
            Function.update_idem, Option.getD_some, hlen']
          congr 1
          · congr 1
            push_cast
            rw [add_sub_cancel_right, xr_bufferTape_pop]
          · congr 1
            push_cast
            ring
        have hdec : decide (L' ++ [b'] ++ [true] = [true]) = false := by
          rw [decide_eq_false_iff_not]
          intro h
          have := congrArg List.length h
          simp at this
        rw [show (L' ++ [b'] ++ [true]).length + 2 = 2 + 1 + (L'.length + 1) by
            simp only [List.length_append, List.length_singleton]; try omega,
          MultiTapeTM.runFrom_add (tm := xr_testTM K r) d (2 + 1) (L'.length + 1),
          MultiTapeTM.runFrom_add (tm := xr_testTM K r) d 2 1, xr_runFrom_two, xr_runFrom_one,
          hstart, hstep2, hstep3,
          xr_test_tail r L' _ rfl (by dsimp only; rw [Function.update_self])
            (by dsimp only; rw [Function.update_self]), hdec]
        dsimp only
        rw [Function.update_idem, Function.update_idem]

/-- **The input rewind**: a left step, then left while the input head reads a symbol, then one
step right at the left blank. -/
private def xr_inRewindTM (K : ℕ) : MultiTapeTM K Bool xr_St where
  q₀ := .start
  tr := fun q inp _ =>
    match q with
    | .start => FinTM.controlAction .neg (some .run)
    | .run =>
      match inp with
      | some _ => FinTM.controlAction .neg (some .run)
      | none => FinTM.controlAction .pos (some (.done true))
    | q => xr_stay q

/-- **The answer**: emit `b` and halt. -/
private def xr_answerTM (K : ℕ) (b : Bool) : MultiTapeTM K Bool xr_St where
  q₀ := .start
  tr := fun _ _ _ => ⟨0, fun _ => (none, 0), some b, none⟩

/-- The answer's contract: one step from any live state emits `b` and halts. -/
private theorem xr_answerTM_run {K : ℕ} {x : List Bool} (b : Bool) (d : Cfg K Bool xr_St x)
    (q : xr_St) (hd : d.state = some q) :
    (xr_answerTM K b).runFrom d 1 = {d with state := none, output := d.output ++ [b]} := by
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, MultiTapeTM.step_of_some hd]
  apply Cfg.ext
  · exact Action.apply_state _ _
  · exact (Action.apply_inputPos _ _).trans (moveInputPos_zero _)
  · funext i
    rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
    simp [xr_answerTM]
  · funext i
    rw [Action.apply_workTapePos]
    simp [xr_answerTM]
  · exact Action.apply_output _ _

/-! #### The clocked replay and its silent embedding

The step clock over the replay machine, as `Turing.exists_stepClockTMVia` supplies it, read at
`Γ = Bool` with the identity embedding and no stop state; the tape bank of `E` (the clocked
replay's `k + 2` tapes, then the capture tape and the depth tape); and one replay's two exits,
identified with `N`'s branch along the choice word through the replay lemma and the translation
of the work tapes. -/

/-- **The step clock over the replay machine.** The control `Q`, the clocked machine `H` on
`N.k + 2` tapes (the counter last), the injection of the replay's states, the two exit families,
and the clock's two exits: `finish none` when the body halts within the budget, `timeout` with
the body's live state when it does not, each with no earlier exit. -/
private structure xr_Clock (N : FinNDTM Bool) where
  Q : Type
  [fintypeQ : Fintype Q]
  [decEqQ : DecidableEq Q]
  H : MultiTapeTM (N.k + 2) Bool Q
  inj : N.State → Q
  finish : Option N.State → Q
  timeout : Option N.State → Q
  finish_ne_timeout : ∀ a b, finish a ≠ timeout b
  inj_ne : ∀ s r, inj s ≠ finish r ∧ inj s ≠ timeout r
  spec_finish : ∀ {x : List Bool} (c : Cfg (N.k + 1) Bool N.State x) (q : N.State),
    c.state = some q → ∀ (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ),
    (∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p) →
    ∀ τ ≤ Nat.ofDigits 2 (w.map Bool.toNat), (N.tm.replayTM.runFrom c τ).state = none →
    (∀ u < τ, (N.tm.replayTM.runFrom c u).state ≠ none) →
    ∃ T ≤ 5 * τ + 2 * w.length + 2, ∃ w' : List Bool, w'.length = w.length ∧
      H.runFrom (clockCfg (some (inj q)) c ct cp) T =
        clockCfg (some (finish none)) (N.tm.replayTM.runFrom c τ) (wordPatch ct cp w') cp ∧
      ∀ u < T, ∀ r, (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠ some (finish r) ∧
        (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠ some (timeout r)
  spec_timeout : ∀ {x : List Bool} (c : Cfg (N.k + 1) Bool N.State x) (q : N.State),
    c.state = some q → ∀ (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ),
    (∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p) →
    (∀ u ≤ Nat.ofDigits 2 (w.map Bool.toNat), (N.tm.replayTM.runFrom c u).state ≠ none) →
    ∃ T ≤ 5 * Nat.ofDigits 2 (w.map Bool.toNat) + 2 * w.length + 2, ∃ w' : List Bool,
      w'.length = w.length ∧
      H.runFrom (clockCfg (some (inj q)) c ct cp) T =
        clockCfg (some (timeout
            (N.tm.replayTM.runFrom c (Nat.ofDigits 2 (w.map Bool.toNat))).state))
          (N.tm.replayTM.runFrom c (Nat.ofDigits 2 (w.map Bool.toNat))) (wordPatch ct cp w') cp ∧
      ∀ u < T, ∀ r, (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠ some (finish r) ∧
        (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠ some (timeout r)

attribute [instance] xr_Clock.fintypeQ xr_Clock.decEqQ

/-- With no stop state, a body configuration is stopped exactly when it is halted. -/
private theorem xr_stopped_iff {k : ℕ} {S : Type} {x : List Bool} (c : Cfg k Bool S x) :
    c.Stopped (fun _ : S => false) ↔ c.state = none := by
  rw [Cfg.stopped_iff]
  simp

/-- The clock exists: `Turing.exists_stepClockTMVia` at `Γ = Bool`, the identity embedding and
no stop state, with its two exits read. -/
private theorem xr_Clock.exists (N : FinNDTM Bool) : Nonempty (xr_Clock N) := by
  obtain ⟨Q, instF, instD, H, inj, finish, timeout, -, -, hft, hinj, hspec⟩ :=
    exists_stepClockTMVia (Function.Embedding.refl Bool) N.tm.replayTM (fun _ => false)
  have hmap : ∀ w : List Bool, w.map ⇑(Function.Embedding.refl Bool) = w := fun w => by
    rw [Function.Embedding.coe_refl, List.map_id]
  letI : Fintype Q := instF
  letI : DecidableEq Q := instD
  refine ⟨⟨Q, H, inj, finish, timeout, hft, hinj, ?_, ?_⟩⟩
  · intro x c q hq w ct cp hct τ hτ hstop hlive
    have hct' : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
        ct (cp + p) = FinTM.bufferTape (w.map ⇑(Function.Embedding.refl Bool)) p := by
      rw [hmap]; exact hct
    obtain ⟨T, hT, w', hw', hrun, hguard, -⟩ := (hspec c q hq w ct cp hct').1 τ hτ
      ((xr_stopped_iff _).mpr hstop)
      (fun u hu => by rw [xr_stopped_iff]; exact hlive u hu)
    refine ⟨T, hT, w', hw', ?_, hguard⟩
    rw [hrun, hstop, hmap]
  · intro x c q hq w ct cp hct hlive
    have hct' : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
        ct (cp + p) = FinTM.bufferTape (w.map ⇑(Function.Embedding.refl Bool)) p := by
      rw [hmap]; exact hct
    obtain ⟨T, hT, w', hw', hrun, hguard, -⟩ := (hspec c q hq w ct cp hct').2
      (fun u hu => by rw [xr_stopped_iff]; exact hlive u hu)
    refine ⟨T, hT, w', hw', ?_, hguard⟩
    rw [hrun, hmap]

/-! The tape bank of `E` for an NDTM with `k` work tapes: the `k + 2` tapes of the clocked replay
(`N`'s `k` tapes, the choice tape, the clock's counter), then the capture tape and the depth
tape, as `Fin (k + 2 + 2)`. -/

/-- The clocked replay's bank, as the first `k + 2` tapes. -/
private def xr_ι (k : ℕ) : Fin (k + 2) ↪ Fin (k + 2 + 2) := Fin.castAddEmb 2

/-- The capture tape. -/
private def xr_cap (k : ℕ) : Fin (k + 2 + 2) := Fin.natAdd (k + 2) 0

/-- The depth tape. -/
private def xr_dep (k : ℕ) : Fin (k + 2 + 2) := Fin.natAdd (k + 2) 1

/-- `N`'s work tape `j`. -/
private def xr_work (k : ℕ) (j : Fin k) : Fin (k + 2 + 2) := Fin.castAdd 2 j.castSucc.castSucc

/-- The choice tape. -/
private def xr_choice (k : ℕ) : Fin (k + 2 + 2) := Fin.castAdd 2 (Fin.last k).castSucc

/-- The clock's counter tape. -/
private def xr_ctr (k : ℕ) : Fin (k + 2 + 2) := Fin.castAdd 2 (Fin.last (k + 1))

/-- `E`'s work tapes from their five banks. -/
private def xr_tapes {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp : ℤ → Option Bool) :
    Fin (k + 2 + 2) → ℤ → Option Bool :=
  Fin.addCases (Fin.lastCases ctr (Fin.lastCases ch wk))
    (fun j : Fin 2 => if j = 0 then cp else dp)

/-- `E`'s work heads from their five banks. -/
private def xr_heads {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) : Fin (k + 2 + 2) → ℤ :=
  Fin.addCases (Fin.lastCases hctr (Fin.lastCases hch hk))
    (fun j : Fin 2 => if j = 0 then hcp else hdp)

private theorem xr_tapes_work {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp) (j : Fin k) :
    xr_tapes wk ch ctr cp dp (xr_work k j) = wk j := by
  simp [xr_tapes, xr_work]

private theorem xr_tapes_choice {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp) :
    xr_tapes wk ch ctr cp dp (xr_choice k) = ch := by
  simp [xr_tapes, xr_choice]

private theorem xr_tapes_ctr {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp) :
    xr_tapes wk ch ctr cp dp (xr_ctr k) = ctr := by
  simp [xr_tapes, xr_ctr]

private theorem xr_tapes_cap {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp) :
    xr_tapes wk ch ctr cp dp (xr_cap k) = cp := by
  simp [xr_tapes, xr_cap]

private theorem xr_tapes_dep {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp) :
    xr_tapes wk ch ctr cp dp (xr_dep k) = dp := by
  simp [xr_tapes, xr_dep]

private theorem xr_heads_work {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) (j : Fin k) :
    xr_heads hk hch hctr hcp hdp (xr_work k j) = hk j := by
  simp [xr_heads, xr_work]

private theorem xr_heads_choice {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) :
    xr_heads hk hch hctr hcp hdp (xr_choice k) = hch := by
  simp [xr_heads, xr_choice]

private theorem xr_heads_ctr {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) :
    xr_heads hk hch hctr hcp hdp (xr_ctr k) = hctr := by
  simp [xr_heads, xr_ctr]

private theorem xr_heads_cap {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) :
    xr_heads hk hch hctr hcp hdp (xr_cap k) = hcp := by
  simp [xr_heads, xr_cap]

private theorem xr_heads_dep {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) :
    xr_heads hk hch hctr hcp hdp (xr_dep k) = hdp := by
  simp [xr_heads, xr_dep]

/-- The capture tape is outside the clocked replay's bank. -/
private theorem xr_cap_not_mem (k : ℕ) : xr_cap k ∉ Set.range (xr_ι k) := by
  rintro ⟨i, hi⟩
  have := congrArg Fin.val hi
  simp [xr_ι, xr_cap] at this
  omega

/-- The depth tape is outside the clocked replay's bank. -/
private theorem xr_dep_not_mem (k : ℕ) : xr_dep k ∉ Set.range (xr_ι k) := by
  rintro ⟨i, hi⟩
  have := congrArg Fin.val hi
  simp [xr_ι, xr_dep] at this
  omega

private theorem xr_dep_ne_cap (k : ℕ) : xr_dep k ≠ xr_cap k := by
  intro h
  have := congrArg Fin.val h
  simp [xr_dep, xr_cap] at this

/-- Every index of `Fin (m + n)` is a left or a right index. -/
private theorem xr_addCases_split {m n : ℕ} (j : Fin (m + n)) :
    (∃ i : Fin m, j = Fin.castAdd n i) ∨ ∃ i : Fin n, j = Fin.natAdd m i :=
  Fin.addCases
    (motive := fun j => (∃ i : Fin m, j = Fin.castAdd n i) ∨ ∃ i : Fin n, j = Fin.natAdd m i)
    (fun i => Or.inl ⟨i, rfl⟩) (fun i => Or.inr ⟨i, rfl⟩) j

/-- Every index of `Fin (n + 1)` is the last one or a cast. -/
private theorem xr_lastCases_split {n : ℕ} (i : Fin (n + 1)) :
    i = Fin.last n ∨ ∃ i' : Fin n, i = i'.castSucc :=
  Fin.lastCases (motive := fun i => i = Fin.last n ∨ ∃ i' : Fin n, i = i'.castSucc)
    (Or.inl rfl) (fun i' => Or.inr ⟨i', rfl⟩) i

private theorem xr_fin2 (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

/-- **The embedded clocked configuration, by banks**: the clocked replay configuration over `N`'s
configuration `c`, the choice tape and the counter, embedded silently with the capture tape and
the depth tape, is the explicit `E` configuration. -/
private theorem xr_embed_eq {k : ℕ} {S Q : Type} {z : List Bool} (q : Option Q)
    (c : Cfg k Bool S z) (chT ct : ℤ → Option Bool) (chP cp : ℤ) (dp : ℤ → Option Bool)
    (hdp : ℤ) (pre out₀ : List Bool) :
    embedSilentCfg (xr_ι k) (xr_cap k) (fun _ => dp) (fun _ => hdp) pre out₀
        (clockCfg q (NDTM.withChoiceTape c chT chP) ct cp) =
      ⟨q, c.inputPos, xr_tapes c.workTapes chT ct (FinTM.bufferTape (pre ++ c.output)) dp,
        xr_heads c.workTapePos chP cp ((pre ++ c.output).length : ℤ) hdp, out₀⟩ := by
  apply Cfg.ext
  · rw [embedSilentCfg_state, clockCfg_state]
  · rw [embedSilentCfg_inputPos, clockCfg_inputPos, NDTM.withChoiceTape_inputPos]
  · funext j
    rcases xr_addCases_split j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [← Fin.castAddEmb_apply, show Fin.castAddEmb 2 = xr_ι k from rfl,
        embedSilentCfg_selected_tape]
      funext a
      rw [clockCfg_workTapes]
      show _ = xr_tapes c.workTapes chT ct (FinTM.bufferTape (pre ++ c.output)) dp
        (Fin.castAdd 2 i) a
      rw [xr_tapes, Fin.addCases_left]
      rcases xr_lastCases_split i with rfl | ⟨i, rfl⟩
      · rw [Fin.lastCases_last, Fin.lastCases_last]
      · rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc, NDTM.withChoiceTape_workTapes]
    · rcases xr_fin2 i with rfl | rfl
      · rw [show Fin.natAdd (k + 2) (0 : Fin 2) = xr_cap k from rfl,
          (embedSilentCfg_cap _ _ (xr_cap_not_mem k) _ _ _ _ _).1, clockCfg_output,
          NDTM.withChoiceTape_output]
        show _ = xr_tapes c.workTapes chT ct (FinTM.bufferTape (pre ++ c.output)) dp
          (Fin.natAdd (k + 2) 0)
        rw [xr_tapes, Fin.addCases_right]
        simp
      · rw [show Fin.natAdd (k + 2) (1 : Fin 2) = xr_dep k from rfl,
          (embedSilentCfg_unselected _ _ _ _ _ _ _ _ (xr_dep_not_mem k) (xr_dep_ne_cap k)).1]
        show _ = xr_tapes c.workTapes chT ct (FinTM.bufferTape (pre ++ c.output)) dp
          (Fin.natAdd (k + 2) 1)
        rw [xr_tapes, Fin.addCases_right]
        simp
  · funext j
    rcases xr_addCases_split j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [← Fin.castAddEmb_apply, show Fin.castAddEmb 2 = xr_ι k from rfl,
        embedSilentCfg_selected_pos, clockCfg_workTapePos]
      show _ = xr_heads c.workTapePos chP cp ((pre ++ c.output).length : ℤ) hdp (Fin.castAdd 2 i)
      rw [xr_heads, Fin.addCases_left]
      rcases xr_lastCases_split i with rfl | ⟨i, rfl⟩
      · rw [Fin.lastCases_last, Fin.lastCases_last]
      · rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc, NDTM.withChoiceTape_workTapePos]
    · rcases xr_fin2 i with rfl | rfl
      · rw [show Fin.natAdd (k + 2) (0 : Fin 2) = xr_cap k from rfl,
          (embedSilentCfg_cap _ _ (xr_cap_not_mem k) _ _ _ _ _).2, clockCfg_output,
          NDTM.withChoiceTape_output]
        show _ = xr_heads c.workTapePos chP cp ((pre ++ c.output).length : ℤ) hdp
          (Fin.natAdd (k + 2) 0)
        rw [xr_heads, Fin.addCases_right]
        simp
      · rw [show Fin.natAdd (k + 2) (1 : Fin 2) = xr_dep k from rfl,
          (embedSilentCfg_unselected _ _ _ _ _ _ _ _ (xr_dep_not_mem k) (xr_dep_ne_cap k)).2]
        show _ = xr_heads c.workTapePos chP cp ((pre ++ c.output).length : ℤ) hdp
          (Fin.natAdd (k + 2) 1)
        rw [xr_heads, Fin.addCases_right]
        simp
  · rw [embedSilentCfg_output]

/-- Patching a same-width word over a stored word at the origin stores the new word. -/
private theorem xr_wordPatch_buffer (w w' : List Bool) (hw : w'.length = w.length) :
    wordPatch (FinTM.bufferTape w) 0 w' = FinTM.bufferTape w' := by
  funext q
  by_cases h : 0 ≤ q ∧ q < 0 + (w'.length : ℤ)
  · rw [wordPatch_of_mem _ _ _ h.1 h.2, sub_zero]
  · rw [wordPatch_of_not_mem _ _ _ h, (xr_bufferTape_eq_none_iff _ _).mpr ?_,
      (xr_bufferTape_eq_none_iff _ _).mpr ?_]
    · omega
    · omega

/-- **The replay phase**: the clocked replay, embedded silently with the capture tape. -/
private def xr_replayTM {N : FinNDTM Bool} (C : xr_Clock N) :
    MultiTapeTM (N.k + 2 + 2) Bool C.Q :=
  embedSilentTM (xr_ι N.k) (xr_cap N.k) C.H

/-- `E` at the start of a replay of the choice word `s` under the budget word `w`: the clock at
the replay's initial state, `N`'s tapes blank with their heads at `h`, the input head at `1`, the
capture tape blank, the depth word `wD`, every auxiliary head at its origin. -/
private def xr_replayStart {N : FinNDTM Bool} (C : xr_Clock N) (z s w wD : List Bool)
    (h : Fin N.k → ℤ) : Cfg (N.k + 2 + 2) Bool C.Q z :=
  ⟨some (C.inj N.tm.q₀), 1,
    xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape w) (FinTM.bufferTape [])
      (FinTM.bufferTape wD),
    xr_heads h 0 0 0 0, []⟩

/-- The replay's start is the embedded clocked configuration over the translated initial
configuration of `N`. -/
private theorem xr_replayStart_eq {N : FinNDTM Bool} (C : xr_Clock N) (z s w wD : List Bool)
    (h : Fin N.k → ℤ) :
    xr_replayStart C z s w wD h =
      embedSilentCfg (xr_ι N.k) (xr_cap N.k) (fun _ => FinTM.bufferTape wD) (fun _ => 0) [] []
        (clockCfg (some (C.inj N.tm.q₀))
          (NDTM.withChoiceTape (xr_shift h (N.tm.initCfg z)) (FinTM.bufferTape s) 0)
          (FinTM.bufferTape w) 0) := by
  rw [xr_embed_eq]
  have h1 : (fun i p => (N.tm.initCfg z).workTapes i (p - h i)) =
      fun (_ : Fin N.k) (_ : ℤ) => (none : Option Bool) := by
    funext i p
    rw [NDTM.initCfg_eq, Cfg.init_workTapes]
  have h2 : (fun i => (N.tm.initCfg z).workTapePos i + h i) = h := by
    funext i
    rw [NDTM.initCfg_eq, Cfg.init_workTapePos, zero_add]
  apply Cfg.ext
  · rfl
  · show (1 : Fin _) = (N.tm.initCfg z).inputPos
    rw [NDTM.initCfg_eq, Cfg.init_inputPos]
  · show xr_tapes (fun _ _ => none) _ _ (FinTM.bufferTape []) _ =
      xr_tapes (fun i p => (N.tm.initCfg z).workTapes i (p - h i)) _ _
        (FinTM.bufferTape ([] ++ (N.tm.initCfg z).output)) _
    rw [h1, NDTM.initCfg_eq, Cfg.init_output, List.nil_append]
  · show xr_heads h 0 0 0 0 =
      xr_heads (fun i => (N.tm.initCfg z).workTapePos i + h i) 0 0
        (([] ++ (N.tm.initCfg z).output).length : ℤ) 0
    rw [h2, NDTM.initCfg_eq, Cfg.init_output, List.nil_append, List.length_nil, Nat.cast_zero]
  · rfl

/-- The replay's body states along the choice word are `N`'s branch states. -/
private theorem xr_replay_state {N : FinNDTM Bool} (z s : List Bool) (h : Fin N.k → ℤ) (u : ℕ)
    (hu : u ≤ s.length) :
    (N.tm.replayTM.runFrom
      (NDTM.withChoiceTape (xr_shift h (N.tm.initCfg z)) (FinTM.bufferTape s) 0) u).state =
      (N.tm.runWith (s.take u) (N.tm.initCfg z)).state := by
  obtain ⟨p, -, -, hrun⟩ := NDTM.replayTM_runFrom N.tm (xr_shift h (N.tm.initCfg z)) s u hu
  rw [hrun, NDTM.withChoiceTape_state, xr_runWith_shift]
  rfl

/-- **One replay, the `finish` exit.** If the branch along `s` first halts at `τ ≤ |s|`, and the
budget word `w` has value `|s|`, the replay phase reaches, within `5τ + 2|w| + 2` steps and with no
earlier exit, the exit `finish none` over `N`'s halted branch configuration, translated by `h`:
its input head and output, its work tapes and heads translated, the choice head at some `p ≤ τ`,
the counter rewritten to some word of the same width with its head at the origin, the output
captured with the capture head at its end, the depth tape untouched, and nothing emitted. -/
private theorem xr_replay_finish {N : FinNDTM Bool} (C : xr_Clock N) (z s w wD : List Bool)
    (h : Fin N.k → ℤ) (hval : Nat.ofDigits 2 (w.map Bool.toNat) = s.length) (τ : ℕ)
    (hτ : τ ≤ s.length) (hhalt : (N.tm.runWith (s.take τ) (N.tm.initCfg z)).state = none)
    (hlive : ∀ u < τ, (N.tm.runWith (s.take u) (N.tm.initCfg z)).state ≠ none) :
    ∃ T ≤ 5 * τ + 2 * w.length + 2, ∃ p ≤ τ, ∃ w' : List Bool, w'.length = w.length ∧
      (xr_replayTM C).runFrom (xr_replayStart C z s w wD h) T =
        ⟨some (C.finish none), (N.tm.runWith (s.take τ) (N.tm.initCfg z)).inputPos,
          xr_tapes (xr_shift h (N.tm.runWith (s.take τ) (N.tm.initCfg z))).workTapes
            (FinTM.bufferTape s) (FinTM.bufferTape w')
            (FinTM.bufferTape (N.tm.runWith (s.take τ) (N.tm.initCfg z)).output)
            (FinTM.bufferTape wD),
          xr_heads (xr_shift h (N.tm.runWith (s.take τ) (N.tm.initCfg z))).workTapePos p 0
            ((N.tm.runWith (s.take τ) (N.tm.initCfg z)).output.length : ℤ) 0, []⟩ ∧
      ∀ u < T, ∀ r,
        ((xr_replayTM C).runFrom (xr_replayStart C z s w wD h) u).state ≠ some (C.finish r) ∧
        ((xr_replayTM C).runFrom (xr_replayStart C z s w wD h) u).state ≠ some (C.timeout r) := by
  have hq : (NDTM.withChoiceTape (xr_shift h (N.tm.initCfg z)) (FinTM.bufferTape s) 0).state =
      some N.tm.q₀ := by
    rw [NDTM.withChoiceTape_state]
    show (N.tm.initCfg z).state = _
    rw [NDTM.initCfg_eq, Cfg.init_state]
  have hct : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      FinTM.bufferTape w (0 + p) = FinTM.bufferTape w p := fun p _ _ => by rw [zero_add]
  obtain ⟨T, hT, w', hw', hrun, hguard⟩ := C.spec_finish _ _ hq w (FinTM.bufferTape w) 0 hct τ
    (by rw [hval]; exact hτ) (by rw [xr_replay_state z s h τ hτ]; exact hhalt)
    (fun u hu => by rw [xr_replay_state z s h u (by omega)]; exact hlive u hu)
  obtain ⟨p, hp, -, hrep⟩ := NDTM.replayTM_runFrom N.tm (xr_shift h (N.tm.initCfg z)) s τ hτ
  rw [xr_runWith_shift] at hrep
  have hE : ∀ u, (xr_replayTM C).runFrom (xr_replayStart C z s w wD h) u =
      embedSilentCfg (xr_ι N.k) (xr_cap N.k) (fun _ => FinTM.bufferTape wD) (fun _ => 0) [] []
        (C.H.runFrom (clockCfg (some (C.inj N.tm.q₀))
          (NDTM.withChoiceTape (xr_shift h (N.tm.initCfg z)) (FinTM.bufferTape s) 0)
          (FinTM.bufferTape w) 0) u) := fun u => by
    rw [xr_replayStart_eq, xr_replayTM, embedSilentTM_runFrom _ _ (xr_cap_not_mem N.k)]
  refine ⟨T, hT, p, hp, w', hw', ?_, fun u hu r => ?_⟩
  · rw [hE, hrun, hrep, xr_embed_eq, xr_wordPatch_buffer w w' hw', List.nil_append]
    rfl
  · rw [hE, embedSilentCfg_state]
    exact hguard u hu r

/-- **One replay, the `timeout` exit.** If the branch along `s` is still live after `|s|` steps
(and so at every earlier time), and the budget word `w` has value `|s|`, the replay phase reaches,
within `7|s| + 2|w| + 2` steps and with no earlier exit, the exit `timeout` carrying the branch's
live state, over `N`'s branch configuration translated by `h`, with the same bank layout as the
`finish` exit. -/
private theorem xr_replay_timeout {N : FinNDTM Bool} (C : xr_Clock N) (z s w wD : List Bool)
    (h : Fin N.k → ℤ) (hval : Nat.ofDigits 2 (w.map Bool.toNat) = s.length)
    (hlive : ∀ u ≤ s.length, (N.tm.runWith (s.take u) (N.tm.initCfg z)).state ≠ none) :
    ∃ T ≤ 5 * s.length + 2 * w.length + 2, ∃ p ≤ s.length, ∃ w' : List Bool,
      w'.length = w.length ∧
      (xr_replayTM C).runFrom (xr_replayStart C z s w wD h) T =
        ⟨some (C.timeout (N.tm.runWith s (N.tm.initCfg z)).state),
          (N.tm.runWith s (N.tm.initCfg z)).inputPos,
          xr_tapes (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapes
            (FinTM.bufferTape s) (FinTM.bufferTape w')
            (FinTM.bufferTape (N.tm.runWith s (N.tm.initCfg z)).output) (FinTM.bufferTape wD),
          xr_heads (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapePos p 0
            ((N.tm.runWith s (N.tm.initCfg z)).output.length : ℤ) 0, []⟩ ∧
      ∀ u < T, ∀ r,
        ((xr_replayTM C).runFrom (xr_replayStart C z s w wD h) u).state ≠ some (C.finish r) ∧
        ((xr_replayTM C).runFrom (xr_replayStart C z s w wD h) u).state ≠ some (C.timeout r) := by
  have hq : (NDTM.withChoiceTape (xr_shift h (N.tm.initCfg z)) (FinTM.bufferTape s) 0).state =
      some N.tm.q₀ := by
    rw [NDTM.withChoiceTape_state]
    show (N.tm.initCfg z).state = _
    rw [NDTM.initCfg_eq, Cfg.init_state]
  have hct : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      FinTM.bufferTape w (0 + p) = FinTM.bufferTape w p := fun p _ _ => by rw [zero_add]
  obtain ⟨T, hT, w', hw', hrun, hguard⟩ := C.spec_timeout _ _ hq w (FinTM.bufferTape w) 0 hct
    (fun u hu => by rw [xr_replay_state z s h u (by omega)]; exact hlive u (by omega))
  rw [hval] at hT hrun
  obtain ⟨p, hp, -, hrep⟩ := NDTM.replayTM_runFrom N.tm (xr_shift h (N.tm.initCfg z)) s s.length
    le_rfl
  rw [xr_runWith_shift, List.take_length] at hrep
  have hE : ∀ u, (xr_replayTM C).runFrom (xr_replayStart C z s w wD h) u =
      embedSilentCfg (xr_ι N.k) (xr_cap N.k) (fun _ => FinTM.bufferTape wD) (fun _ => 0) [] []
        (C.H.runFrom (clockCfg (some (C.inj N.tm.q₀))
          (NDTM.withChoiceTape (xr_shift h (N.tm.initCfg z)) (FinTM.bufferTape s) 0)
          (FinTM.bufferTape w) 0) u) := fun u => by
    rw [xr_replayStart_eq, xr_replayTM, embedSilentTM_runFrom _ _ (xr_cap_not_mem N.k)]
  refine ⟨T, hT, p, hp, w', hw', ?_, fun u hu r => ?_⟩
  · rw [hE, hrun, hrep, xr_embed_eq, xr_wordPatch_buffer w w' hw', List.nil_append,
      NDTM.withChoiceTape_state]
    rfl
  · rw [hE, embedSilentCfg_state]
    exact hguard u hu r

/-! #### The host: its phases, its redirect table, and one phase's step

The exhaustive replay is `Turing.phaseHostTM` over the phases of one depth (copy the depth word
to the clock's counter; one replay; the capture test; the choice and input rewinds; the window
clear, six passes per work tape; the increment of the choice word) and of a depth change (extend
the choice word and the depth word, increment the depth word), with the two flags "some branch
accepted" and "some branch is live" in the phase index, and the answer phases. -/

/-- **The first arrival at a stationary anchor, over a family of anchors.** If every state in `A`
is stationary and a run reaches `c'` in a state of `A` at time `T`, the first time the state is in
`A` is at most `T`, reaches `c'` too, and no earlier state is in `A`. -/
private theorem xr_firstArrival' {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S)
    (A : S → Prop)
    (hstat : ∀ d : Cfg k Bool S x, ∀ a, d.state = some a → A a → tm.step d = d)
    {c c' : Cfg k Bool S x} {T : ℕ} (h : tm.runFrom c T = c') {a : S} (hc' : c'.state = some a)
    (ha : A a) :
    ∃ T' ≤ T, tm.runFrom c T' = c' ∧
      ∀ u < T', ∀ a', (tm.runFrom c u).state = some a' → ¬ A a' := by
  classical
  have hT' : ∃ a', (tm.runFrom c T).state = some a' ∧ A a' := ⟨a, by rw [h]; exact hc', ha⟩
  have hex : ∃ u, ∃ a', (tm.runFrom c u).state = some a' ∧ A a' := ⟨T, hT'⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hT', ?_,
    fun u hu a' ha' hA => Nat.find_min hex hu ⟨a', ha', hA⟩⟩
  obtain ⟨a'', ha'', hA''⟩ := Nat.find_spec hex
  have hsplit : tm.runFrom c T = tm.runFrom (tm.runFrom c (Nat.find hex)) (T - Nat.find hex) := by
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_cancel' (Nat.find_min' hex hT')]
  rw [xr_runFrom_fixed tm _ (hstat _ a'' ha'' hA'')] at hsplit
  exact hsplit.symm.trans h

/-- Every `done` anchor of a leaf row whose table is stationary there is stationary. -/
private theorem xr_done_stationary {K : ℕ} {x : List Bool} (tm : MultiTapeTM K Bool xr_St)
    (htr : ∀ b inp w, tm.tr (.done b) inp w = xr_stay (.done b)) (d : Cfg K Bool xr_St x)
    (a : xr_St) (hd : d.state = some a) (ha : ∃ b, a = .done b) : tm.step d = d := by
  obtain ⟨b, rfl⟩ := ha
  exact xr_stay_step tm (.done b) (htr b) d hd

/-! ##### The banks are distinct -/

private theorem xr_work_val {k : ℕ} (j : Fin k) : (xr_work k j).val = j.val := by
  simp [xr_work]
private theorem xr_choice_val (k : ℕ) : (xr_choice k).val = k := by
  simp [xr_choice]
private theorem xr_ctr_val (k : ℕ) : (xr_ctr k).val = k + 1 := by
  simp [xr_ctr]
private theorem xr_cap_val (k : ℕ) : (xr_cap k).val = k + 2 := by
  simp [xr_cap]
private theorem xr_dep_val (k : ℕ) : (xr_dep k).val = k + 3 := by
  simp [xr_dep]

private theorem xr_work_ne_choice {k : ℕ} (j : Fin k) : xr_work k j ≠ xr_choice k := by
  intro h; have := congrArg Fin.val h; rw [xr_work_val, xr_choice_val] at this; omega
private theorem xr_work_ne_ctr {k : ℕ} (j : Fin k) : xr_work k j ≠ xr_ctr k := by
  intro h; have := congrArg Fin.val h; rw [xr_work_val, xr_ctr_val] at this; omega
private theorem xr_work_ne_cap {k : ℕ} (j : Fin k) : xr_work k j ≠ xr_cap k := by
  intro h; have := congrArg Fin.val h; rw [xr_work_val, xr_cap_val] at this; omega
private theorem xr_work_ne_dep {k : ℕ} (j : Fin k) : xr_work k j ≠ xr_dep k := by
  intro h; have := congrArg Fin.val h; rw [xr_work_val, xr_dep_val] at this; omega
private theorem xr_choice_ne_ctr (k : ℕ) : xr_choice k ≠ xr_ctr k := by
  intro h; have := congrArg Fin.val h; rw [xr_choice_val, xr_ctr_val] at this; omega
private theorem xr_choice_ne_cap (k : ℕ) : xr_choice k ≠ xr_cap k := by
  intro h; have := congrArg Fin.val h; rw [xr_choice_val, xr_cap_val] at this; omega
private theorem xr_choice_ne_dep (k : ℕ) : xr_choice k ≠ xr_dep k := by
  intro h; have := congrArg Fin.val h; rw [xr_choice_val, xr_dep_val] at this; omega
private theorem xr_ctr_ne_cap (k : ℕ) : xr_ctr k ≠ xr_cap k := by
  intro h; have := congrArg Fin.val h; rw [xr_ctr_val, xr_cap_val] at this; omega
private theorem xr_ctr_ne_dep (k : ℕ) : xr_ctr k ≠ xr_dep k := by
  intro h; have := congrArg Fin.val h; rw [xr_ctr_val, xr_dep_val] at this; omega
private theorem xr_cap_ne_dep (k : ℕ) : xr_cap k ≠ xr_dep k := by
  intro h; have := congrArg Fin.val h; rw [xr_cap_val, xr_dep_val] at this; omega
private theorem xr_work_injective {k : ℕ} {j j' : Fin k} (h : xr_work k j = xr_work k j') :
    j = j' := by
  apply Fin.ext
  have := congrArg Fin.val h
  rwa [xr_work_val, xr_work_val] at this

/-- Two functions on `E`'s tape indices agree when they agree on every bank. -/
private theorem xr_bank_ext {k : ℕ} {α : Type} (F G : Fin (k + 2 + 2) → α)
    (hw : ∀ j, F (xr_work k j) = G (xr_work k j)) (hch : F (xr_choice k) = G (xr_choice k))
    (hctr : F (xr_ctr k) = G (xr_ctr k)) (hcap : F (xr_cap k) = G (xr_cap k))
    (hdep : F (xr_dep k) = G (xr_dep k)) : F = G := by
  funext j
  rcases xr_addCases_split j with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rcases xr_lastCases_split i with rfl | ⟨i, rfl⟩
    · exact hctr
    · rcases xr_lastCases_split i with rfl | ⟨i, rfl⟩
      · exact hch
      · exact hw i
  · rcases xr_fin2 i with rfl | rfl
    · exact hcap
    · exact hdep

/-! ##### Updating one bank -/

private theorem xr_tapes_upd_work {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp) (j : Fin k)
    (X : ℤ → Option Bool) :
    Function.update (xr_tapes wk ch ctr cp dp) (xr_work k j) X =
      xr_tapes (Function.update wk j X) ch ctr cp dp := by
  apply xr_bank_ext
  · intro j'
    by_cases hj : j' = j
    · subst hj; rw [Function.update_self, xr_tapes_work, Function.update_self]
    · rw [Function.update_of_ne (fun h => hj (xr_work_injective h)), xr_tapes_work, xr_tapes_work,
        Function.update_of_ne hj]
  · rw [Function.update_of_ne (Ne.symm (xr_work_ne_choice j)), xr_tapes_choice, xr_tapes_choice]
  · rw [Function.update_of_ne (Ne.symm (xr_work_ne_ctr j)), xr_tapes_ctr, xr_tapes_ctr]
  · rw [Function.update_of_ne (Ne.symm (xr_work_ne_cap j)), xr_tapes_cap, xr_tapes_cap]
  · rw [Function.update_of_ne (Ne.symm (xr_work_ne_dep j)), xr_tapes_dep, xr_tapes_dep]

private theorem xr_tapes_upd_choice {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp)
    (X : ℤ → Option Bool) :
    Function.update (xr_tapes wk ch ctr cp dp) (xr_choice k) X = xr_tapes wk X ctr cp dp := by
  apply xr_bank_ext
  · intro j; rw [Function.update_of_ne (xr_work_ne_choice j), xr_tapes_work, xr_tapes_work]
  · rw [Function.update_self, xr_tapes_choice]
  · rw [Function.update_of_ne (Ne.symm (xr_choice_ne_ctr k)), xr_tapes_ctr, xr_tapes_ctr]
  · rw [Function.update_of_ne (Ne.symm (xr_choice_ne_cap k)), xr_tapes_cap, xr_tapes_cap]
  · rw [Function.update_of_ne (Ne.symm (xr_choice_ne_dep k)), xr_tapes_dep, xr_tapes_dep]

private theorem xr_tapes_upd_ctr {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp)
    (X : ℤ → Option Bool) :
    Function.update (xr_tapes wk ch ctr cp dp) (xr_ctr k) X = xr_tapes wk ch X cp dp := by
  apply xr_bank_ext
  · intro j; rw [Function.update_of_ne (xr_work_ne_ctr j), xr_tapes_work, xr_tapes_work]
  · rw [Function.update_of_ne (xr_choice_ne_ctr k), xr_tapes_choice, xr_tapes_choice]
  · rw [Function.update_self, xr_tapes_ctr]
  · rw [Function.update_of_ne (Ne.symm (xr_ctr_ne_cap k)), xr_tapes_cap, xr_tapes_cap]
  · rw [Function.update_of_ne (Ne.symm (xr_ctr_ne_dep k)), xr_tapes_dep, xr_tapes_dep]

private theorem xr_tapes_upd_cap {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp)
    (X : ℤ → Option Bool) :
    Function.update (xr_tapes wk ch ctr cp dp) (xr_cap k) X = xr_tapes wk ch ctr X dp := by
  apply xr_bank_ext
  · intro j; rw [Function.update_of_ne (xr_work_ne_cap j), xr_tapes_work, xr_tapes_work]
  · rw [Function.update_of_ne (xr_choice_ne_cap k), xr_tapes_choice, xr_tapes_choice]
  · rw [Function.update_of_ne (xr_ctr_ne_cap k), xr_tapes_ctr, xr_tapes_ctr]
  · rw [Function.update_self, xr_tapes_cap]
  · rw [Function.update_of_ne (Ne.symm (xr_cap_ne_dep k)), xr_tapes_dep, xr_tapes_dep]

private theorem xr_tapes_upd_dep {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp)
    (X : ℤ → Option Bool) :
    Function.update (xr_tapes wk ch ctr cp dp) (xr_dep k) X = xr_tapes wk ch ctr cp X := by
  apply xr_bank_ext
  · intro j; rw [Function.update_of_ne (xr_work_ne_dep j), xr_tapes_work, xr_tapes_work]
  · rw [Function.update_of_ne (xr_choice_ne_dep k), xr_tapes_choice, xr_tapes_choice]
  · rw [Function.update_of_ne (xr_ctr_ne_dep k), xr_tapes_ctr, xr_tapes_ctr]
  · rw [Function.update_of_ne (xr_cap_ne_dep k), xr_tapes_cap, xr_tapes_cap]
  · rw [Function.update_self, xr_tapes_dep]

private theorem xr_heads_upd_work {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) (j : Fin k)
    (X : ℤ) :
    Function.update (xr_heads hk hch hctr hcp hdp) (xr_work k j) X =
      xr_heads (Function.update hk j X) hch hctr hcp hdp := by
  apply xr_bank_ext
  · intro j'
    by_cases hj : j' = j
    · subst hj; rw [Function.update_self, xr_heads_work, Function.update_self]
    · rw [Function.update_of_ne (fun h => hj (xr_work_injective h)), xr_heads_work, xr_heads_work,
        Function.update_of_ne hj]
  · rw [Function.update_of_ne (Ne.symm (xr_work_ne_choice j)), xr_heads_choice, xr_heads_choice]
  · rw [Function.update_of_ne (Ne.symm (xr_work_ne_ctr j)), xr_heads_ctr, xr_heads_ctr]
  · rw [Function.update_of_ne (Ne.symm (xr_work_ne_cap j)), xr_heads_cap, xr_heads_cap]
  · rw [Function.update_of_ne (Ne.symm (xr_work_ne_dep j)), xr_heads_dep, xr_heads_dep]

private theorem xr_heads_upd_choice {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) (X : ℤ) :
    Function.update (xr_heads hk hch hctr hcp hdp) (xr_choice k) X =
      xr_heads hk X hctr hcp hdp := by
  apply xr_bank_ext
  · intro j; rw [Function.update_of_ne (xr_work_ne_choice j), xr_heads_work, xr_heads_work]
  · rw [Function.update_self, xr_heads_choice]
  · rw [Function.update_of_ne (Ne.symm (xr_choice_ne_ctr k)), xr_heads_ctr, xr_heads_ctr]
  · rw [Function.update_of_ne (Ne.symm (xr_choice_ne_cap k)), xr_heads_cap, xr_heads_cap]
  · rw [Function.update_of_ne (Ne.symm (xr_choice_ne_dep k)), xr_heads_dep, xr_heads_dep]

private theorem xr_heads_upd_cap {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) (X : ℤ) :
    Function.update (xr_heads hk hch hctr hcp hdp) (xr_cap k) X = xr_heads hk hch hctr X hdp := by
  apply xr_bank_ext
  · intro j; rw [Function.update_of_ne (xr_work_ne_cap j), xr_heads_work, xr_heads_work]
  · rw [Function.update_of_ne (xr_choice_ne_cap k), xr_heads_choice, xr_heads_choice]
  · rw [Function.update_of_ne (xr_ctr_ne_cap k), xr_heads_ctr, xr_heads_ctr]
  · rw [Function.update_self, xr_heads_cap]
  · rw [Function.update_of_ne (Ne.symm (xr_cap_ne_dep k)), xr_heads_dep, xr_heads_dep]

private theorem xr_heads_upd_dep {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) (X : ℤ) :
    Function.update (xr_heads hk hch hctr hcp hdp) (xr_dep k) X = xr_heads hk hch hctr hcp X := by
  apply xr_bank_ext
  · intro j; rw [Function.update_of_ne (xr_work_ne_dep j), xr_heads_work, xr_heads_work]
  · rw [Function.update_of_ne (xr_choice_ne_dep k), xr_heads_choice, xr_heads_choice]
  · rw [Function.update_of_ne (xr_ctr_ne_dep k), xr_heads_ctr, xr_heads_ctr]
  · rw [Function.update_of_ne (xr_cap_ne_dep k), xr_heads_cap, xr_heads_cap]
  · rw [Function.update_self, xr_heads_dep]

/-- **The catalog rows' result tape.** A row that rewrites the cells `[0, |w|)` of a bank holding
the word `w` at the origin with a same-width word `v` leaves that bank holding `v`. -/
private theorem xr_patch_eq {K : ℕ} (tp : Fin K → ℤ → Option Bool) (hd : Fin K → ℤ) (i : Fin K)
    (hi : hd i = 0) (w v w₀ : List Bool) (hv : v.length = w.length)
    (hw : tp i = FinTM.bufferTape w₀)
    (hlen : w₀.length ≤ w.length) :
    (fun j q => if j = i ∧ hd j ≤ q ∧ q < hd j + (w.length : ℤ) then FinTM.bufferTape v (q - hd j)
      else tp j q) = Function.update tp i (FinTM.bufferTape v) := by
  funext j q
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self, hi, hw, sub_zero, zero_add]
    by_cases h : 0 ≤ q ∧ q < (w.length : ℤ)
    · rw [if_pos ⟨rfl, h⟩]
    · rw [if_neg (fun h' => h h'.2), (xr_bufferTape_eq_none_iff _ _).mpr (by omega),
        (xr_bufferTape_eq_none_iff _ _).mpr (by omega)]
  · rw [Function.update_of_ne hj, if_neg (fun h' => hj h'.1)]

/-! ##### The counter words: little-endian binary values -/

/-- The value of a binary word, little-endian. -/
private def xr_val (w : List Bool) : ℕ := Nat.ofDigits 2 (w.map Bool.toNat)

private theorem xr_val_nil : xr_val [] = 0 := by
  simp [xr_val]

private theorem xr_val_cons (b : Bool) (w : List Bool) :
    xr_val (b :: w) = b.toNat + 2 * xr_val w := by
  simp [xr_val, Nat.ofDigits_cons]

private theorem xr_val_lt (w : List Bool) : xr_val w < 2 ^ w.length := by
  have := Nat.ofDigits_lt_base_pow_length (b := 2) (l := w.map Bool.toNat) (by norm_num)
    (by intro x hx; obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx; cases b <;> simp)
  simpa [xr_val] using this

private theorem xr_val_inj :
    ∀ {w w' : List Bool}, w.length = w'.length → xr_val w = xr_val w' → w = w'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | b :: w, b' :: w', h, hv => by
    rw [xr_val_cons, xr_val_cons] at hv
    have hb : b = b' := by
      cases b <;> cases b' <;> simp at hv ⊢ <;> omega
    subst hb
    have hw : xr_val w = xr_val w' := by omega
    rw [xr_val_inj (by simpa using h) hw]

private theorem xr_val_append_false (w : List Bool) : xr_val (w ++ [false]) = xr_val w := by
  simp [xr_val, Nat.ofDigits_append]

private theorem xr_val_replicate_false (n : ℕ) : xr_val (List.replicate n false) = 0 := by
  induction n with
  | zero => exact xr_val_nil
  | succ n ih => rw [List.replicate_succ, xr_val_cons, ih]; rfl

private theorem xr_val_replicate_true (n : ℕ) : xr_val (List.replicate n true) + 1 = 2 ^ n := by
  induction n with
  | zero => rw [List.replicate_zero, xr_val_nil]; rfl
  | succ n ih => rw [List.replicate_succ, xr_val_cons, pow_succ]; simp only [Bool.toNat_true]; omega

/-- The increment adds one to the value. -/
private theorem xr_incFixed_val : ∀ {w v : List Bool}, incFixed w = some v → xr_val v = xr_val w + 1
  | [], _, h => by rw [incFixed_nil] at h; exact absurd h (by simp)
  | false :: w, v, h => by
    rw [incFixed_false_cons, Option.some.injEq] at h
    subst h
    rw [xr_val_cons, xr_val_cons]
    simp only [Bool.toNat_false, Bool.toNat_true]
    omega
  | true :: w, v, h => by
    rw [incFixed_true_cons] at h
    obtain ⟨v', hv', rfl⟩ := Option.map_eq_some_iff.mp h
    rw [xr_val_cons, xr_val_cons, xr_incFixed_val hv']
    simp only [Bool.toNat_false, Bool.toNat_true]
    omega

/-- At the overflow the word is all `true`, so every same-length word has a value at most its. -/
private theorem xr_incFixed_none_max {w w' : List Bool} (h : incFixed w = none)
    (hlen : w'.length = w.length) : xr_val w' ≤ xr_val w := by
  have hrep := (incFixed_eq_none_iff_replicate w).mp h
  have h1 := xr_val_lt w'
  have h2 := xr_val_replicate_true w.length
  rw [hlen] at h1
  rw [hrep]
  omega

/-- A word not entirely `true` increments. -/
private theorem xr_incFixed_append_false (w : List Bool) :
    ∃ v, incFixed (w ++ [false]) = some v := by
  rcases h : incFixed (w ++ [false]) with _ | v
  · exfalso
    have := (incFixed_eq_none_iff_replicate _).mp h
    have hmem : false ∈ List.replicate (w ++ [false]).length true := by
      rw [← this]; simp
    simp at hmem
  · exact ⟨v, rfl⟩

/-! ##### The phase index, the phase machines and the redirect table -/

/-- The phases of the exhaustive replay. -/
private inductive xr_Ph (k : ℕ) where
  /-- copy the depth word onto the clock's counter -/
  | copy
  /-- the clocked replay -/
  | replay
  /-- the capture test, which also clears the captured output -/
  | test
  /-- rewind the choice head -/
  | crewind
  /-- rewind the input head -/
  | irewind
  /-- pass `n` of the window clear of work tape `j`: `n < 2` leftward, then rightward -/
  | pass (j : Fin k) (n : Fin 6)
  /-- increment the choice word -/
  | inc
  /-- extend the choice word by one `false` (a depth change) -/
  | extC
  /-- extend the depth word by one `false` (a depth change) -/
  | extD
  /-- increment the depth word (a depth change) -/
  | incD
  /-- the end: a stationary anchor the seam reads, the answer in the accept flag -/
  | halt
  deriving DecidableEq, Fintype

/-- The phase index: a phase with the two flags "some branch accepted" and "some branch is live". -/
private abbrev xr_I (k : ℕ) := xr_Ph k × Bool × Bool

/-- Each phase's control. -/
private def xr_PhSt {N : FinNDTM Bool} (C : xr_Clock N) : xr_I N.k → Type
  | (.copy, _, _) => SweepPhase
  | (.replay, _, _) => C.Q
  | (.test, _, _) => xr_St
  | (.crewind, _, _) => xr_St
  | (.irewind, _, _) => xr_St
  | (.pass _ _, _, _) => xr_St
  | (.inc, _, _) => FlagPhase
  | (.extC, _, _) => xr_St
  | (.extD, _, _) => xr_St
  | (.incD, _, _) => FlagPhase
  | (.halt, _, _) => xr_St

private instance xr_PhSt_fintype {N : FinNDTM Bool} (C : xr_Clock N) :
    ∀ i, Fintype (xr_PhSt C i)
  | (.copy, _, _) => inferInstanceAs (Fintype SweepPhase)
  | (.replay, _, _) => inferInstanceAs (Fintype C.Q)
  | (.test, _, _) => inferInstanceAs (Fintype xr_St)
  | (.crewind, _, _) => inferInstanceAs (Fintype xr_St)
  | (.irewind, _, _) => inferInstanceAs (Fintype xr_St)
  | (.pass _ _, _, _) => inferInstanceAs (Fintype xr_St)
  | (.inc, _, _) => inferInstanceAs (Fintype FlagPhase)
  | (.extC, _, _) => inferInstanceAs (Fintype xr_St)
  | (.extD, _, _) => inferInstanceAs (Fintype xr_St)
  | (.incD, _, _) => inferInstanceAs (Fintype FlagPhase)
  | (.halt, _, _) => inferInstanceAs (Fintype xr_St)

private instance xr_PhSt_decEq {N : FinNDTM Bool} (C : xr_Clock N) :
    ∀ i, DecidableEq (xr_PhSt C i)
  | (.copy, _, _) => inferInstanceAs (DecidableEq SweepPhase)
  | (.replay, _, _) => inferInstanceAs (DecidableEq C.Q)
  | (.test, _, _) => inferInstanceAs (DecidableEq xr_St)
  | (.crewind, _, _) => inferInstanceAs (DecidableEq xr_St)
  | (.irewind, _, _) => inferInstanceAs (DecidableEq xr_St)
  | (.pass _ _, _, _) => inferInstanceAs (DecidableEq xr_St)
  | (.inc, _, _) => inferInstanceAs (DecidableEq FlagPhase)
  | (.extC, _, _) => inferInstanceAs (DecidableEq xr_St)
  | (.extD, _, _) => inferInstanceAs (DecidableEq xr_St)
  | (.incD, _, _) => inferInstanceAs (DecidableEq FlagPhase)
  | (.halt, _, _) => inferInstanceAs (DecidableEq xr_St)

/-- The direction of pass `n`: the first two passes move left, the last four right. -/
private def xr_dir (n : Fin 6) : SignType := if n.val < 2 then SignType.neg else SignType.pos

/-- The idle row: stationary everywhere (the `halt` phase, which the host never steps). -/
private def xr_idleTM (K : ℕ) : MultiTapeTM K Bool xr_St where
  q₀ := .start
  tr := fun q _ _ => xr_stay q

/-- The phase machines. -/
private def xr_M {N : FinNDTM Bool} (C : xr_Clock N) :
    ∀ i : xr_I N.k, MultiTapeTM (N.k + 2 + 2) Bool (xr_PhSt C i)
  | (.copy, _, _) => copyTM (N.k + 2 + 2) (xr_dep N.k) (xr_ctr N.k)
  | (.replay, _, _) => xr_replayTM C
  | (.test, _, _) => xr_testTM (N.k + 2 + 2) (xr_cap N.k)
  | (.crewind, _, _) => xr_rewindTM (N.k + 2 + 2) (xr_choice N.k)
  | (.irewind, _, _) => xr_inRewindTM (N.k + 2 + 2)
  | (.pass j n, _, _) => xr_passTM (N.k + 2 + 2) (xr_work N.k j) (xr_dep N.k) (xr_dir n)
  | (.inc, _, _) => incrementTM (N.k + 2 + 2) (xr_choice N.k)
  | (.extC, _, _) => xr_extendTM (N.k + 2 + 2) (xr_choice N.k)
  | (.extD, _, _) => xr_extendTM (N.k + 2 + 2) (xr_dep N.k)
  | (.incD, _, _) => incrementTM (N.k + 2 + 2) (xr_dep N.k)
  | (.halt, _, _) => xr_idleTM (N.k + 2 + 2)

/-- The first phase of the window clear (the increment when `N` has no work tape). -/
private def xr_firstPass {N : FinNDTM Bool} (C : xr_Clock N) (a l : Bool) : Σ i, xr_PhSt C i :=
  if h : 0 < N.k then ⟨(.pass ⟨0, h⟩ 0, a, l), xr_St.run⟩ else ⟨(.inc, a, l), FlagPhase.run⟩

/-- The phase after pass `n` of tape `j`: the next pass, the next tape, or the increment. -/
private def xr_afterPass {N : FinNDTM Bool} (C : xr_Clock N) (a l : Bool) (j : Fin N.k)
    (n : Fin 6) : Σ i, xr_PhSt C i :=
  if h : n.val + 1 < 6 then ⟨(.pass j ⟨n.val + 1, h⟩, a, l), xr_St.run⟩
  else if h' : j.val + 1 < N.k then ⟨(.pass ⟨j.val + 1, h'⟩ 0, a, l), xr_St.run⟩
  else ⟨(.inc, a, l), FlagPhase.run⟩

/-- The redirect of a leaf row's anchor `done b` at phase `i`, when the phase redirects on a
`done` state at all. -/
private def xr_redDone {N : FinNDTM Bool} (C : xr_Clock N) (i : xr_I N.k) (b : Bool) :
    Option (Σ i, xr_PhSt C i) :=
  match i with
  | (.test, a, l) => some ⟨(.crewind, a || b, l), xr_St.start⟩
  | (.crewind, a, l) => if b then some ⟨(.irewind, a, l), xr_St.start⟩ else none
  | (.irewind, a, l) => if b then some (xr_firstPass C a l) else none
  | (.pass j n, a, l) => if b then some (xr_afterPass C a l j n) else none
  | (.extC, a, l) => if b then some ⟨(.extD, a, l), xr_St.run⟩ else none
  | (.extD, a, l) => if b then some ⟨(.incD, a, l), FlagPhase.run⟩ else none
  | _ => none

open Classical in
/-- The redirect table. -/
private noncomputable def xr_red {N : FinNDTM Bool} (C : xr_Clock N) :
    ∀ i : xr_I N.k, xr_PhSt C i → Option (Σ i, xr_PhSt C i)
  | (.copy, a, l), s => if s = SweepPhase.done then some ⟨(.replay, a, l), C.inj N.tm.q₀⟩ else none
  | (.replay, a, l), q =>
    if ∃ r, q = C.finish r then some ⟨(.test, a, l), xr_St.start⟩
    else if ∃ r, q = C.timeout r then some ⟨(.test, a, true), xr_St.start⟩ else none
  | (.test, a, l), s => match s with | .done b => xr_redDone C (.test, a, l) b | _ => none
  | (.crewind, a, l), s => match s with | .done b => xr_redDone C (.crewind, a, l) b | _ => none
  | (.irewind, a, l), s => match s with | .done b => xr_redDone C (.irewind, a, l) b | _ => none
  | (.pass j n, a, l), s => match s with | .done b => xr_redDone C (.pass j n, a, l) b | _ => none
  | (.inc, a, l), s =>
    match s with
    | .done true => some ⟨(.copy, a, l), SweepPhase.sweep⟩
    | .done false =>
      some (if l then ⟨(.extC, false, false), xr_St.run⟩ else ⟨(.halt, a, false), xr_St.start⟩)
    | _ => none
  | (.extC, a, l), s => match s with | .done b => xr_redDone C (.extC, a, l) b | _ => none
  | (.extD, a, l), s => match s with | .done b => xr_redDone C (.extD, a, l) b | _ => none
  | (.incD, a, l), s => match s with | .done _ => some ⟨(.copy, a, l), SweepPhase.sweep⟩ | _ => none
  | (.halt, a, l), _ => some ⟨(.halt, a, l), xr_St.start⟩

/-- **The host of the exhaustive replay**: the phase host over the phases above, starting at the
copy with both flags down. The machine `E` is the two-exit seam of this host onto the two
one-step answers. -/
private noncomputable def xr_host {N : FinNDTM Bool} (C : xr_Clock N) :
    MultiTapeTM (N.k + 2 + 2) Bool (Σ i, xr_PhSt C i) :=
  phaseHostTM (xr_M C) ⟨(.copy, false, false), SweepPhase.sweep⟩ (xr_red C)

/-- **One phase of the host.** If phase `i`, started at `s₀` over the tapes `tp` and heads `hd`,
reaches `c'` in `T` steps, `c'` is in a state `s'` that the table redirects to `q'`, and no earlier
state is redirected, then the host, started at `⟨i, s₀⟩` over the same tapes, reaches `c'`'s tapes
and heads in state `q'` in `T + 1` steps. -/
private theorem xr_phase_step {N : FinNDTM Bool} (C : xr_Clock N) {z : List Bool} (i : xr_I N.k)
    (s₀ : xr_PhSt C i) (ip : Fin (z.length + 2)) (tp : Fin (N.k + 2 + 2) → ℤ → Option Bool)
    (hd : Fin (N.k + 2 + 2) → ℤ) (T : ℕ) (c' : Cfg (N.k + 2 + 2) Bool (xr_PhSt C i) z)
    (h : (xr_M C i).runFrom ⟨some s₀, ip, tp, hd, []⟩ T = c') (s' : xr_PhSt C i)
    (hs' : c'.state = some s') (hout : c'.output = []) (q' : Σ i, xr_PhSt C i)
    (hred : xr_red C i s' = some q')
    (hguard : ∀ u < T, ∀ s, ((xr_M C i).runFrom ⟨some s₀, ip, tp, hd, []⟩ u).state = some s →
      xr_red C i s = none) :
    (xr_host C).runFrom ⟨some ⟨i, s₀⟩, ip, tp, hd, []⟩ (T + 1) =
      ⟨some q', c'.inputPos, c'.workTapes, c'.workTapePos, []⟩ := by
  have hstart : (⟨some ⟨i, s₀⟩, ip, tp, hd, []⟩ : Cfg (N.k + 2 + 2) Bool (Σ i, xr_PhSt C i) z) =
      (⟨some s₀, ip, tp, hd, []⟩ : Cfg (N.k + 2 + 2) Bool (xr_PhSt C i) z).mapState
        (Sigma.mk i) := by
    apply Cfg.ext
    · rw [Cfg.mapState_state]; rfl
    · rw [Cfg.mapState_inputPos]
    · funext j p; rw [Cfg.mapState_workTapes]
    · funext j; rw [Cfg.mapState_workTapePos]
    · rw [Cfg.mapState_output]
  have hhost := (phaseHostTM_run (xr_M C) ⟨(.copy, false, false), SweepPhase.sweep⟩ (xr_red C) i _
    c' T h s' hs' q' hred hguard).2
  rw [hstart]
  show (phaseHostTM (xr_M C) ⟨(.copy, false, false), SweepPhase.sweep⟩ (xr_red C)).runFrom _
    (T + 1) = _
  rw [hhost]
  apply Cfg.ext
  · rw [Cfg.mapState_state, hs']; rfl
  · rw [Cfg.mapState_inputPos]
  · funext j p; rw [Cfg.mapState_workTapes]
  · funext j; rw [Cfg.mapState_workTapePos]
  · rw [Cfg.mapState_output, hout]

/-! #### One cycle: the phases of one replay, on the host

The configurations between phases, by banks, and each phase's effect on the host, from the
rows' run lemmas through `xr_phase_step`. -/

/-- `E` at the start of a cycle at depth `|s|`: the copy phase with the flags `a` and `l`, the
depth word `wL` on the depth tape, the choice word `s`, some word `u` on the counter, the capture
tape blank, `N`'s tapes blank with their heads at `h`, the input head at `1`. -/
private def xr_cycle {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (wL s u : List Bool) (h : Fin N.k → ℤ) : Cfg (N.k + 2 + 2) Bool (Σ i, xr_PhSt C i) z :=
  ⟨some ⟨(.copy, a, l), SweepPhase.sweep⟩, 1,
    xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u) (FinTM.bufferTape [])
      (FinTM.bufferTape wL),
    xr_heads h 0 0 0 0, []⟩

/-- `E` at the end of a depth, after the choice word's overflow: the deepening when some branch
was live, else the answer; the choice tape holds the all-`false` word again. -/
private def xr_depthEnd {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (L : ℕ) (wL u : List Bool) (h : Fin N.k → ℤ) : Cfg (N.k + 2 + 2) Bool (Σ i, xr_PhSt C i) z :=
  ⟨some (if l then ⟨(.extC, false, false), xr_St.run⟩ else ⟨(.halt, a, false), xr_St.start⟩), 1,
    xr_tapes (fun _ _ => none) (FinTM.bufferTape (List.replicate L false)) (FinTM.bufferTape u)
      (FinTM.bufferTape []) (FinTM.bufferTape wL),
    xr_heads h 0 0 0 0, []⟩

/-- A branch of length `|s|` moves the input head at most `|s|` cells from its start at `1`
(through the replay machine and `Turing.MultiTapeTM.timed_input_bound`). -/
private theorem xr_branch_inputPos_le {N : FinNDTM Bool} (z s : List Bool) :
    (N.tm.runWith s (N.tm.initCfg z)).inputPos.val ≤ 1 + s.length := by
  obtain ⟨p, -, -, hrun⟩ := NDTM.replayTM_runFrom N.tm (N.tm.initCfg z) s s.length le_rfl
  have h := MultiTapeTM.timed_input_bound (tm := N.tm.replayTM)
    (NDTM.withChoiceTape (N.tm.initCfg z) (FinTM.bufferTape s) 0) s.length
  rw [hrun, NDTM.withChoiceTape_inputPos, NDTM.withChoiceTape_inputPos, List.take_length,
    NDTM.initCfg_eq, Cfg.init_inputPos] at h
  simpa using h

/-! ##### The redirect table, read -/

private theorem xr_red_copy_done {N : FinNDTM Bool} (C : xr_Clock N) (a l : Bool) :
    xr_red C (.copy, a, l) SweepPhase.done = some ⟨(.replay, a, l), C.inj N.tm.q₀⟩ := by
  simp [xr_red]

private theorem xr_red_copy_none {N : FinNDTM Bool} (C : xr_Clock N) (a l : Bool)
    (s : SweepPhase) (hs : s ≠ SweepPhase.done) : xr_red C (.copy, a, l) s = none := by
  simp [xr_red, hs]

private theorem xr_red_replay_finish {N : FinNDTM Bool} (C : xr_Clock N) (a l : Bool)
    (r : Option N.State) :
    xr_red C (.replay, a, l) (C.finish r) = some ⟨(.test, a, l), xr_St.start⟩ := by
  show (if ∃ r', C.finish r = C.finish r' then _ else _) = _
  rw [if_pos ⟨r, rfl⟩]

private theorem xr_red_replay_timeout {N : FinNDTM Bool} (C : xr_Clock N) (a l : Bool)
    (r : Option N.State) :
    xr_red C (.replay, a, l) (C.timeout r) = some ⟨(.test, a, true), xr_St.start⟩ := by
  show (if ∃ r', C.timeout r = C.finish r' then _
    else if ∃ r', C.timeout r = C.timeout r' then _ else _) = _
  rw [if_neg (fun ⟨r', hr'⟩ => C.finish_ne_timeout r' r hr'.symm), if_pos ⟨r, rfl⟩]

private theorem xr_red_replay_none {N : FinNDTM Bool} (C : xr_Clock N) (a l : Bool) (q : C.Q)
    (hq : ∀ r, q ≠ C.finish r ∧ q ≠ C.timeout r) : xr_red C (.replay, a, l) q = none := by
  show (if ∃ r', q = C.finish r' then _ else if ∃ r', q = C.timeout r' then _ else _) = _
  rw [if_neg (fun ⟨r', hr'⟩ => (hq r').1 hr'), if_neg (fun ⟨r', hr'⟩ => (hq r').2 hr')]

/-- The phases run by a leaf row redirect only at a `done` anchor. -/
private theorem xr_red_leaf_none {N : FinNDTM Bool} (C : xr_Clock N) (i : xr_I N.k)
    (hi : (∃ a l, i = (.test, a, l)) ∨ (∃ a l, i = (.crewind, a, l)) ∨
      (∃ a l, i = (.irewind, a, l)) ∨ (∃ j n a l, i = (.pass j n, a, l)) ∨
      (∃ a l, i = (.extC, a, l)) ∨ (∃ a l, i = (.extD, a, l)))
    (s : xr_St) (hs : ¬ ∃ b, s = .done b) :
    ∀ (e : xr_PhSt C i = xr_St), xr_red C i (e ▸ s) = none := by
  intro e
  rcases hi with h | h | h | h | h | h
  all_goals first
    | (obtain ⟨a, l, rfl⟩ := h; cases s <;> first | rfl | exact absurd ⟨_, rfl⟩ hs)
    | (obtain ⟨j, n, a, l, rfl⟩ := h; cases s <;> first | rfl | exact absurd ⟨_, rfl⟩ hs)

/-! ##### The copy phase -/

/-- **The copy phase on the host.** From the start of a cycle, `2|wL| + 3` steps copy the depth
word onto the counter and dispatch to the replay. -/
private theorem xr_copy_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (wL s u : List Bool) (h : Fin N.k → ℤ) (hu : u.length ≤ wL.length) :
    (xr_host C).runFrom (xr_cycle C z a l wL s u h) (2 * wL.length + 3) =
      ⟨some ⟨(.replay, a, l), C.inj N.tm.q₀⟩, 1,
        xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape wL) (FinTM.bufferTape [])
          (FinTM.bufferTape wL),
        xr_heads h 0 0 0 0, []⟩ := by
  obtain ⟨hcfg, hguard, -⟩ := copyTM_run_ofCfg (xr_dep N.k) (xr_ctr N.k) (xr_ctr_ne_dep N.k).symm wL
    (⟨some SweepPhase.sweep, 1, xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u)
      (FinTM.bufferTape []) (FinTM.bufferTape wL), xr_heads h 0 0 0 0, []⟩ :
      Cfg (N.k + 2 + 2) Bool SweepPhase z) rfl
    (by intro p _ _; dsimp only; rw [xr_tapes_dep, xr_heads_dep, zero_add])
  rw [xr_cycle, xr_phase_step C (.copy, a, l) SweepPhase.sweep 1 _ _ (2 * wL.length + 2) _ hcfg
    SweepPhase.done rfl rfl _ (xr_red_copy_done C a l)
    (fun t ht s hs => by
      cases s with
      | done => exact absurd hs (hguard t ht)
      | sweep => exact xr_red_copy_none C a l _ (by simp)
      | rewind => exact xr_red_copy_none C a l _ (by simp))]
  dsimp only
  rw [xr_patch_eq _ _ (xr_ctr N.k) (xr_heads_ctr _ _ _ _ _) wL wL u rfl (xr_tapes_ctr _ _ _ _ _) hu,
    xr_tapes_upd_ctr]

/-! ##### The replay phase -/

/-- **The replay phase on the host.** From the copy's end, the clocked replay of the choice word
`s` runs, within `5|s| + 2|wL| + 3` steps, to the capture test, raising the live flag exactly when
the branch along `s` is live after `|s|` steps; the tapes hold the branch's configuration,
translated by `h`, with the output captured. -/
private theorem xr_replay_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (wL s : List Bool) (h : Fin N.k → ℤ) (hval : xr_val wL = s.length) :
    ∃ T ≤ 5 * s.length + 2 * wL.length + 3, ∃ p ≤ s.length, ∃ w' : List Bool,
      w'.length = wL.length ∧
      (xr_host C).runFrom ⟨some ⟨(.replay, a, l), C.inj N.tm.q₀⟩, 1,
        xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape wL) (FinTM.bufferTape [])
          (FinTM.bufferTape wL), xr_heads h 0 0 0 0, []⟩ T =
      ⟨some ⟨(.test, a, l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome), xr_St.start⟩,
        (N.tm.runWith s (N.tm.initCfg z)).inputPos,
        xr_tapes (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapes (FinTM.bufferTape s)
          (FinTM.bufferTape w') (FinTM.bufferTape (N.tm.runWith s (N.tm.initCfg z)).output)
          (FinTM.bufferTape wL),
        xr_heads (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapePos p 0
          ((N.tm.runWith s (N.tm.initCfg z)).output.length : ℤ) 0, []⟩ := by
  classical
  by_cases hb : (N.tm.runWith s (N.tm.initCfg z)).state = none
  · -- the branch halts: the `finish` exit at the first halting time
    have hex : ∃ u, (N.tm.runWith (s.take u) (N.tm.initCfg z)).state = none :=
      ⟨s.length, by rw [List.take_length]; exact hb⟩
    set τ := Nat.find hex with hτdef
    have hτ : τ ≤ s.length := Nat.find_min' hex (by rw [List.take_length]; exact hb)
    have hhalt : (N.tm.runWith (s.take τ) (N.tm.initCfg z)).state = none := Nat.find_spec hex
    have hlive : ∀ u < τ, (N.tm.runWith (s.take u) (N.tm.initCfg z)).state ≠ none :=
      fun u hu => Nat.find_min hex hu
    have hbτ : N.tm.runWith s (N.tm.initCfg z) = N.tm.runWith (s.take τ) (N.tm.initCfg z) := by
      conv_lhs => rw [← List.take_append_drop τ s]
      rw [NDTM.runWith_append, NDTM.runWith_of_halt _ hhalt]
    obtain ⟨T, hT, p, hp, w', hw', hrun, hguard⟩ :=
      xr_replay_finish C z s wL wL h (by rw [← hval]; rfl) τ hτ hhalt hlive
    refine ⟨T + 1, by omega, p, hp.trans hτ, w', hw', ?_⟩
    rw [xr_phase_step C (.replay, a, l) (C.inj N.tm.q₀) 1 _ _ T _ hrun (C.finish none) rfl rfl _
      (xr_red_replay_finish C a l none)
      (fun u hu q hq => xr_red_replay_none C a l q (fun r =>
        ⟨fun h => (hguard u hu r).1 (by rw [h] at hq; exact hq),
          fun h => (hguard u hu r).2 (by rw [h] at hq; exact hq)⟩))]
    rw [hbτ, hhalt, Option.isSome_none, Bool.or_false]
  · -- the branch is live: the `timeout` exit
    have hlive : ∀ u ≤ s.length, (N.tm.runWith (s.take u) (N.tm.initCfg z)).state ≠ none := by
      intro u hu hhalt
      apply hb
      conv_lhs => rw [← List.take_append_drop u s]
      rw [NDTM.runWith_append, NDTM.runWith_of_halt _ hhalt]
      exact hhalt
    obtain ⟨T, hT, p, hp, w', hw', hrun, hguard⟩ :=
      xr_replay_timeout C z s wL wL h (by rw [← hval]; rfl) hlive
    refine ⟨T + 1, by omega, p, hp, w', hw', ?_⟩
    rw [xr_phase_step C (.replay, a, l) (C.inj N.tm.q₀) 1 _ _ T _ hrun _ rfl rfl _
      (xr_red_replay_timeout C a l _)
      (fun u hu q hq => xr_red_replay_none C a l q (fun r =>
        ⟨fun h => (hguard u hu r).1 (by rw [h] at hq; exact hq),
          fun h => (hguard u hu r).2 (by rw [h] at hq; exact hq)⟩))]
    rw [Option.isSome_iff_ne_none.mpr hb, Bool.or_true]

/-! ##### The capture test, the choice rewind, the input rewind -/

/-- **The capture test on the host.** With the output `out` captured, within `|out| + 3` steps the
host clears it, returns the capture head, raises the accept flag exactly when `out = [true]`, and
dispatches to the choice rewind. -/
private theorem xr_test_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (ip : Fin (z.length + 2)) (wk : Fin N.k → ℤ → Option Bool) (ch ctr dp : ℤ → Option Bool)
    (hk : Fin N.k → ℤ) (hch hctr hdp : ℤ) (out : List Bool) :
    ∃ T ≤ out.length + 3,
      (xr_host C).runFrom ⟨some ⟨(.test, a, l), xr_St.start⟩, ip,
        xr_tapes wk ch ctr (FinTM.bufferTape out) dp, xr_heads hk hch hctr (out.length : ℤ) hdp, []⟩
        T =
      ⟨some ⟨(.crewind, a || decide (out = [true]), l), xr_St.start⟩, ip,
        xr_tapes wk ch ctr (FinTM.bufferTape []) dp, xr_heads hk hch hctr 0 hdp, []⟩ := by
  have hrun := xr_testTM_run (xr_cap N.k) out
    (⟨some xr_St.start, ip, xr_tapes wk ch ctr (FinTM.bufferTape out) dp,
      xr_heads hk hch hctr (out.length : ℤ) hdp, []⟩ : Cfg (N.k + 2 + 2) Bool xr_St z) rfl
    (xr_tapes_cap _ _ _ _ _) (xr_heads_cap _ _ _ _ _)
  obtain ⟨T', hT', hrun', hguard⟩ := xr_firstArrival' (xr_testTM (N.k + 2 + 2) (xr_cap N.k))
    (fun s => ∃ b, s = .done b) (xr_done_stationary _ (fun b inp w => rfl)) hrun rfl ⟨_, rfl⟩
  refine ⟨T' + 1, by omega, ?_⟩
  rw [xr_phase_step C (.test, a, l) xr_St.start ip _ _ T' _ hrun' _ rfl rfl
    ⟨(.crewind, a || decide (out = [true]), l), xr_St.start⟩ rfl
    (fun u hu s hs =>
      xr_red_leaf_none C (.test, a, l) (Or.inl ⟨a, l, rfl⟩) s (hguard u hu s hs) rfl)]
  dsimp only
  rw [xr_tapes_upd_cap, xr_heads_upd_cap, FinTM.bufferTape_nil]

/-- **The choice rewind on the host.** With the choice head at `p ≤ |s|`, within `p + 3` steps the
host returns it to the origin and dispatches to the input rewind. -/
private theorem xr_crewind_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (ip : Fin (z.length + 2)) (wk : Fin N.k → ℤ → Option Bool) (s : List Bool)
    (ctr cp dp : ℤ → Option Bool) (hk : Fin N.k → ℤ) (p : ℕ) (hp : p ≤ s.length)
    (hctr hcp hdp : ℤ) :
    ∃ T ≤ p + 3,
      (xr_host C).runFrom ⟨some ⟨(.crewind, a, l), xr_St.start⟩, ip,
        xr_tapes wk (FinTM.bufferTape s) ctr cp dp, xr_heads hk (p : ℤ) hctr hcp hdp, []⟩ T =
      ⟨some ⟨(.irewind, a, l), xr_St.start⟩, ip, xr_tapes wk (FinTM.bufferTape s) ctr cp dp,
        xr_heads hk 0 hctr hcp hdp, []⟩ := by
  have hrun := xr_rewindTM_run (xr_choice N.k) s p hp
    (⟨some xr_St.start, ip, xr_tapes wk (FinTM.bufferTape s) ctr cp dp,
      xr_heads hk (p : ℤ) hctr hcp hdp, []⟩ : Cfg (N.k + 2 + 2) Bool xr_St z) rfl
    (xr_tapes_choice _ _ _ _ _) (xr_heads_choice _ _ _ _ _)
  obtain ⟨T', hT', hrun', hguard⟩ := xr_firstArrival' (xr_rewindTM (N.k + 2 + 2) (xr_choice N.k))
    (fun s => ∃ b, s = .done b) (xr_done_stationary _ (fun b inp w => rfl)) hrun rfl ⟨_, rfl⟩
  refine ⟨T' + 1, by omega, ?_⟩
  rw [xr_phase_step C (.crewind, a, l) xr_St.start ip _ _ T' _ hrun' _ rfl rfl
    ⟨(.irewind, a, l), xr_St.start⟩ rfl
    (fun u hu s hs => xr_red_leaf_none C (.crewind, a, l) (Or.inr (Or.inl ⟨a, l, rfl⟩)) s
      (hguard u hu s hs) rfl)]
  dsimp only
  rw [xr_heads_upd_choice]

/-- **The input rewind on the host.** Within `inputPos + 3` steps the host returns the input head
to `1` and dispatches to the window clear (or to the increment when `N` has no work tape). -/
private theorem xr_irewind_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (ip : Fin (z.length + 2)) (tp : Fin (N.k + 2 + 2) → ℤ → Option Bool)
    (hd : Fin (N.k + 2 + 2) → ℤ) :
    ∃ T ≤ ip.val + 3,
      (xr_host C).runFrom ⟨some ⟨(.irewind, a, l), xr_St.start⟩, ip, tp, hd, []⟩ T =
        ⟨some (xr_firstPass C a l), 1, tp, hd, []⟩ := by
  obtain ⟨T₀, hT₀, hrun₀⟩ := FinTM.timed_rewind (xr_inRewindTM (N.k + 2 + 2)) .start .run
    (some (.done true)) (fun inp work => rfl) (fun inp work => by cases inp <;> rfl)
    (⟨some xr_St.start, ip, tp, hd, []⟩ : Cfg (N.k + 2 + 2) Bool xr_St z) rfl
  have hT₀' : T₀ ≤ ip.val + 2 := hT₀
  obtain ⟨T', hT', hrun, hguard⟩ := xr_firstArrival' (xr_inRewindTM (N.k + 2 + 2))
    (fun s => ∃ b, s = .done b) (xr_done_stationary _ (fun b inp w => rfl)) hrun₀ rfl ⟨_, rfl⟩
  refine ⟨T' + 1, by omega, ?_⟩
  rw [xr_phase_step C (.irewind, a, l) xr_St.start ip tp hd T' _ hrun (.done true) rfl rfl
    (xr_firstPass C a l) rfl
    (fun u hu s hs => xr_red_leaf_none C (.irewind, a, l) (Or.inr (Or.inr (Or.inl ⟨a, l, rfl⟩))) s
      (hguard u hu s hs) rfl)]

/-! ##### The increment of the choice word -/

/-- **The increment on the host, a successor.** When `incFixed s = some s'`, within `2|s| + 3`
steps the host writes `s'` on the choice tape and dispatches to the next cycle. -/
private theorem xr_inc_host_succ {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (wL s s' u : List Bool) (hs' : incFixed s = some s') (hk : Fin N.k → ℤ) :
    ∃ T ≤ 2 * s.length + 3,
      (xr_host C).runFrom ⟨some ⟨(.inc, a, l), FlagPhase.run⟩, 1,
        xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u) (FinTM.bufferTape [])
          (FinTM.bufferTape wL), xr_heads hk 0 0 0 0, []⟩ T = xr_cycle C z a l wL s' u hk := by
  obtain ⟨hcfg, hguard, -⟩ := incrementTM_run_succ_ofCfg (xr_choice N.k) s s' hs'
    (⟨some FlagPhase.run, 1, xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u)
      (FinTM.bufferTape []) (FinTM.bufferTape wL), xr_heads hk 0 0 0 0, []⟩ :
      Cfg (N.k + 2 + 2) Bool FlagPhase z) rfl
    (by intro p _ _; dsimp only; rw [xr_tapes_choice, xr_heads_choice, zero_add])
  refine ⟨2 * (s.takeWhile id).length + 2 + 1, by
    have := (List.takeWhile_sublist (l := s) id).length_le; omega, ?_⟩
  rw [xr_phase_step C (.inc, a, l) FlagPhase.run 1 _ _ _ _ hcfg (FlagPhase.done true) rfl rfl
    ⟨(.copy, a, l), SweepPhase.sweep⟩ rfl
    (fun t ht s hs => by
      cases s with
      | done b => exact absurd hs (hguard t ht b)
      | run => rfl
      | rewind b => rfl)]
  dsimp only
  rw [xr_patch_eq _ _ (xr_choice N.k) (xr_heads_choice _ _ _ _ _) s s' s (incFixed_length hs')
    (xr_tapes_choice _ _ _ _ _) le_rfl, xr_tapes_upd_choice]
  rfl

/-- **The increment on the host, the overflow.** When `incFixed s = none`, `2|s| + 3` steps leave
the all-`false` word on the choice tape and dispatch to the depth's end. -/
private theorem xr_inc_host_overflow {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool)
    (a l : Bool) (wL s u : List Bool) (hs : incFixed s = none) (hk : Fin N.k → ℤ) :
    (xr_host C).runFrom ⟨some ⟨(.inc, a, l), FlagPhase.run⟩, 1,
        xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u) (FinTM.bufferTape [])
          (FinTM.bufferTape wL), xr_heads hk 0 0 0 0, []⟩ (2 * s.length + 3) =
      xr_depthEnd C z a l s.length wL u hk := by
  obtain ⟨hcfg, hguard, -⟩ := incrementTM_run_overflow_ofCfg (xr_choice N.k) s hs
    (⟨some FlagPhase.run, 1, xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u)
      (FinTM.bufferTape []) (FinTM.bufferTape wL), xr_heads hk 0 0 0 0, []⟩ :
      Cfg (N.k + 2 + 2) Bool FlagPhase z) rfl
    (by intro p _ _; dsimp only; rw [xr_tapes_choice, xr_heads_choice, zero_add])
  rw [show 2 * s.length + 3 = 2 * s.length + 2 + 1 from rfl,
    xr_phase_step C (.inc, a, l) FlagPhase.run 1 _ _ _ _ hcfg (FlagPhase.done false) rfl rfl
    (if l then ⟨(.extC, false, false), xr_St.run⟩ else ⟨(.halt, a, false), xr_St.start⟩) rfl
    (fun t ht s hs => by
      cases s with
      | done b => exact absurd hs (hguard t ht b)
      | run => rfl
      | rewind b => rfl)]
  dsimp only
  rw [xr_patch_eq _ _ (xr_choice N.k) (xr_heads_choice _ _ _ _ _) s
    (List.replicate s.length false) s List.length_replicate (xr_tapes_choice _ _ _ _ _) le_rfl,
    xr_tapes_upd_choice]
  rfl

/-! ##### The window clear on the host -/

/-- Content within radius `R` of the cell `a`. -/
private def xr_Win (f : ℤ → Option Bool) (a R : ℤ) : Prop :=
  ∀ p, f p ≠ none → a - R ≤ p ∧ p ≤ a + R

/-- Blank on `[lo, hi]`. -/
private def xr_Blank (f : ℤ → Option Bool) (lo hi : ℤ) : Prop :=
  ∀ p, lo ≤ p → p ≤ hi → f p = none

private theorem xr_dir_cast (n : Fin 6) :
    ((xr_dir n : SignType) : ℤ) = if n.val < 2 then -1 else 1 := by
  unfold xr_dir
  split_ifs <;> rfl

/-- The phase at which the window clear of tape `m` starts (the increment when `m = N.k`). -/
private def xr_passStart {N : FinNDTM Bool} (C : xr_Clock N) (a l : Bool) (m : ℕ) :
    Σ i, xr_PhSt C i :=
  if h : m < N.k then ⟨(.pass ⟨m, h⟩ 0, a, l), xr_St.run⟩ else ⟨(.inc, a, l), FlagPhase.run⟩

private theorem xr_firstPass_eq {N : FinNDTM Bool} (C : xr_Clock N) (a l : Bool) :
    xr_firstPass C a l = xr_passStart C a l 0 := rfl

private theorem xr_afterPass_last {N : FinNDTM Bool} (C : xr_Clock N) (a l : Bool) (j : Fin N.k) :
    xr_afterPass C a l j ⟨5, by omega⟩ = xr_passStart C a l (j.val + 1) := by
  unfold xr_afterPass xr_passStart
  rw [dif_neg (by decide)]

/-- **One pass on the host.** From the start of pass `n` of tape `j`, within `2|wL| + 3` steps head
`j` moves `|wL|` cells along the pass's direction, the cells between its start and its end are
blanked, the ruler head returns, and the host dispatches to the next pass. -/
private theorem xr_pass_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (ip : Fin (z.length + 2)) (wk : Fin N.k → ℤ → Option Bool) (ch ctr cp : ℤ → Option Bool)
    (wL : List Bool) (hk : Fin N.k → ℤ) (hch hctr hcp : ℤ) (j : Fin N.k) (n : Fin 6) :
    ∃ T ≤ 2 * wL.length + 3, ∃ f : ℤ → Option Bool,
      (xr_host C).runFrom ⟨some ⟨(.pass j n, a, l), xr_St.run⟩, ip,
        xr_tapes wk ch ctr cp (FinTM.bufferTape wL), xr_heads hk hch hctr hcp 0, []⟩ T =
      ⟨some (xr_afterPass C a l j n), ip, xr_tapes (Function.update wk j f) ch ctr cp
        (FinTM.bufferTape wL),
        xr_heads (Function.update hk j (hk j + wL.length * (if n.val < 2 then -1 else 1))) hch hctr
          hcp 0, []⟩ ∧
      (∀ p : ℤ, (∃ i : ℕ, i ≤ wL.length ∧ p = hk j + i * (if n.val < 2 then -1 else 1)) →
        f p = none) ∧
      (∀ p, f p = none ∨ f p = wk j p) := by
  obtain ⟨f, hrun, hblank, hkeep⟩ := xr_passTM_run (xr_work N.k j) (xr_dep N.k) (xr_work_ne_dep j)
    (xr_dir n) wL
    (⟨some xr_St.run, ip, xr_tapes wk ch ctr cp (FinTM.bufferTape wL),
      xr_heads hk hch hctr hcp 0, []⟩ : Cfg (N.k + 2 + 2) Bool xr_St z) rfl
    (xr_tapes_dep _ _ _ _ _) (xr_heads_dep _ _ _ _ _)
  simp only [xr_heads_work, xr_tapes_work, xr_dir_cast] at hrun hblank hkeep
  obtain ⟨T', hT', hrun', hguard⟩ := xr_firstArrival' (xr_passTM (N.k + 2 + 2) (xr_work N.k j)
    (xr_dep N.k) (xr_dir n)) (fun s => ∃ b, s = .done b)
    (xr_done_stationary _ (fun b inp w => rfl)) hrun rfl ⟨_, rfl⟩
  refine ⟨T' + 1, by omega, f, ?_, hblank, ?_⟩
  · rw [xr_phase_step C (.pass j n, a, l) xr_St.run ip _ _ T' _ hrun' _ rfl rfl
      (xr_afterPass C a l j n) rfl
      (fun u hu s hs => xr_red_leaf_none C (.pass j n, a, l)
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, n, a, l, rfl⟩)))) s (hguard u hu s hs) rfl)]
    dsimp only
    rw [xr_tapes_upd_work, xr_heads_upd_work]
  · intro p
    by_cases h : ∃ i : ℕ, i ≤ wL.length ∧ p = hk j + i * (if n.val < 2 then -1 else 1)
    · exact Or.inl (hblank p h)
    · exact Or.inr (hkeep p (fun i hi hp => h ⟨i, hi, hp⟩))

/-- A leftward pass: head `j` moves `|wL|` cells left and `[hk j - |wL|, hk j]` is blanked. -/
private theorem xr_pass_left {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (ip : Fin (z.length + 2)) (wk : Fin N.k → ℤ → Option Bool) (ch ctr cp : ℤ → Option Bool)
    (wL : List Bool) (hk : Fin N.k → ℤ) (hch hctr hcp : ℤ) (j : Fin N.k) (n : Fin 6)
    (hn : n.val < 2) :
    ∃ T ≤ 2 * wL.length + 3, ∃ f : ℤ → Option Bool,
      (xr_host C).runFrom ⟨some ⟨(.pass j n, a, l), xr_St.run⟩, ip,
        xr_tapes wk ch ctr cp (FinTM.bufferTape wL), xr_heads hk hch hctr hcp 0, []⟩ T =
      ⟨some (xr_afterPass C a l j n), ip, xr_tapes (Function.update wk j f) ch ctr cp
        (FinTM.bufferTape wL),
        xr_heads (Function.update hk j (hk j - wL.length)) hch hctr hcp 0, []⟩ ∧
      xr_Blank f (hk j - wL.length) (hk j) ∧ (∀ p, f p = none ∨ f p = wk j p) := by
  obtain ⟨T, hT, f, hrun, hbl, hsub⟩ := xr_pass_host C z a l ip wk ch ctr cp wL hk hch hctr hcp j n
  have he : hk j + (wL.length : ℤ) * (-1) = hk j - wL.length := by ring
  rw [if_pos hn, he] at hrun
  refine ⟨T, hT, f, hrun, fun p hlo hhi => hbl p ⟨(hk j - p).toNat, by omega, ?_⟩, hsub⟩
  rw [if_pos hn]
  omega

/-- A rightward pass: head `j` moves `|wL|` cells right and `[hk j, hk j + |wL|]` is blanked. -/
private theorem xr_pass_right {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (ip : Fin (z.length + 2)) (wk : Fin N.k → ℤ → Option Bool) (ch ctr cp : ℤ → Option Bool)
    (wL : List Bool) (hk : Fin N.k → ℤ) (hch hctr hcp : ℤ) (j : Fin N.k) (n : Fin 6)
    (hn : ¬ n.val < 2) :
    ∃ T ≤ 2 * wL.length + 3, ∃ f : ℤ → Option Bool,
      (xr_host C).runFrom ⟨some ⟨(.pass j n, a, l), xr_St.run⟩, ip,
        xr_tapes wk ch ctr cp (FinTM.bufferTape wL), xr_heads hk hch hctr hcp 0, []⟩ T =
      ⟨some (xr_afterPass C a l j n), ip, xr_tapes (Function.update wk j f) ch ctr cp
        (FinTM.bufferTape wL),
        xr_heads (Function.update hk j (hk j + wL.length)) hch hctr hcp 0, []⟩ ∧
      xr_Blank f (hk j) (hk j + wL.length) ∧ (∀ p, f p = none ∨ f p = wk j p) := by
  obtain ⟨T, hT, f, hrun, hbl, hsub⟩ := xr_pass_host C z a l ip wk ch ctr cp wL hk hch hctr hcp j n
  have he : hk j + (wL.length : ℤ) * 1 = hk j + wL.length := by ring
  rw [if_neg hn, he] at hrun
  refine ⟨T, hT, f, hrun, fun p hlo hhi => hbl p ⟨(p - hk j).toNat, by omega, ?_⟩, hsub⟩
  rw [if_neg hn]
  omega

/-- Blank cells stay blank under a pass. -/
private theorem xr_Blank_mono {f g : ℤ → Option Bool} (h : ∀ p, g p = none ∨ g p = f p) {lo hi : ℤ}
    (hf : xr_Blank f lo hi) : xr_Blank g lo hi := by
  intro p hlo hhi
  rcases h p with h' | h'
  · exact h'
  · rw [h', hf p hlo hhi]

/-- A blank cell stays blank under a pass. -/
private theorem xr_none_mono {f g : ℤ → Option Bool} (h : ∀ p, g p = none ∨ g p = f p) {p : ℤ}
    (hf : f p = none) : g p = none := by
  rcases h p with h' | h'
  · exact h'
  · rw [h', hf]

/-- **The window clear of one tape on the host.** From the start of pass `0` of tape `j`, whose
content lies within radius `2|wL|` of its head, within `6(2|wL| + 3)` steps the six passes blank
the tape and move its head `2|wL|` cells right; the host dispatches to the next tape (or the
increment). -/
private theorem xr_clearTape_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (ip : Fin (z.length + 2)) (wk : Fin N.k → ℤ → Option Bool) (ch ctr cp : ℤ → Option Bool)
    (wL : List Bool) (hk : Fin N.k → ℤ) (hch hctr hcp : ℤ) (j : Fin N.k)
    (hwin : xr_Win (wk j) (hk j) (2 * wL.length)) :
    ∃ T ≤ 6 * (2 * wL.length + 3),
      (xr_host C).runFrom ⟨some ⟨(.pass j ⟨0, by omega⟩, a, l), xr_St.run⟩, ip,
        xr_tapes wk ch ctr cp (FinTM.bufferTape wL), xr_heads hk hch hctr hcp 0, []⟩ T =
      ⟨some (xr_passStart C a l (j.val + 1)), ip,
        xr_tapes (Function.update wk j (fun _ => none)) ch ctr cp (FinTM.bufferTape wL),
        xr_heads (Function.update hk j (hk j + 2 * wL.length)) hch hctr hcp 0, []⟩ := by
  have e0 : xr_afterPass C a l j ⟨0, by omega⟩ =
    ⟨(.pass j ⟨1, by omega⟩, a, l), xr_St.run⟩ := rfl
  have e1 : xr_afterPass C a l j ⟨1, by omega⟩ =
    ⟨(.pass j ⟨2, by omega⟩, a, l), xr_St.run⟩ := rfl
  have e2 : xr_afterPass C a l j ⟨2, by omega⟩ =
    ⟨(.pass j ⟨3, by omega⟩, a, l), xr_St.run⟩ := rfl
  have e3 : xr_afterPass C a l j ⟨3, by omega⟩ =
    ⟨(.pass j ⟨4, by omega⟩, a, l), xr_St.run⟩ := rfl
  have e4 : xr_afterPass C a l j ⟨4, by omega⟩ =
    ⟨(.pass j ⟨5, by omega⟩, a, l), xr_St.run⟩ := rfl
  obtain ⟨T₀, hT₀, f₀, hrun₀, hbl₀, hsub₀⟩ :=
    xr_pass_left C z a l ip wk ch ctr cp wL hk hch hctr hcp j ⟨0, by omega⟩
      (by show (0 : ℕ) < 2; omega)
  rw [e0] at hrun₀
  obtain ⟨T₁, hT₁, f₁, hrun₁, hbl₁, hsub₁⟩ :=
    xr_pass_left C z a l ip (Function.update wk j f₀) ch ctr cp wL
      (Function.update hk j (hk j - wL.length)) hch hctr hcp j ⟨1, by omega⟩
      (by show (1 : ℕ) < 2; omega)
  rw [e1, Function.update_idem, Function.update_self, Function.update_idem] at hrun₁
  rw [Function.update_self] at hbl₁ hsub₁
  obtain ⟨T₂, hT₂, f₂, hrun₂, hbl₂, hsub₂⟩ :=
    xr_pass_right C z a l ip (Function.update wk j f₁) ch ctr cp wL
      (Function.update hk j (hk j - wL.length - wL.length)) hch hctr hcp j ⟨2, by omega⟩
      (by show ¬ ((2 : ℕ) < 2); omega)
  rw [e2, Function.update_idem, Function.update_self, Function.update_idem] at hrun₂
  rw [Function.update_self] at hbl₂ hsub₂
  obtain ⟨T₃, hT₃, f₃, hrun₃, hbl₃, hsub₃⟩ :=
    xr_pass_right C z a l ip (Function.update wk j f₂) ch ctr cp wL
      (Function.update hk j (hk j - wL.length - wL.length + wL.length)) hch hctr hcp j
      ⟨3, by omega⟩ (by show ¬ ((3 : ℕ) < 2); omega)
  rw [e3, Function.update_idem, Function.update_self, Function.update_idem] at hrun₃
  rw [Function.update_self] at hbl₃ hsub₃
  obtain ⟨T₄, hT₄, f₄, hrun₄, hbl₄, hsub₄⟩ :=
    xr_pass_right C z a l ip (Function.update wk j f₃) ch ctr cp wL
      (Function.update hk j (hk j - wL.length - wL.length + wL.length + wL.length)) hch hctr hcp j
      ⟨4, by omega⟩ (by show ¬ ((4 : ℕ) < 2); omega)
  rw [e4, Function.update_idem, Function.update_self, Function.update_idem] at hrun₄
  rw [Function.update_self] at hbl₄ hsub₄
  obtain ⟨T₅, hT₅, f₅, hrun₅, hbl₅, hsub₅⟩ :=
    xr_pass_right C z a l ip (Function.update wk j f₄) ch ctr cp wL
      (Function.update hk j (hk j - wL.length - wL.length + wL.length + wL.length + wL.length))
      hch hctr hcp j ⟨5, by omega⟩ (by show ¬ ((5 : ℕ) < 2); omega)
  rw [xr_afterPass_last, Function.update_idem, Function.update_self, Function.update_idem]
    at hrun₅
  rw [Function.update_self] at hbl₅ hsub₅
  have hf : f₅ = fun _ => none := by
    funext p
    by_cases hin : hk j - 2 * wL.length ≤ p ∧ p ≤ hk j + 2 * wL.length
    · rcases le_or_gt p (hk j - wL.length) with h1 | h1
      · exact xr_Blank_mono hsub₅ (xr_Blank_mono hsub₄ (xr_Blank_mono hsub₃ (xr_Blank_mono hsub₂
          hbl₁))) p (by omega) (by omega)
      · rcases le_or_gt p (hk j) with h2 | h2
        · exact xr_Blank_mono hsub₅ (xr_Blank_mono hsub₄ (xr_Blank_mono hsub₃ (xr_Blank_mono hsub₂
            (xr_Blank_mono hsub₁ hbl₀)))) p (by omega) (by omega)
        · rcases le_or_gt p (hk j + wL.length) with h3 | h3
          · exact xr_Blank_mono hsub₅ hbl₄ p (by omega) (by omega)
          · exact hbl₅ p (by omega) (by omega)
    · have h0 : wk j p = none := by
        by_contra hne
        exact hin (hwin p hne)
      exact xr_none_mono hsub₅ (xr_none_mono hsub₄ (xr_none_mono hsub₃ (xr_none_mono hsub₂
        (xr_none_mono hsub₁ (xr_none_mono hsub₀ h0)))))
  have hh : hk j - wL.length - wL.length + wL.length + wL.length + wL.length + wL.length =
      hk j + 2 * wL.length := by ring
  rw [hf, hh] at hrun₅
  refine ⟨T₀ + T₁ + T₂ + T₃ + T₄ + T₅, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hrun₀, hrun₁, hrun₂, hrun₃, hrun₄, hrun₅]

/-- **The window clear on the host, from tape `N.k - m` on.** The tapes `N.k - m, …, N.k - 1`,
each with its content within radius `2|wL|` of its head, are blanked within `m·6(2|wL| + 3)` steps,
after which the host is at the increment. -/
private theorem xr_clear_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (ip : Fin (z.length + 2)) (ch ctr cp : ℤ → Option Bool) (wL : List Bool) (hch hctr hcp : ℤ) :
    ∀ (m : ℕ), m ≤ N.k → ∀ (wk : Fin N.k → ℤ → Option Bool) (hk : Fin N.k → ℤ),
      (∀ j : Fin N.k, N.k - m ≤ j.val → xr_Win (wk j) (hk j) (2 * wL.length)) →
      ∃ T ≤ m * (6 * (2 * wL.length + 3)), ∃ hk' : Fin N.k → ℤ,
        (xr_host C).runFrom ⟨some (xr_passStart C a l (N.k - m)), ip,
          xr_tapes wk ch ctr cp (FinTM.bufferTape wL), xr_heads hk hch hctr hcp 0, []⟩ T =
        ⟨some ⟨(.inc, a, l), FlagPhase.run⟩, ip,
          xr_tapes (fun j => if N.k - m ≤ j.val then (fun _ => none) else wk j) ch ctr cp
            (FinTM.bufferTape wL),
          xr_heads hk' hch hctr hcp 0, []⟩ := by
  intro m
  induction m with
  | zero =>
    intro _ wk hk _
    refine ⟨0, Nat.zero_le _, hk, ?_⟩
    rw [MultiTapeTM.runFrom_zero]
    have h1 : xr_passStart C a l (N.k - 0) = ⟨(.inc, a, l), FlagPhase.run⟩ := by
      unfold xr_passStart
      rw [dif_neg (by omega)]
    have h2 : (fun j : Fin N.k => if N.k - 0 ≤ j.val then (fun _ : ℤ => (none : Option Bool))
        else wk j) = wk := by
      funext j
      rw [if_neg (by have := j.isLt; omega)]
    rw [h1, h2]
  | succ m ih =>
    intro hm wk hk hwin
    have hj : N.k - (m + 1) < N.k := by omega
    have hstart : xr_passStart C a l (N.k - (m + 1)) =
        ⟨(.pass ⟨N.k - (m + 1), hj⟩ ⟨0, by omega⟩, a, l), xr_St.run⟩ := by
      unfold xr_passStart
      rw [dif_pos hj]
      rfl
    obtain ⟨T₁, hT₁, hrun₁⟩ := xr_clearTape_host C z a l ip wk ch ctr cp wL hk hch hctr hcp
      ⟨N.k - (m + 1), hj⟩ (hwin _ le_rfl)
    have hnext : (⟨N.k - (m + 1), hj⟩ : Fin N.k).val + 1 = N.k - m := by
      show N.k - (m + 1) + 1 = N.k - m
      omega
    rw [hnext] at hrun₁
    obtain ⟨T₂, hT₂, hk', hrun₂⟩ := ih (by omega) (Function.update wk ⟨N.k - (m + 1), hj⟩
      (fun _ => none))
      (Function.update hk ⟨N.k - (m + 1), hj⟩ (hk ⟨N.k - (m + 1), hj⟩ + 2 * wL.length))
      (by
        intro j hjm
        have hne : j ≠ ⟨N.k - (m + 1), hj⟩ := by
          intro h
          rw [h] at hjm
          change N.k - m ≤ N.k - (m + 1) at hjm
          omega
        rw [Function.update_of_ne hne, Function.update_of_ne hne]
        exact hwin j (by omega))
    have htp : (fun j : Fin N.k => if N.k - m ≤ j.val then (fun _ : ℤ => (none : Option Bool))
        else Function.update wk ⟨N.k - (m + 1), hj⟩ (fun _ => none) j) =
        fun j => if N.k - (m + 1) ≤ j.val then (fun _ => none) else wk j := by
      funext j
      by_cases hjj : j = ⟨N.k - (m + 1), hj⟩
      · rw [hjj, if_neg (by change ¬ (N.k - m ≤ N.k - (m + 1)); omega), Function.update_self,
          if_pos (le_refl _)]
      · rw [Function.update_of_ne hjj]
        by_cases h1 : N.k - m ≤ j.val
        · rw [if_pos h1, if_pos (by omega)]
        · have hne : j.val ≠ N.k - (m + 1) := fun h => hjj (Fin.ext h)
          rw [if_neg h1, if_neg (by omega)]
    have hmul : (m + 1) * (6 * (2 * wL.length + 3)) =
        m * (6 * (2 * wL.length + 3)) + 6 * (2 * wL.length + 3) := by ring
    refine ⟨T₁ + T₂, by omega, hk', ?_⟩
    rw [hstart, MultiTapeTM.runFrom_add, hrun₁, hrun₂, htp]

/-! ##### One cycle -/

/-- The branch along `s` keeps `N`'s tapes within radius `2|s|` of its translated heads. -/
private theorem xr_branch_win {N : FinNDTM Bool} (z s : List Bool) (h : Fin N.k → ℤ)
    (j : Fin N.k) :
    xr_Win ((xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapes j)
      ((xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapePos j) (2 * s.length) := by
  obtain ⟨hpos, hblank, -⟩ := xr_window_runWith N.tm z s
  intro q hq
  have h1 := hpos j
  have h2 : ¬ (s.length : ℤ) < |q - h j| := fun hlt => hq (hblank j (q - h j) hlt)
  rw [abs_le] at h1
  push_neg at h2
  rw [abs_le] at h2
  show (N.tm.runWith s (N.tm.initCfg z)).workTapePos j + h j - 2 * s.length ≤ q ∧
    q ≤ (N.tm.runWith s (N.tm.initCfg z)).workTapePos j + h j + 2 * s.length
  omega

/-- **One cycle on the host.** From the start of a cycle at depth `L = |s|` (the depth word has
value `L` and width `L`, the counter width at most `L`), within `(18 N.k + 19)(L + 1)` steps the
host replays the choice word `s`, folds its verdicts into the flags (the output `[true]` raises
the accept flag, a live branch the live flag), restores the tapes, and either dispatches to the
next cycle on `incFixed s`, or, at the overflow, to the depth's end. -/
private theorem xr_cycle_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (wL s u : List Bool) (h : Fin N.k → ℤ) (hval : xr_val wL = s.length)
    (hL : wL.length = s.length) (hu : u.length ≤ wL.length) :
    ∃ T ≤ (18 * N.k + 19) * (s.length + 1), ∃ u' : List Bool, u'.length ≤ wL.length ∧
      ∃ h' : Fin N.k → ℤ,
      (∀ s', incFixed s = some s' →
        (xr_host C).runFrom (xr_cycle C z a l wL s u h) T =
          xr_cycle C z (a || decide ((N.tm.runWith s (N.tm.initCfg z)).output = [true]))
            (l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome) wL s' u' h') ∧
      (incFixed s = none →
        (xr_host C).runFrom (xr_cycle C z a l wL s u h) T =
          xr_depthEnd C z (a || decide ((N.tm.runWith s (N.tm.initCfg z)).output = [true]))
            (l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome) s.length wL u' h') := by
  obtain ⟨-, -, hout⟩ := xr_window_runWith N.tm z s
  have hip := xr_branch_inputPos_le (N := N) z s
  have h1 := xr_copy_host C z a l wL s u h hu
  obtain ⟨T₂, hT₂, p, hp, w', hw', h2⟩ := xr_replay_host C z a l wL s h hval
  obtain ⟨T₃, hT₃, h3⟩ := xr_test_host C z a (l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome)
    (N.tm.runWith s (N.tm.initCfg z)).inputPos
    (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapes (FinTM.bufferTape s)
    (FinTM.bufferTape w') (FinTM.bufferTape wL)
    (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapePos p 0 0
    (N.tm.runWith s (N.tm.initCfg z)).output
  obtain ⟨T₄, hT₄, h4⟩ := xr_crewind_host C z
    (a || decide ((N.tm.runWith s (N.tm.initCfg z)).output = [true]))
    (l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome)
    (N.tm.runWith s (N.tm.initCfg z)).inputPos
    (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapes s (FinTM.bufferTape w')
    (FinTM.bufferTape []) (FinTM.bufferTape wL)
    (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapePos p hp 0 0 0
  obtain ⟨T₅, hT₅, h5⟩ := xr_irewind_host C z
    (a || decide ((N.tm.runWith s (N.tm.initCfg z)).output = [true]))
    (l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome)
    (N.tm.runWith s (N.tm.initCfg z)).inputPos
    (xr_tapes (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapes (FinTM.bufferTape s)
      (FinTM.bufferTape w') (FinTM.bufferTape []) (FinTM.bufferTape wL))
    (xr_heads (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapePos 0 0 0 0)
  rw [xr_firstPass_eq] at h5
  obtain ⟨T₆, hT₆, hk', h6⟩ := xr_clear_host C z
    (a || decide ((N.tm.runWith s (N.tm.initCfg z)).output = [true]))
    (l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome) 1 (FinTM.bufferTape s)
    (FinTM.bufferTape w') (FinTM.bufferTape []) wL 0 0 0 N.k le_rfl
    (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapes
    (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapePos
    (fun j _ => by rw [hL]; exact xr_branch_win z s h j)
  rw [Nat.sub_self] at h6
  have hblank : (fun j : Fin N.k => if 0 ≤ j.val then (fun _ : ℤ => (none : Option Bool))
      else (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapes j) = fun _ _ => none := by
    funext j
    rw [if_pos (Nat.zero_le _)]
  rw [hblank] at h6
  have hchain : ∀ T₇, (xr_host C).runFrom (xr_cycle C z a l wL s u h)
      (2 * wL.length + 3 + T₂ + T₃ + T₄ + T₅ + T₆ + T₇) =
      (xr_host C).runFrom ⟨some ⟨(.inc,
        a || decide ((N.tm.runWith s (N.tm.initCfg z)).output = [true]),
        l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome), FlagPhase.run⟩, 1,
        xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape w') (FinTM.bufferTape [])
          (FinTM.bufferTape wL), xr_heads hk' 0 0 0 0, []⟩ T₇ := by
    intro T₇
    rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, h1, h2, h3, h4, h5,
      h6]
  have hbound : 2 * wL.length + 3 + T₂ + T₃ + T₄ + T₅ + T₆ + (2 * s.length + 3) ≤
      (18 * N.k + 19) * (s.length + 1) := by
    have e1 : N.k * (6 * (2 * wL.length + 3)) = 12 * (N.k * s.length) + 18 * N.k := by
      rw [hL]
      ring
    have e2 : (18 * N.k + 19) * (s.length + 1) =
        18 * (N.k * s.length) + 18 * N.k + 19 * s.length + 19 := by
      ring
    omega
  rcases hs : incFixed s with _ | s'
  · -- the overflow
    have h7 := xr_inc_host_overflow C z
      (a || decide ((N.tm.runWith s (N.tm.initCfg z)).output = [true]))
      (l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome) wL s w' hs hk'
    refine ⟨2 * wL.length + 3 + T₂ + T₃ + T₄ + T₅ + T₆ + (2 * s.length + 3), hbound, w', hw'.le,
      hk',
      (fun s' hs' => nomatch hs'), fun _ => ?_⟩
    rw [hchain, h7]
  · -- a successor
    obtain ⟨T₇, hT₇, h7⟩ := xr_inc_host_succ C z
      (a || decide ((N.tm.runWith s (N.tm.initCfg z)).output = [true]))
      (l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome) wL s s' w' hs hk'
    refine ⟨2 * wL.length + 3 + T₂ + T₃ + T₄ + T₅ + T₆ + T₇, by omega, w', hw'.le, hk',
      fun s'' hs'' => ?_, (fun h0 => nomatch h0)⟩
    rw [Option.some.injEq] at hs''
    subst hs''
    rw [hchain, h7]

/-! #### One depth, the depth change -/

/-- **One depth on the host.** From the cycle at the word `s`, with `m = 2^L - val s` words of
depth `L` left to replay, the host runs through them to the depth's end within
`m·(18 N.k + 19)(L + 1)` steps; the accept flag ends up raised exactly when it was, or some word
of value at least `val s` outputs `[true]`, and the live flag exactly when it was, or some such
word is live after `L` steps. -/
private theorem xr_depth_host {N : FinNDTM Bool} (C : xr_Clock N) (z wL : List Bool) (L : ℕ)
    (hL : wL.length = L) (hval : xr_val wL = L) :
    ∀ (m : ℕ) (a l : Bool) (s u : List Bool) (h : Fin N.k → ℤ), s.length = L → u.length ≤ L →
      2 ^ L - xr_val s = m →
      ∃ T ≤ m * ((18 * N.k + 19) * (L + 1)), ∃ (a' l' : Bool) (u' : List Bool) (h' : Fin N.k → ℤ),
        (xr_host C).runFrom (xr_cycle C z a l wL s u h) T = xr_depthEnd C z a' l' L wL u' h' ∧
        u'.length ≤ L ∧
        (a' = true ↔ a = true ∨ ∃ s', s'.length = L ∧ xr_val s ≤ xr_val s' ∧
          (N.tm.runWith s' (N.tm.initCfg z)).output = [true]) ∧
        (l' = true ↔ l = true ∨ ∃ s', s'.length = L ∧ xr_val s ≤ xr_val s' ∧
          (N.tm.runWith s' (N.tm.initCfg z)).state ≠ none) := by
  intro m
  induction m with
  | zero =>
    intro a l s u h hs hu hm
    exfalso
    have := xr_val_lt s
    rw [hs] at this
    omega
  | succ m ih =>
    intro a l s u h hs hu hm
    obtain ⟨T₁, hT₁, u₁, hu₁, h₁, hsucc, hover⟩ := xr_cycle_host C z a l wL s u h
      (hval.trans hs.symm) (hL.trans hs.symm) (hu.trans hL.symm.le)
    rw [hs] at hT₁
    rcases hinc : incFixed s with _ | s'
    · -- `s` is the depth's last word
      have hmax : ∀ s', s'.length = L → xr_val s ≤ xr_val s' → s' = s := fun s' hs' hle =>
        xr_val_inj (hs'.trans hs.symm)
          (le_antisymm (xr_incFixed_none_max hinc (hs'.trans hs.symm)) hle)
      refine ⟨T₁, hT₁.trans (Nat.le_mul_of_pos_left _ (by omega)),
        a || decide ((N.tm.runWith s (N.tm.initCfg z)).output = [true]),
        l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome, u₁, h₁, ?_, hu₁.trans hL.le, ?_,
        ?_⟩
      · rw [hover hinc, hs]
      · rw [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro (h0 | h0)
          · exact Or.inl h0
          · exact Or.inr ⟨s, hs, le_rfl, h0⟩
        · rintro (h0 | ⟨s', hs', hle, hout⟩)
          · exact Or.inl h0
          · rw [hmax s' hs' hle] at hout
            exact Or.inr hout
      · rw [Bool.or_eq_true, Option.isSome_iff_ne_none]
        constructor
        · rintro (h0 | h0)
          · exact Or.inl h0
          · exact Or.inr ⟨s, hs, le_rfl, h0⟩
        · rintro (h0 | ⟨s', hs', hle, hlive⟩)
          · exact Or.inl h0
          · rw [hmax s' hs' hle] at hlive
            exact Or.inr hlive
    · -- `s'` follows `s`
      have hs' : s'.length = L := (incFixed_length hinc).trans hs
      have hv' : xr_val s' = xr_val s + 1 := xr_incFixed_val hinc
      have hlt := xr_val_lt s'
      rw [hs'] at hlt
      obtain ⟨T₂, hT₂, a', l', u', h', hrun₂, hu', ha', hl'⟩ := ih
        (a || decide ((N.tm.runWith s (N.tm.initCfg z)).output = [true]))
        (l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome) s' u₁ h₁ hs'
        (hu₁.trans hL.le) (by omega)
      have hmul : (m + 1) * ((18 * N.k + 19) * (L + 1)) =
          m * ((18 * N.k + 19) * (L + 1)) + (18 * N.k + 19) * (L + 1) := by ring
      refine ⟨T₁ + T₂, by omega, a', l', u', h', ?_, hu', ?_, ?_⟩
      · rw [MultiTapeTM.runFrom_add, hsucc s' hinc, hrun₂]
      · rw [ha', Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro ((h0 | h0) | ⟨s'', hs'', hle, hout⟩)
          · exact Or.inl h0
          · exact Or.inr ⟨s, hs, le_rfl, h0⟩
          · exact Or.inr ⟨s'', hs'', by omega, hout⟩
        · rintro (h0 | ⟨s'', hs'', hle, hout⟩)
          · exact Or.inl (Or.inl h0)
          · rcases Nat.lt_or_ge (xr_val s) (xr_val s'') with hlt' | hge
            · exact Or.inr ⟨s'', hs'', by omega, hout⟩
            · have hss : s'' = s := xr_val_inj (hs''.trans hs.symm) (le_antisymm hge hle)
              subst hss
              exact Or.inl (Or.inr hout)
      · rw [hl', Bool.or_eq_true, Option.isSome_iff_ne_none]
        constructor
        · rintro ((h0 | h0) | ⟨s'', hs'', hle, hlive⟩)
          · exact Or.inl h0
          · exact Or.inr ⟨s, hs, le_rfl, h0⟩
          · exact Or.inr ⟨s'', hs'', by omega, hlive⟩
        · rintro (h0 | ⟨s'', hs'', hle, hlive⟩)
          · exact Or.inl (Or.inl h0)
          · rcases Nat.lt_or_ge (xr_val s) (xr_val s'') with hlt' | hge
            · exact Or.inr ⟨s'', hs'', by omega, hlive⟩
            · have hss : s'' = s := xr_val_inj (hs''.trans hs.symm) (le_antisymm hge hle)
              subst hss
              exact Or.inl (Or.inr hlive)

/-- **The choice word's extension on the host**: within `2|s| + 3` steps a `false` is appended to
the choice word and the host dispatches to the depth word's extension. -/
private theorem xr_extC_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (s u wL : List Bool) (h : Fin N.k → ℤ) :
    ∃ T ≤ 2 * s.length + 3,
      (xr_host C).runFrom (⟨some ⟨(.extC, a, l), xr_St.run⟩, 1,
        xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u) (FinTM.bufferTape [])
          (FinTM.bufferTape wL), xr_heads h 0 0 0 0, []⟩ :
            Cfg (N.k + 2 + 2) Bool (Σ i, xr_PhSt C i) z) T =
      ⟨some ⟨(.extD, a, l), xr_St.run⟩, 1,
        xr_tapes (fun _ _ => none) (FinTM.bufferTape (s ++ [false])) (FinTM.bufferTape u)
          (FinTM.bufferTape []) (FinTM.bufferTape wL), xr_heads h 0 0 0 0, []⟩ := by
  have hrun := xr_extendTM_run (xr_choice N.k) s
    (⟨some xr_St.run, 1, xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u)
      (FinTM.bufferTape []) (FinTM.bufferTape wL), xr_heads h 0 0 0 0, []⟩ :
      Cfg (N.k + 2 + 2) Bool xr_St z) rfl (xr_tapes_choice _ _ _ _ _) (xr_heads_choice _ _ _ _ _)
  obtain ⟨T', hT', hrun', hguard⟩ := xr_firstArrival' (xr_extendTM (N.k + 2 + 2) (xr_choice N.k))
    (fun s => ∃ b, s = .done b) (xr_done_stationary _ (fun b inp w => rfl)) hrun rfl ⟨_, rfl⟩
  refine ⟨T' + 1, by omega, ?_⟩
  rw [xr_phase_step C (.extC, a, l) xr_St.run 1 _ _ T' _ hrun' _ rfl rfl
    ⟨(.extD, a, l), xr_St.run⟩ rfl
    (fun u hu s hs => xr_red_leaf_none C (.extC, a, l)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, l, rfl⟩))))) s (hguard u hu s hs) rfl)]
  dsimp only
  rw [xr_tapes_upd_choice, xr_heads_upd_choice]

/-- **The depth word's extension on the host**: within `2|wL| + 3` steps a `false` is appended to
the depth word and the host dispatches to its increment. -/
private theorem xr_extD_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (s u wL : List Bool) (h : Fin N.k → ℤ) :
    ∃ T ≤ 2 * wL.length + 3,
      (xr_host C).runFrom (⟨some ⟨(.extD, a, l), xr_St.run⟩, 1,
        xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u) (FinTM.bufferTape [])
          (FinTM.bufferTape wL), xr_heads h 0 0 0 0, []⟩ :
            Cfg (N.k + 2 + 2) Bool (Σ i, xr_PhSt C i) z) T =
      ⟨some ⟨(.incD, a, l), FlagPhase.run⟩, 1,
        xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u) (FinTM.bufferTape [])
          (FinTM.bufferTape (wL ++ [false])), xr_heads h 0 0 0 0, []⟩ := by
  have hrun := xr_extendTM_run (xr_dep N.k) wL
    (⟨some xr_St.run, 1, xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u)
      (FinTM.bufferTape []) (FinTM.bufferTape wL), xr_heads h 0 0 0 0, []⟩ :
      Cfg (N.k + 2 + 2) Bool xr_St z) rfl (xr_tapes_dep _ _ _ _ _) (xr_heads_dep _ _ _ _ _)
  obtain ⟨T', hT', hrun', hguard⟩ := xr_firstArrival' (xr_extendTM (N.k + 2 + 2) (xr_dep N.k))
    (fun s => ∃ b, s = .done b) (xr_done_stationary _ (fun b inp w => rfl)) hrun rfl ⟨_, rfl⟩
  refine ⟨T' + 1, by omega, ?_⟩
  rw [xr_phase_step C (.extD, a, l) xr_St.run 1 _ _ T' _ hrun' _ rfl rfl
    ⟨(.incD, a, l), FlagPhase.run⟩ rfl
    (fun u hu s hs => xr_red_leaf_none C (.extD, a, l)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, l, rfl⟩))))) s (hguard u hu s hs) rfl)]
  dsimp only
  rw [xr_tapes_upd_dep, xr_heads_upd_dep]

/-- **The depth word's increment on the host**: with `incFixed w = some w'`, within `2|w| + 3` steps
the depth tape holds `w'` and the host dispatches to the next depth's first cycle. -/
private theorem xr_incD_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (s u w w' : List Bool) (hw' : incFixed w = some w') (h : Fin N.k → ℤ) :
    ∃ T ≤ 2 * w.length + 3,
      (xr_host C).runFrom (⟨some ⟨(.incD, a, l), FlagPhase.run⟩, 1,
        xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u) (FinTM.bufferTape [])
          (FinTM.bufferTape w), xr_heads h 0 0 0 0, []⟩ :
            Cfg (N.k + 2 + 2) Bool (Σ i, xr_PhSt C i) z) T = xr_cycle C z a l w' s u h := by
  obtain ⟨hcfg, hguard, -⟩ := incrementTM_run_succ_ofCfg (xr_dep N.k) w w' hw'
    (⟨some FlagPhase.run, 1, xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u)
      (FinTM.bufferTape []) (FinTM.bufferTape w), xr_heads h 0 0 0 0, []⟩ :
      Cfg (N.k + 2 + 2) Bool FlagPhase z) rfl
    (by intro p _ _; dsimp only; rw [xr_tapes_dep, xr_heads_dep, zero_add])
  refine ⟨2 * (w.takeWhile id).length + 2 + 1, by
    have := (List.takeWhile_sublist (l := w) id).length_le; omega, ?_⟩
  rw [xr_phase_step C (.incD, a, l) FlagPhase.run 1 _ _ _ _ hcfg (FlagPhase.done true) rfl rfl
    ⟨(.copy, a, l), SweepPhase.sweep⟩ rfl
    (fun t ht s hs => by
      cases s with
      | done b => exact absurd hs (hguard t ht b)
      | run => rfl
      | rewind b => rfl)]
  dsimp only
  rw [xr_patch_eq _ _ (xr_dep N.k) (xr_heads_dep _ _ _ _ _) w w' w (incFixed_length hw')
    (xr_tapes_dep _ _ _ _ _) le_rfl, xr_tapes_upd_dep]
  rfl

/-- **The depth change on the host.** From a depth's end with the live flag up, within `6L + 11`
steps the host extends the choice word to the all-`false` word of length `L + 1`, extends and
increments the depth word to a word of width and value `L + 1`, lowers both flags, and starts
the next depth's first cycle. -/
private theorem xr_deepen_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a : Bool)
    (L : ℕ) (wL u : List Bool) (h : Fin N.k → ℤ) (hL : wL.length = L) (hval : xr_val wL = L) :
    ∃ T ≤ 6 * L + 11, ∃ wL' : List Bool, wL'.length = L + 1 ∧ xr_val wL' = L + 1 ∧
      (xr_host C).runFrom (xr_depthEnd C z a true L wL u h) T =
        xr_cycle C z false false wL' (List.replicate (L + 1) false) u h := by
  obtain ⟨T₁, hT₁, h1⟩ := xr_extC_host C z false false (List.replicate L false) u wL h
  obtain ⟨T₂, hT₂, h2⟩ := xr_extD_host C z false false (List.replicate L false ++ [false]) u wL h
  obtain ⟨wL', hwL'⟩ := xr_incFixed_append_false wL
  obtain ⟨T₃, hT₃, h3⟩ := xr_incD_host C z false false (List.replicate L false ++ [false]) u
    (wL ++ [false]) wL' hwL' h
  have hlen : (wL ++ [false]).length = L + 1 := by simp [hL]
  refine ⟨T₁ + T₂ + T₃, by rw [List.length_replicate] at hT₁; rw [hlen] at hT₃; omega, wL',
    (incFixed_length hwL').trans hlen, by rw [xr_incFixed_val hwL', xr_val_append_false, hval], ?_⟩
  rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add]
  show (xr_host C).runFrom ((xr_host C).runFrom ((xr_host C).runFrom ⟨some ⟨(.extC, false, false),
    xr_St.run⟩, 1, xr_tapes (fun _ _ => none) (FinTM.bufferTape (List.replicate L false))
      (FinTM.bufferTape u) (FinTM.bufferTape []) (FinTM.bufferTape wL), xr_heads h 0 0 0 0, []⟩ T₁)
      T₂) T₃ = _
  rw [h1, h2, h3, ← List.replicate_succ']

/-! #### The whole run, the machine `E`, the answer -/

/-- The halt phase's `start` is stationary on the host: the table redirects it to itself. -/
private theorem xr_halt_fixed {N : FinNDTM Bool} (C : xr_Clock N) {z : List Bool}
    (d : Cfg (N.k + 2 + 2) Bool (Σ i, xr_PhSt C i) z) (a l : Bool)
    (hd : d.state = some ⟨(.halt, a, l), xr_St.start⟩) : (xr_host C).step d = d := by
  have hhost := (phaseHostTM_run (xr_M C) ⟨(.copy, false, false), SweepPhase.sweep⟩ (xr_red C)
    (.halt, a, l) (⟨some xr_St.start, d.inputPos, d.workTapes, d.workTapePos, d.output⟩ :
      Cfg (N.k + 2 + 2) Bool (xr_PhSt C (.halt, a, l)) z) _ 0 MultiTapeTM.runFrom_zero
    xr_St.start rfl ⟨(.halt, a, l), xr_St.start⟩ rfl
    (fun u hu => absurd hu (Nat.not_lt_zero u))).2
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero] at hhost
  have hd' : (⟨some xr_St.start, d.inputPos, d.workTapes, d.workTapePos, d.output⟩ :
      Cfg (N.k + 2 + 2) Bool (xr_PhSt C (.halt, a, l)) z).mapState (Sigma.mk (.halt, a, l)) =
        d := by
    apply Cfg.ext
    · rw [Cfg.mapState_state, hd]; rfl
    · rw [Cfg.mapState_inputPos]
    · funext j p; rw [Cfg.mapState_workTapes]
    · funext j; rw [Cfg.mapState_workTapePos]
    · rw [Cfg.mapState_output]
  have hd'' : (⟨some xr_St.start, d.inputPos, d.workTapes, d.workTapePos, d.output⟩ :
      Cfg (N.k + 2 + 2) Bool (xr_PhSt C (.halt, a, l)) z).mapState
        (fun _ => (⟨(.halt, a, l), xr_St.start⟩ : Σ i, xr_PhSt C i)) = d := by
    apply Cfg.ext
    · rw [Cfg.mapState_state, hd]; rfl
    · rw [Cfg.mapState_inputPos]
    · funext j p; rw [Cfg.mapState_workTapes]
    · funext j; rw [Cfg.mapState_workTapePos]
    · rw [Cfg.mapState_output]
  rw [hd', hd''] at hhost
  exact hhost

open Classical in
/-- **The depths on the host.** With `L*` the first all-halting depth, from the first cycle at a
depth `L ≤ L*` (the depth word of width and value `L`, the choice word all `false`, the counter
word of width at most `L`, both flags down), within `Σ_{i ≤ L* - L} 2^{L+i}·(18 N.k + 38)(L+i+1)`
steps the host reaches the depth `L*`'s end, the live flag down and the accept flag
`decide (N.AcceptsWithin z L*)`: every depth below `L*` has a live branch and deepens, and the
depth `L*` answers. -/
private theorem xr_run_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (Ls : ℕ)
    (hLs : N.tm.HaltsWithin z Ls) (hmin : ∀ L' < Ls, ¬ N.tm.HaltsWithin z L') :
    ∀ (m L : ℕ) (wL u : List Bool) (h : Fin N.k → ℤ), L + m = Ls → wL.length = L →
      xr_val wL = L → u.length ≤ L →
      ∃ T ≤ ∑ i ∈ Finset.range (m + 1), 2 ^ (L + i) * ((18 * N.k + 38) * (L + i + 1)),
        ∃ (wL' u' : List Bool) (h' : Fin N.k → ℤ),
          (xr_host C).runFrom (xr_cycle C z false false wL (List.replicate L false) u h) T =
            xr_depthEnd C z (decide (N.AcceptsWithin z Ls)) false Ls wL' u' h' := by
  intro m
  induction m with
  | zero =>
    intro L wL u h hLm hL hval hu
    have hLm' : L = Ls := by omega
    rw [hLm'] at hL hval hu
    rw [hLm']
    obtain ⟨T₁, hT₁, a', l', u', h', hrun, -, ha', hl'⟩ := xr_depth_host C z wL Ls hL hval
      (2 ^ Ls) false false (List.replicate Ls false) u h (by simp) hu
      (by rw [xr_val_replicate_false, Nat.sub_zero])
    have hl'' : l' = false := by
      cases l' with
      | false => rfl
      | true =>
        exfalso
        rcases hl'.mp rfl with h0 | ⟨s', hs', -, hlive⟩
        · exact Bool.false_ne_true h0
        · exact hlive (NDTM.haltsWithin_iff.mp hLs s' hs')
    have ha'' : a' = decide (N.AcceptsWithin z Ls) := by
      rw [Bool.eq_iff_iff, decide_eq_true_iff, ha']
      constructor
      · rintro (h0 | ⟨s', hs', -, hout⟩)
        · exact absurd h0 Bool.false_ne_true
        · exact FinNDTM.acceptsWithin_iff.mpr ⟨s', hs', NDTM.haltsWithin_iff.mp hLs s' hs', hout⟩
      · intro hacc
        obtain ⟨w, hw, -, hout⟩ := FinNDTM.acceptsWithin_iff.mp hacc
        exact Or.inr ⟨w, hw, by rw [xr_val_replicate_false]; exact Nat.zero_le _, hout⟩
    subst hl'' ha''
    refine ⟨T₁, ?_, wL, u', h', hrun⟩
    simp only [Nat.zero_add, Nat.add_zero, Finset.sum_range_one]
    exact hT₁.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega)))
  | succ m ih =>
    intro L wL u h hLm hL hval hu
    have hnot := hmin L (by omega)
    rw [NDTM.haltsWithin_iff] at hnot
    push_neg at hnot
    obtain ⟨s₀, hs₀, hlive⟩ := hnot
    obtain ⟨T₁, hT₁, a', l', u', h', hrun₁, hu', -, hl'⟩ := xr_depth_host C z wL L hL hval
      (2 ^ L) false false (List.replicate L false) u h (by simp) hu
      (by rw [xr_val_replicate_false, Nat.sub_zero])
    have hl'' : l' = true :=
      hl'.mpr (Or.inr ⟨s₀, hs₀, by rw [xr_val_replicate_false]; exact Nat.zero_le _, hlive⟩)
    subst hl''
    obtain ⟨T₂, hT₂, wL', hwL'len, hwL'val, hrun₂⟩ := xr_deepen_host C z a' L wL u' h' hL hval
    obtain ⟨T₃, hT₃, wL'', u'', h'', hrun₃⟩ := ih (L + 1) wL' u' h' (by omega) hwL'len hwL'val
      (hu'.trans (Nat.le_succ L))
    refine ⟨T₁ + T₂ + T₃, ?_, wL'', u'', h'', ?_⟩
    · rw [Finset.sum_range_succ']
      have hshift : ∑ i ∈ Finset.range (m + 1),
          2 ^ (L + (i + 1)) * ((18 * N.k + 38) * (L + (i + 1) + 1)) =
          ∑ i ∈ Finset.range (m + 1), 2 ^ (L + 1 + i) * ((18 * N.k + 38) * (L + 1 + i + 1)) :=
        Finset.sum_congr rfl (fun i _ => by rw [show L + (i + 1) = L + 1 + i by omega])
      have hlast : 2 ^ (L + 0) * ((18 * N.k + 38) * (L + 0 + 1)) =
          2 ^ L * ((18 * N.k + 38) * (L + 1)) := rfl
      have h19 : 6 * L + 11 ≤ 2 ^ L * (19 * (L + 1)) := by
        have := Nat.le_mul_of_pos_left (19 * (L + 1)) (Nat.two_pow_pos L)
        omega
      have hsplit : 2 ^ L * ((18 * N.k + 38) * (L + 1)) =
          2 ^ L * ((18 * N.k + 19) * (L + 1)) + 2 ^ L * (19 * (L + 1)) := by ring
      omega
    · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hrun₁, hrun₂, hrun₃]

/-- The blank tape bank. -/
private theorem xr_tapes_blank (k : ℕ) :
    xr_tapes (k := k) (fun _ _ => none) (fun _ => none) (fun _ => none) (fun _ => none)
      (fun _ => none) = fun _ _ => none :=
  xr_bank_ext _ _ (fun j => xr_tapes_work _ _ _ _ _ j) (xr_tapes_choice _ _ _ _ _)
    (xr_tapes_ctr _ _ _ _ _) (xr_tapes_cap _ _ _ _ _) (xr_tapes_dep _ _ _ _ _)

/-- The heads at the origin. -/
private theorem xr_heads_zero (k : ℕ) : xr_heads (k := k) (fun _ => 0) 0 0 0 0 = fun _ => 0 :=
  xr_bank_ext _ _ (fun j => xr_heads_work _ _ _ _ _ j) (xr_heads_choice _ _ _ _ _)
    (xr_heads_ctr _ _ _ _ _) (xr_heads_cap _ _ _ _ _) (xr_heads_dep _ _ _ _ _)

/-- The host's halt anchor with the accept flag `b`. -/
private def xr_anchor {N : FinNDTM Bool} (C : xr_Clock N) (b : Bool) : Σ i, xr_PhSt C i :=
  ⟨(.halt, b, false), xr_St.start⟩

/-- The two-exit seam of the host onto the two one-step answers: at the anchor with the accept
flag up, the answer `[true]`; at the anchor with it down, the answer `[false]`. -/
private noncomputable def xr_seam {N : FinNDTM Bool} (C : xr_Clock N) :
    MultiTapeTM (N.k + 2 + 2) Bool (((Σ i, xr_PhSt C i) ⊕ xr_St) ⊕ xr_St) :=
  seamCompTM₂ (xr_host C) (xr_anchor C true) (xr_anchor C false)
    (xr_answerTM (N.k + 2 + 2) true) xr_St.start (xr_answerTM (N.k + 2 + 2) false) xr_St.start

/-- **The exhaustive replay's machine `E`**: the seam, started at the host's first cycle. -/
private noncomputable def xr_E {N : FinNDTM Bool} (C : xr_Clock N) : FinTM Bool :=
  ⟨N.k + 2 + 2, ((Σ i, xr_PhSt C i) ⊕ xr_St) ⊕ xr_St,
    { xr_seam C with q₀ := Sum.inl (Sum.inl ⟨(.copy, false, false), SweepPhase.sweep⟩) }⟩

/-- `E`'s initial configuration on `z` is the host's first cycle at depth `0`, in the seam's
states. -/
private theorem xr_E_initCfg {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) :
    (xr_E C).tm.initCfg z =
      ((xr_cycle C z false false [] [] [] (fun _ => 0)).mapState Sum.inl).mapState Sum.inl := by
  refine (MultiTapeTM.initCfg_with_q₀ (xr_seam C)
    (Sum.inl (Sum.inl ⟨(.copy, false, false), SweepPhase.sweep⟩)) z).trans ?_
  apply Cfg.ext
  · rw [Cfg.init_state, Cfg.mapState_state, Cfg.mapState_state]; rfl
  · rw [Cfg.init_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]; rfl
  · funext j p
    simp only [Cfg.init_workTapes, Cfg.mapState_workTapes]
    show none = xr_tapes (fun _ _ => none) (FinTM.bufferTape []) (FinTM.bufferTape [])
      (FinTM.bufferTape []) (FinTM.bufferTape []) j p
    rw [FinTM.bufferTape_nil, xr_tapes_blank]
  · funext j
    simp only [Cfg.init_workTapePos, Cfg.mapState_workTapePos]
    show (0 : ℤ) = xr_heads (fun _ => 0) 0 0 0 0 j
    rw [xr_heads_zero]
  · rw [Cfg.init_output, Cfg.mapState_output, Cfg.mapState_output]; rfl

/-- **The answer's tail.** From a live configuration with empty output, one step of the answer
row halts with the output `[b]`, read in any renaming of the states. -/
private theorem xr_answer_tail {K : ℕ} {x : List Bool} {S S' : Type} (b : Bool)
    (d : Cfg K Bool S x) (q : S) (hd : d.state = some q) (hout : d.output = [])
    (f : xr_St → S') :
    (((xr_answerTM K b).runFrom (d.mapState fun _ => xr_St.start) 1).mapState f).state = none ∧
    (((xr_answerTM K b).runFrom (d.mapState fun _ => xr_St.start) 1).mapState f).output = [b] := by
  rw [xr_answerTM_run b (d.mapState fun _ => xr_St.start) xr_St.start
    (by rw [Cfg.mapState_state, hd]; rfl)]
  refine ⟨?_, ?_⟩
  · rw [Cfg.mapState_state]; rfl
  · rw [Cfg.mapState_output]
    show (d.mapState fun _ => xr_St.start).output ++ [b] = [b]
    rw [Cfg.mapState_output, hout, List.nil_append]

/-- **The exhaustive replay `E`.** For every bundled binary NDTM `N` there is a deterministic
machine `E` and a constant `C` such that, on every input `z` on which every branch of `N` of
length `T` has halted (any `T`, which nobody needs to compute), `E` outputs `[true]` if `N`
accepts `z` within `T`, and `[false]` otherwise, in either case within `C·2^{C·(T + 1)}` steps.
There is no `|z|` term. [AB09, §3.2, proof of Theorem 3.2: the trivial exponential simulation
of a nondeterministic machine]

**Proof sketch.** Iterative deepening. For `L = 0, 1, …`: enumerate the `2^L` words of length
`L` on a counter tape (`Turing.incrementTM`); replay each through `N.tm.replayTM` for `L` steps
under the step-clocked runner (`Turing.exists_stepClockTMVia`, gated with the B6 hosts),
silently (`Turing.embedSilentTM`); record whether some branch accepted (halted with output
`[true]`) and whether some branch is still live; between replays clear the work tapes within
radius `L` (a counter-driven window clear) and rewind the native input head. Stop at the first
`L` at which every branch has halted; it is at most `T`, and acceptance within `L` and within
`T` agree there (`Turing.FinNDTM.AcceptsWithin.mono` one way; the other by truncating an
accepting word of length `T` at `L`, `Turing.NDTM.runWith_of_halt`). Answer accordingly. Each
replay touches at most `L + 1` input cells, so there is no `|z|` term. Ledger:
`Σ_{L ≤ T} 2^L·O_N(L + 1) ≤ C·2^{C·(T + 1)}`. -/
theorem FinNDTM.exists_exhaustiveDecider (N : FinNDTM Bool) :
    ∃ (E : FinTM Bool) (C : ℕ), ∀ (z : List Bool) (T : ℕ), N.tm.HaltsWithin z T →
      (N.AcceptsWithin z T → E.ComputesInTime z [true] (C * 2 ^ (C * (T + 1)))) ∧
      (¬N.AcceptsWithin z T → E.ComputesInTime z [false] (C * 2 ^ (C * (T + 1)))) := by
  classical
  obtain ⟨C⟩ := xr_Clock.exists N
  refine ⟨xr_E C, 18 * N.k + 41, fun z T hT => ?_⟩
  obtain ⟨Ls, -, hLsT, hLs, hmin, hiff⟩ := xr_first_depth N z T hT
  obtain ⟨T₀, hT₀, wL', u', h', hrun⟩ := xr_run_host C z Ls hLs hmin Ls 0 [] [] (fun _ => 0)
    (Nat.zero_add Ls) rfl xr_val_nil (Nat.zero_le 0)
  rw [List.replicate_zero] at hrun
  simp only [Nat.zero_add] at hT₀
  -- the time: the ledger over the depths `0, …, L*`, then the dispatch and the answer
  have hled := xr_ledger (18 * N.k + 38) Ls
  rw [show 18 * N.k + 38 + 3 = 18 * N.k + 41 by omega] at hled
  have hpow : (18 * N.k + 41) * 2 ^ ((18 * N.k + 41) * (Ls + 1)) ≤
      (18 * N.k + 41) * 2 ^ ((18 * N.k + 41) * (T + 1)) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (by omega)))
  -- `E`'s run, read through the seam
  have hE : ∀ t, (xr_E C).tm.runFrom ((xr_E C).tm.initCfg z) t =
      (seamCompTM₂ (xr_host C) (xr_anchor C true) (xr_anchor C false)
        (xr_answerTM (N.k + 2 + 2) true) xr_St.start (xr_answerTM (N.k + 2 + 2) false)
        xr_St.start).runFrom
        (((xr_cycle C z false false [] [] [] (fun _ => 0)).mapState Sum.inl).mapState Sum.inl)
        t :=
    fun t => (congrArg (fun c => (xr_E C).tm.runFrom c t) (xr_E_initCfg C z)).trans
      (MultiTapeTM.runFrom_with_q₀ (xr_seam C) _ _ t)
  have hstat : ∀ (d : Cfg (N.k + 2 + 2) Bool (Σ i, xr_PhSt C i) z) q, d.state = some q →
      (q = xr_anchor C true ∨ q = xr_anchor C false) → (xr_host C).step d = d := by
    rintro d q hd (rfl | rfl)
    · exact xr_halt_fixed C d true false hd
    · exact xr_halt_fixed C d false false hd
  have he : xr_anchor C true ≠ xr_anchor C false := fun h =>
    Bool.false_ne_true (congrArg (fun q : Σ i, xr_PhSt C i => q.1.2.1) h).symm
  -- the answer, for either value of the accept flag
  have key : ∀ b, decide (N.AcceptsWithin z Ls) = b →
      (xr_E C).ComputesInTime z [b] ((18 * N.k + 41) * 2 ^ ((18 * N.k + 41) * (T + 1))) := by
    intro b hb
    rw [hb] at hrun
    have hend : (xr_depthEnd C z b false Ls wL' u' h').state = some (xr_anchor C b) := rfl
    have hA : xr_anchor C b = xr_anchor C true ∨ xr_anchor C b = xr_anchor C false := by
      cases b
      exacts [Or.inr rfl, Or.inl rfl]
    obtain ⟨T₁, hT₁, hrun₁, hcut⟩ := xr_firstArrival' (xr_host C)
      (fun q => q = xr_anchor C true ∨ q = xr_anchor C false) hstat hrun hend hA
    have hcut' : ∀ t < T₁,
        ((xr_host C).runFrom (xr_cycle C z false false [] [] [] (fun _ => 0)) t).state ≠
          some (xr_anchor C true) ∧
        ((xr_host C).runFrom (xr_cycle C z false false [] [] [] (fun _ => 0)) t).state ≠
          some (xr_anchor C false) :=
      fun t ht => ⟨fun h => hcut t ht _ h (Or.inl rfl), fun h => hcut t ht _ h (Or.inr rfl)⟩
    have hseam := seamCompTM₂_run_ofCfg (xr_host C) (xr_anchor C true) (xr_anchor C false) he
      (xr_answerTM (N.k + 2 + 2) true) xr_St.start (xr_answerTM (N.k + 2 + 2) false) xr_St.start
      hrun₁ hcut'
    have hcomp : (xr_E C).ComputesInTime z [b] (T₁ + 1 + 1) := by
      rw [FinTM.computesInTime_iff, hE]
      cases b
      · rw [hseam.2 hend 1]
        exact xr_answer_tail false _ _ hend rfl Sum.inr
      · rw [hseam.1 hend 1]
        obtain ⟨h1, h2⟩ := xr_answer_tail true _ _ hend rfl
          (Sum.inr : xr_St → (Σ i, xr_PhSt C i) ⊕ xr_St)
        exact ⟨by rw [Cfg.mapState_state, h1]; rfl, by rw [Cfg.mapState_output, h2]⟩
    exact hcomp.mono (by omega)
  exact ⟨fun hacc => key true (decide_eq_true (hiff.mpr hacc)),
    fun hrej => key false (decide_eq_false fun h => hrej (hiff.mp h))⟩

/-- **The exponential decider from the universal NDTM**, `BF := E(UN)`: if `UN` is a timed
universal NDTM for the scheme `c` (the statement of `Turing.exists_timed_universal_NDTM`), then
there is a deterministic machine `BF` such that for every code `α` there is a constant `C` with
`BF` outputting `[true]` or `[false]` on `⟨⟨bits t, α⟩, x⟩`, according to whether the coded
machine accepts `x` within `t`, within `C·2^{C·(t + 1)}` steps (the statement of
`Turing.exists_ndAcceptsWithin_decider`). [AB09, §3.2, proof of Theorem 3.2, step 2]

**Proof sketch.** `BF` is the exhaustive replay of `UN`
(`Turing.FinNDTM.exists_exhaustiveDecider`) with constant `C_E`. Every branch of `UN` halts
within `C_α·(t + 1)`, so `E` decides `UN`'s acceptance within that bound, which is the coded
machine's acceptance within `t`, in time `C_E·2^{C_E·(C_α·(t + 1) + 1)}`; with
`C := C_E·(C_α + 1)` this is at most `C·2^{C·(t + 1)}`. -/
theorem ndAcceptsWithin_decider_of_universal (c : EffectiveNDMachineCode)
    (hUN : ∃ UN : FinNDTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      UN.tm.HaltsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ∧
      (UN.AcceptsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ↔
        (c.decode α).toFinNDTM.AcceptsWithin x t)) :
    ∃ BF : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      ((c.decode α).toFinNDTM.AcceptsWithin x t →
        BF.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [true]
          (C * 2 ^ (C * (t + 1)))) ∧
      (¬(c.decode α).toFinNDTM.AcceptsWithin x t →
        BF.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
          (C * 2 ^ (C * (t + 1)))) := by
  obtain ⟨UN, hU⟩ := hUN
  obtain ⟨E, CE, hE⟩ := FinNDTM.exists_exhaustiveDecider UN
  refine ⟨E, fun α => ?_⟩
  obtain ⟨C, hC⟩ := hU α
  refine ⟨CE * (C + 1), fun x t => ?_⟩
  obtain ⟨hhalt, hiff⟩ := hC x t
  obtain ⟨hacc, hrej⟩ := hE (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) hhalt
  have hexp : CE * (C * (t + 1) + 1) ≤ CE * (C + 1) * (t + 1) := by
    have : C * (t + 1) + 1 ≤ (C + 1) * (t + 1) := by rw [Nat.succ_mul]; omega
    calc CE * (C * (t + 1) + 1) ≤ CE * ((C + 1) * (t + 1)) := Nat.mul_le_mul_left CE this
      _ = CE * (C + 1) * (t + 1) := (Nat.mul_assoc _ _ _).symm
  have hbound : CE * 2 ^ (CE * (C * (t + 1) + 1)) ≤
      CE * (C + 1) * 2 ^ (CE * (C + 1) * (t + 1)) := by
    apply Nat.mul_le_mul
    · exact Nat.le_mul_of_pos_right CE (Nat.succ_pos C)
    · exact Nat.pow_le_pow_right (by omega) hexp
  exact ⟨fun h => (hacc (hiff.mpr h)).mono hbound,
    fun h => (hrej (fun h' => h (hiff.mp h'))).mono hbound⟩

end Turing


-- Diagonalization/NTimeHierarchy at the tip (inlined; its ExhaustiveReplay import is the block above)
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The nondeterministic time hierarchy theorem

[AB09, §3.2, Theorem 3.2] ([Coo72]): for time-constructible `f` and `g` with
`f(n+1) = o(g(n))`, `NTIME(f) ⊊ NTIME(g)` — by **lazy diagonalization**, since
a nondeterministic machine cannot flip its own answer directly. The tools are
the clocked universal NDTM of [AB09, Exercise 2.6] at **linear overhead**
(decision CH34-Q8: the strongest form possible, and exactly what puts the
theorem at book strength), the trivial exponential-time deterministic
evaluation of nondeterministic acceptance (the flip at each stage top), and
the linear-overhead coded normal form ([BGW70]-style guess-then-verify).
Phase P3.3 of `AroraBarakChapters3-4Plan.md`, over the code layer of
`TCSlib.Complexity.TuringMachine.NDCodes`.

**Status.** The universal NDTM `Turing.exists_timed_universal_NDTM` and the hierarchy
`Complexity.ntime_hierarchy` are sorried; the exponential decider and the two corollaries are
proved from them.

## Design (declared deviations, each for the audit)

* **The universal is iff-packaged with an unconditional clock.** [AB09]'s
  step 1 says "if `M_i` has not halted in this time, then halt and accept";
  the campaign's universal instead delivers, on every budget-shaped input,
  all-branch halting within `C·(t+1)` **and** acceptance iff the coded
  machine accepts within `t` — so a branch cut by the clock rejects. The
  honest reason this is sound (round-1 finding 7 — it is **not** that every
  coded branch finishes: the normal form guarantees no all-branch halting,
  and its guess phase has infinite non-accepting branches even for total
  deciders): accepting witnesses finish within the forward transfer bound,
  every completed accepting display is sound, and the backward direction
  uses the *original* decider's all-branch halting for truncation. Cut
  branches reject, which can never create a false positive.
* **Linear overhead `C·(t+1)` with `C` per code** (decision CH34-Q8): the
  clock is fused into the interpreter loop — one countdown tick per
  simulated step, with **amortized** linear total cost (a single decrement
  can borrow across the whole counter width; the borrows sum to
  `Σⱼ ν₂(j) ≤ t`, round-1 finding 5) — not a countdown that re-scans the
  counter word at every tick: that is where the received
  `Turing.timed_universal` pays its `C·(t+1)²` (each simulated step costs a
  further `O(|bits t| + 1)`), and the quadratic would surrender the
  book-strength hierarchy. (The received `Complexity.TimeHierarchy.clockTM`
  is a *linear* fused runner, `Complexity.TimeHierarchy.clockTM_spec`; it
  runs its body only from the body's initial configuration and emits a
  negated `[true]`-test, so it is not reused here.)
* **The domination hypothesis carries an extra `f n` addend**:
  `∀ A, A·(f(n+1) + f n + n + 1) ≤ g n` eventually. The `f(n+1)` term is the
  book's `f(n+1) = o(g(n))`; the `f n` term covers the inclusion half
  `NTIME f ⊆ NTIME (g+1)` without assuming `f` monotone (the book reads it
  off `f(n+1) = o(g)` implicitly); the `n + 1` term covers linear
  startup/virtual-input costs. For monotone `f` the extra addend is absorbed,
  so no strength is lost against [AB09].
* **The larger class is `NTIME (g + 1)`**, as in the received deterministic
  `Complexity.time_hierarchy`; the positive-bound form recovers `NTIME g`.
* **Guess first, then interpret (sketch routes; user decisions of
  2026-10-13).** No statement changes. The universal NDTM and the
  diagonalizer guess their whole choice word up front with the bounded
  choice writer and then run deterministically, so no nondeterministic
  counter loop is built (statement note SC-3 is closed by this route); the
  exponential decider is `E(UN)`, the exhaustive replay of the universal;
  nondeterministic codes are interpreted through their replay machine, with
  the deterministic step block unchanged; the universal reads its input
  through a bounded window copy. The host contracts live in
  `TCSlib.Complexity.TuringMachine.ChoiceReplay`,
  `TCSlib.Complexity.TuringMachine.Build.NDHost`,
  `TCSlib.Complexity.TuringMachine.Build.InputWindow`,
  `TCSlib.Complexity.TuringMachine.NDCodeSimulator` and
  `TCSlib.Complexity.ClassNP.ExhaustiveReplay`; the normal form is in
  `TCSlib.Complexity.ClassNP.NDNormalForm`.

## Main results

* `Turing.exists_timed_universal_NDTM` — [AB09, Exercise 2.6] at linear
  overhead (CH34-Q8).
* `Turing.exists_ndAcceptsWithin_decider` — the exponential deterministic
  evaluation ("this trivial exponential simulation … does suffice").
* `Turing.FinNDTM.exists_codeNDTM_accepts_linear` — the linear-overhead coded
  normal form ([BGW70]-style), stated in
  `TCSlib.Complexity.ClassNP.NDNormalForm` (moved there, user 2026-10-17).
* `Complexity.ntime_hierarchy`, `Complexity.ntime_hierarchy_of_pos` —
  [AB09, Theorem 3.2].
* `Complexity.NTIME_linear_ssubset_square` — the ℕ-rendered showcase
  instance (the book displays `NTIME(n) ⊊ NTIME(n^{1.5})`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.2, Theorem 3.2, Figure 3.1,
  Exercise 2.6.)
* [Coo72] S. Cook, *A hierarchy for nondeterministic time complexity*,
  STOC 1972. (Cited through [AB09]; no external text is required.)
* [BGW70] R. Book, S. Greibach, B. Wegbreit, *Time- and tape-bounded Turing
  acceptors and AFLs*, JCSS 4(6), 1970. (Cited through [AB09]; likewise.)
-/

namespace Turing

/-- **The clocked universal NDTM at linear overhead** ([AB09, Exercise 2.6];
decision CH34-Q8; spec, fill pending — phase P3.3): for every effective
nondeterministic scheme there is a universal NDTM `UN` such that for every
code `α` there is a constant `C` with, on input `⟨⟨bits t, α⟩, x⟩`: every
branch of `UN` halts within `C·(t+1)` steps, and `UN` accepts within
`C·(t+1)` iff the coded machine accepts `x` within `t`.

**Proof sketch.** Guess first, then interpret deterministically (user
decision 1 of 2026-10-13; a declared sketch deviation from the P3.3 route,
which passed choice bits through one per simulated step). `UN` parses the
header and expands `t` into a unary block on a stream tape
(`Turing.expandTM`). It then **guesses its whole choice word up front**: the
bounded choice writer (`Turing.ndWriterTM_run_block`) overwrites the block
with `t` choice bits in `t + 1` steps, the same time on every branch, and
the stream head is rewound (`Turing.skipBackTM`). Everything after the guess
is deterministic: the interpreter core `Turing.exists_ndInterpreterCore`,
run on the guessed stream `s`. Per code, the core installs the serialization
of the decoded machine's **replay machine** (`Turing.NDTM.replayTM`, the
coded NDTM as a deterministic three-work-tape machine that reads its choices
from the last tape; `Turing.exists_replayCanonizer`; user decision 3). It
copies the input window `x.take t` (`Turing.exists_inputWindowCopyTM`; the
whole `x` is never copied, so the budget need not dominate `|x|`, and input
locality, `Turing.NDTM.runWith_initCfg_take`, makes the window enough; user
decision 5). It then runs the deterministic clocked interpreter loop: one
round of the step block H2, at three work tapes, per simulated step, hosted
by Z1 on the window, with the countdown of the budget word `bits t`
**fused into the loop** and **amortized**, not pointwise (round-1 finding
5): a decrement from `j` borrows across `ν₂(j)` trailing zeros, unbounded
for a single tick, but the borrows of `t` ticks sum to at most `t`
(`Turing.counterOverhead_le_of_le`). It is not a countdown that re-scans
the counter word at every tick, which is where the received
`Turing.timed_universal` pays its `C·(t+1)²`, exactly what decision CH34-Q8
forbids. Per simulated step the remaining cost is one table round,
`O(|table|)`, a constant for fixed `α`, absorbed into `C`. The core accepts
iff the coded machine's branch along `s.take t` halts with output `[true]`.
The assembly is the nondeterministic phase host `Turing.NDTM.phaseHostND`
over a deterministic prefix, the writer and the deterministic core: the
transfer `Turing.NDTM.runWith_mapState_of_agreeOn_det` carries each
deterministic contract to every branch, and the replay lemma
`Turing.NDTM.replayTM_runFrom` identifies the core's simulated run with the
coded branch. So every branch of `UN` halts within `C·(t+1)`, and `UN`
accepts iff some guessed `s` is an accepting branch of length `t`
(`Turing.FinNDTM.AcceptsWithin.mono` absorbs the timing slack). No
nondeterministic counter loop is needed (statement note SC-3 dissolves): no
choice occurs inside a multi-step round. Linear overhead (CH34-Q8) is kept:
the expansion, the guess, the rewind and the window copy each cost
`O(t + 1)`. Fill obligations, named: the startup and per-code installation;
the choice writer's bounded contract; the window copy; the interpreter core
(H1's hosted clock over the step block at three work tapes, harvested with
H2's promotion); the guess-then-run assembly; the `C`-ledger per code. -/
theorem exists_timed_universal_NDTM (c : EffectiveNDMachineCode) :
    ∃ UN : FinNDTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      UN.tm.HaltsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ∧
      (UN.AcceptsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ↔
        (c.decode α).toFinNDTM.AcceptsWithin x t) := by
  sorry

/-- **Nondeterministic acceptance evaluates deterministically in exponential
time** ([AB09, §3.2: "this trivial exponential simulation … does suffice to
establish a hierarchy theorem"]; spec, fill pending — phase P3.3): a
deterministic machine decides, on input `⟨⟨bits t, α⟩, x⟩`, whether the coded
machine accepts `x` within `t`, in time `C · 2^{C·(t+1)}`. This is the flip
at each stage top of the lazy diagonalization — the only place the answer is
ever negated.

**Proof sketch.** `BF := E(UN)` (user decision 2 of 2026-10-13; a declared
sketch deviation from the P3.3 route, which replayed every choice word
through the universal's deterministic core with an inter-replay cleanup):
the exhaustive replay `Turing.FinNDTM.exists_exhaustiveDecider` of the fixed
universal NDTM `UN` of `Turing.exists_timed_universal_NDTM`. On
`⟨⟨bits t, α⟩, x⟩` every branch of `UN` halts within `C_α·(t+1)`, so `E`
decides `UN`'s acceptance within that bound, which is the coded machine's
acceptance within `t`, in time `C_E·2^{C_E·(C_α·(t+1)+1)} ≤ C·2^{C·(t+1)}`
with `C := C_E·(C_α+1)`. This derivation is proved, as
`Turing.ndAcceptsWithin_decider_of_universal`. Fill obligation, named: `E`
itself (iterative deepening over the choice words of the fixed `UN`, each
replayed by its replay machine under the step-clocked runner, with a window
clear between replays; no `|x|` term). The proof applies
`Turing.ndAcceptsWithin_decider_of_universal` to `Turing.exists_timed_universal_NDTM`. -/
theorem exists_ndAcceptsWithin_decider (c : EffectiveNDMachineCode) :
    ∃ BF : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      ((c.decode α).toFinNDTM.AcceptsWithin x t →
        BF.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [true]
          (C * 2 ^ (C * (t + 1)))) ∧
      (¬(c.decode α).toFinNDTM.AcceptsWithin x t →
        BF.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
          (C * 2 ^ (C * (t + 1)))) := by
  exact ndAcceptsWithin_decider_of_universal c (exists_timed_universal_NDTM c)

end Turing

namespace Complexity

open Turing

/-- **The nondeterministic time hierarchy theorem** ([AB09, Theorem 3.2];
[Coo72]; spec, fill pending — phase P3.3, **the phase summit**): for
time-constructible `f` and `g`, if every constant multiple of
`f(n+1) + f(n) + n + 1` is eventually below `g(n)` — the book's
`f(n+1) = o(g(n))` with the two declared addends (module docstring) — then
`NTIME f ⊊ NTIME (g + 1)`. Book strength: the overhead on `f` is **linear**
(decision CH34-Q8), in contrast to the received deterministic hierarchy's
square.

**Proof sketch.** *Inclusion:* the hypothesis at `A = 1` gives
`f n ≤ g n` eventually (the `f n` addend); finitely many lengths absorb into
the constant (the received `Complexity.time_hierarchy` `F`-sum idiom; no
monotonicity needed). *Strictness* is lazy diagonalization [AB09, proof of
Theorem 3.2 and Figure 3.1], over a scheme fixed by
`Turing.exists_effectiveNDMachineCode`, rebuilt per the round-1 audit (its
two majors: a per-code universal constant cannot be absorbed by choosing a
padded large index — padding preserves `decode`, no law preserves cost —
and the stage locator must be computable within the allowance). The
repaired construction: **(i) the fixed-code stage schedule**: stage
`i = pair(j, r)` runs the `j`-th binary string `α_j` (unranking), so every
code recurs at infinitely many stages — no padded-index selection, and the
alleged decider's constants stay fixed along its own stage subsequence (the
same discipline as the P3.2 enumeration's repetition coordinate).
**(ii) the `f`-adaptive ladder with capped comparisons**: with
`a := ℓ_i + 1` the stage bottom, `T*_i := (f a + a + 1)²` and
`ℓ_{i+1} := 2^{(T*_i)²}`, seeded at `ℓ₀ := 2` with the finitely many
lengths at or below the seed rejected (round-2 finding 1 fixed the seed
and this formula as *the* sequence — the round-2 pack's paraphrase
differed by an offset, a pack erratum acknowledged in the resolutions) —
an explicit recurrence over `f`'s constructibility witness; the locator
compares `n` against `ℓ_{i+1}` by **bit-length arithmetic with capped
witness runs** (the ladder value is
never materialized in unary, and a capped run that fails to finish itself
decides the comparison: an unfinished `f`-witness already certifies
`ℓ_{i+1} > n`), with the completed stages' costs summing geometrically and
the one incomplete evaluation capped — total `O(g n + 1)` after computing
`g n` once by `g`'s witness. **(iii) the self-clocked mid-rung, guess first** (user decision 1 of
2026-10-13; a declared sketch deviation from passing choice bits through):
right after computing `g n`, `D` **guesses a stream of `g n` choice bits**
with the bounded choice writer (`Turing.ndWriterTM_run_block`), its only
nondeterministic phase; every later phase is deterministic. For
`ℓ_i < n < ℓ_{i+1}`, `D` materializes `⟨⟨bits (g n), α_j⟩, 1^{n+1}⟩` and
runs the deterministic interpreter core `Turing.exists_ndInterpreterCore`
on it, hosted by Z1, with the guessed stream, at nominal simulated budget
`g n`, under `D`'s **own step-clocked countdown of `K·(g n + 1)` steps**
(the step clock `Turing.exists_stepClockTMVia`, shared with the B6 hosts)
— `K` fixed by `D`'s architecture, independent of the code, **with the
allowance split stated** (round-2 finding 2): a fixed share is reserved
ahead of simulation for the one `g`-witness run (bounded by its own
`c_g·(g n + 1)` clause — it runs *before* the countdown exists and is not
cut by it), for the guess, for budget and countdown preparation, and for
the worst single binary borrow; the **prefix-bound obligation is a clause
of the core's contract**: when the simulated branch halts at `t' ≤ g n`,
the core stops within `C_α·(t' + |x| + |bits (g n)| + 1)` (here
`|x| = n + 1`, the bounded window copy of user decision 5), so the
remaining share covers the relevant branches; `D` accepts iff the core
accepts within the countdown, and branches cut by the countdown **reject**
(sound: a cut branch is non-accepting, and completed accepting simulations
are sound).
**(iv) the top rung**: at `n = ℓ_{i+1}`, `D` runs `BF` on
`⟨bits T*_i, α_j, 1^{a}⟩` under the same self-cap and **flips** a completed
verdict (default answer if the cap trips); non-unary inputs reject.
`D ∈ NTIME (g + 1)` **by construction**: every phase is either bounded
within its reserved share of the `K·(g n + 1)` allowance or run under the
step-clock cap, uniformly in the code. *The chain, for the alleged
decider:* given `N` deciding `L(D)` within `c₀ · f`, take `M'` and `C₁`
from `Turing.FinNDTM.exists_codeNDTM_accepts_linear N` and let `α` be
`M'`'s code with its **fixed** interpreter constant `C_α`. Mid-rung, at the
late stages of `α`'s subsequence: by the core's prefix clause the genuine
simulation of an accepting `N`-branch costs at most
`C_α·(C₁·(c₀·f(n+1) + 1) + (n + 1) + |bits (g n)| + 1)`, which is at most
`A*·(f(n+1) + n + 1) + C_α·|bits (g n)|` host steps with
`A* := C_α·(C₁·c₀ + C₁ + 2) + 1` **fixed**, and the domination hypothesis
(its `f(n+1)` and `n + 1` addends; the logarithmic term is `o(g n)`) puts
that below `K·(g n + 1)` eventually — so the countdown never cuts the
relevant branches, and
`D(1^n) = [M'` accepts `1^{n+1}` within the window`] = [1^{n+1} ∈ L(D)]`
(forward by the linear transfer and `AcceptsWithin.mono`; backward by the
unbounded transfer plus truncation at `N`'s own all-branch budget,
`Turing.NDTM.runWith_of_halt`) — the chain (3.3). Top rung: the flip needs
the transfer at the **bottom** length `a`:
`T*_i = (f a + a + 1)² ≥ C₁·(c₀·f a + 1)` eventually — the square against
fixed constants, no `g a` comparison needed; the hypothesis's `f n` addend
serves the inclusion half (round-2 note 3) — and `BF`'s cost
`C_BF·2^{C_BF·(T*_i + 1)} ≤ K·(g n + 1)` eventually along the subsequence
since `g n ≥ n = 2^{(T*_i)²}` — the ladder's square in the exponent
outruns any fixed linear exponent — which is the chain's (3.4); `N`
agreeing with `D` on the whole stage collapses (3.3) into (3.4)'s flip,
the contradiction of [AB09, Figure 3.1]. Fill obligations, named: the
schedule and unranking; the ladder recurrence and the capped-comparison
locator with its amortized ledger; the guess and the step-clocked
interpreter core at fixed `K`; the two transfer instantiations (at `f(n+1)` mid-rung, at `f a`
bottom); the chain induction. -/
theorem ntime_hierarchy {f g : ℕ → ℕ} (hf : TimeConstructible f)
    (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) :
    NTIME f ⊂ NTIME (fun n => g n + 1) := by
  sorry

/-- **The nondeterministic time hierarchy for a positive bound**
([AB09, Theorem 3.2]; spec, fill pending): as `Complexity.ntime_hierarchy`,
with the larger class exactly `NTIME g` when `g` never vanishes — mirroring
`Complexity.time_hierarchy_of_pos`.

**Proof sketch.** `c·(g n + 1) ≤ 2c · g n` when `g n ≥ 1`, so
`NTIME (g + 1) ⊆ NTIME g`; the reverse is `Complexity.NTIME.mono`; conclude
from `Complexity.ntime_hierarchy`.

Formally, the factor `2` is absorbed into the membership witness's constant
(`Complexity.mem_NTIME_iff`, `Turing.FinNDTM.decidesInTime_iff`). -/
theorem ntime_hierarchy_of_pos {f g : ℕ → ℕ} (hf : TimeConstructible f)
    (hg : TimeConstructible g) (hpos : ∀ n, 0 < g n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f (n + 1) + f n + n + 1) ≤ g n) :
    NTIME f ⊂ NTIME g := by
  have hback : NTIME (fun n => g n + 1) ⊆ NTIME g := by
    intro L hL
    have hscale : L ∈ NTIME (fun n => 2 * g n) :=
      NTIME.mono (fun n => by have := hpos n; omega) hL
    obtain ⟨a, N, hN⟩ := mem_NTIME_iff.mp hscale
    apply mem_NTIME_iff.mpr
    refine ⟨a * 2, N, FinNDTM.decidesInTime_iff.mpr ?_⟩
    intro x
    simpa only [Nat.mul_assoc] using (FinNDTM.decidesInTime_iff.mp hN x)
  have heq : NTIME (fun n => g n + 1) = NTIME g :=
    Set.Subset.antisymm hback (NTIME.mono (fun n => Nat.le_succ (g n)))
  simpa only [heq] using ntime_hierarchy hf hg hfg

/-- **The showcase separation** (spec, fill pending — phase P3.3):
`NTIME(n + 1) ⊊ NTIME((n + 1)²)`, the ℕ-rendering of the book's displayed
instance `NTIME(n) ⊊ NTIME(n^{1.5})` (fractional exponents have no ℕ-valued
normal form in the campaign; the square is the nearest constructible bound).
This is exactly what decision CH34-Q8 buys: under the received
**deterministic** hierarchy's quadratic overhead, `A·(2n + 2)² ≤ (n + 1)²`
fails for every **positive** `A` (round-1 finding 9; `A = 0` holds
vacuously), so no square-overhead route separates these two classes
— the linear-overhead universal is load-bearing.

**Proof sketch.** `Complexity.ntime_hierarchy_of_pos` at `f := n + 1`,
`g := (n + 1)²`: positivity is immediate; domination is
`A·((n + 2) + (n + 1) + n + 1) = A·(3n + 4) ≤ (n + 1)²` for `n ≥ 3A + 4`.
The two constructibility witnesses are `Complexity.timeConstructible_poly` at
`(C, c) = (1, 0)` and `(1, 1)`; domination takes `N = 3A + 4` and multiplies `N ≤ n` by `n`. -/
theorem NTIME_linear_ssubset_square :
    NTIME (fun n => n + 1) ⊂ NTIME (fun n => (n + 1) ^ 2) := by
  have hf : TimeConstructible (fun n => n + 1) := by
    have h : (fun n : ℕ => 1 * (n + 1) ^ (0 + 1)) = (fun n => n + 1) := by
      funext n
      simp only [Nat.zero_add, pow_one, one_mul]
    rw [← h]
    exact timeConstructible_poly 1 0 (by decide)
  have hg : TimeConstructible (fun n => (n + 1) ^ 2) := by
    have h : (fun n : ℕ => 1 * (n + 1) ^ (1 + 1)) = (fun n => (n + 1) ^ 2) := by
      funext n
      simp only [one_mul]
    rw [← h]
    exact timeConstructible_poly 1 1 (by decide)
  apply ntime_hierarchy_of_pos hf hg
  · intro n
    exact pow_pos (Nat.succ_pos n) _
  · intro A
    refine ⟨3 * A + 4, fun n hn => ?_⟩
    nlinarith [Nat.mul_le_mul_right n hn]

end Complexity


#print axioms Turing.FinNDTM.exists_exhaustiveDecider
#print axioms Turing.ndAcceptsWithin_decider_of_universal
#print axioms Turing.exists_ndAcceptsWithin_decider
#print axioms Turing.exists_timed_universal_NDTM


open Lean Elab Command in
/-- Every constant in the dependency closure of `root` whose own type or value mentions
`sorryAx` (maintainer's read-only admission walk). -/
def c1unSorrySourcesOf (env : Environment) (root : Name) : Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[root]
  let mut srcs : Array Name := #[]
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if visited.contains c then continue
    visited := visited.insert c
    if let some ci := env.find? c then
      let used := ci.getUsedConstantsAsSet
      if used.contains ``sorryAx then srcs := srcs.push c
      for d in used.toList do
        unless visited.contains d do stack := stack.push d
  return srcs

open Lean Elab Command in
elab "#sorry_sources " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  logInfo m!"{n}: direct sorryAx users in closure: {c1unSorrySourcesOf (← getEnv) n}"


#sorry_sources Turing.exists_ndAcceptsWithin_decider
#sorry_sources Complexity.ntime_hierarchy
