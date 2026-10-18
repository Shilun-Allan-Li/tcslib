/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.TuringMachine.ChoiceReplay
import TCSlib.Complexity.TuringMachine.Build.StepClock
import TCSlib.Complexity.TuringMachine.Build.Seam

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

/-- The ledger's shape: `Σ_{L ≤ T} 2^L · A(L + 1) ≤ (A + 3)·2^{(A + 3)(T + 1)}`. -/
private theorem xr_ledger (A T : ℕ) :
    ∑ L ∈ Finset.range (T + 1), 2 ^ L * (A * (L + 1)) ≤ (A + 3) * 2 ^ ((A + 3) * (T + 1)) := by
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
  calc ∑ L ∈ Finset.range (T + 1), 2 ^ L * (A * (L + 1))
      ≤ (T + 1) * (2 ^ T * (A * (T + 1))) := hsum
    _ = A * ((T + 1) * 2 ^ T * (T + 1)) := by ring
    _ ≤ A * (2 ^ (T + 1) * 2 ^ (T + 1) * 2 ^ (T + 1)) :=
        Nat.mul_le_mul_left A (Nat.mul_le_mul (Nat.mul_le_mul hlin h2) hlin)
    _ ≤ (A + 3) * 2 ^ ((A + 3) * (T + 1)) := Nat.mul_le_mul (by omega) hpow

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

/-- The blanking write: `some none` blanks the cell, `none` leaves it. -/
private def xr_wr (blank : Bool) : Option (Option Bool) := if blank then some none else none

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
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero,
      MultiTapeTM.step_of_some hd, hnone b _ _ hread, xr_mv1_apply_none]
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
        ⟨some .run, d.inputPos, d.workTapes, Function.update d.workTapePos r (o + m), d.output⟩ := by
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
  have h1step : ∀ c : Cfg K Bool xr_St x, (xr_testTM K r).runFrom c 1 = (xr_testTM K r).step c :=
    fun c => MultiTapeTM.runFrom_succ_eq_step'.trans (by rw [MultiTapeTM.runFrom_zero])
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
    rw [show ([] : List Bool).length + 2 = 1 + 1 from rfl, MultiTapeTM.runFrom_succ_eq_step, h1step,
      hstart, MultiTapeTM.step_of_some rfl,
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
      rw [hlen, show L.length + 1 + 2 = L.length + 1 + 1 + 1 from rfl,
        MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_succ_eq_step, hstart, hstep2,
        xr_test_tail r L _ rfl (by dsimp only; rw [Function.update_self])
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
        rw [show (([] : List Bool) ++ [true]).length + 2 = 1 + 1 + 1 from rfl,
          MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_succ_eq_step, h1step,
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
        rw [show (L' ++ [b'] ++ [true]).length + 2 = L'.length + 1 + 1 + 1 + 1 by
            simp only [List.length_append, List.length_singleton]; try omega,
          MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_succ_eq_step,
          MultiTapeTM.runFrom_succ_eq_step, hstart, hstep2, hstep3,
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

/-- **The input rewind's contract** (`Turing.FinTM.timed_rewind`, with the first arrival at the
anchor): within `inputPos + 2` steps the input head is at `1`, nothing else changes, the state is
`done true`, and no earlier state is. -/
private theorem xr_inRewindTM_run {K : ℕ} {x : List Bool} (d : Cfg K Bool xr_St x)
    (hd : d.state = some .start) :
    ∃ T ≤ d.inputPos.val + 2,
      (xr_inRewindTM K).runFrom d T = {d with state := some (.done true), inputPos := 1} ∧
      ∀ u < T, ((xr_inRewindTM K).runFrom d u).state ≠ some (.done true) := by
  obtain ⟨T, hT, hrun⟩ := FinTM.timed_rewind (xr_inRewindTM K) .start .run (some (.done true))
    (fun inp work => rfl) (fun inp work => by cases inp <;> rfl) d hd
  obtain ⟨T', hT', hrun', hguard⟩ := xr_firstArrival (xr_inRewindTM K) (.done true)
    (fun e he => xr_stay_step _ _ (fun inp w => rfl) e he) hrun rfl
  exact ⟨T', hT'.trans hT, hrun', hguard⟩

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
  refine ⟨Nat.find hex, Nat.find_min' hex hT', ?_, fun u hu a' ha' hA => Nat.find_min hex hu ⟨a', ha', hA⟩⟩
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
private theorem xr_work_injective {k : ℕ} {j j' : Fin k} (h : xr_work k j = xr_work k j') : j = j' := by
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
    Function.update (xr_heads hk hch hctr hcp hdp) (xr_choice k) X = xr_heads hk X hctr hcp hdp := by
  apply xr_bank_ext
  · intro j; rw [Function.update_of_ne (xr_work_ne_choice j), xr_heads_work, xr_heads_work]
  · rw [Function.update_self, xr_heads_choice]
  · rw [Function.update_of_ne (Ne.symm (xr_choice_ne_ctr k)), xr_heads_ctr, xr_heads_ctr]
  · rw [Function.update_of_ne (Ne.symm (xr_choice_ne_cap k)), xr_heads_cap, xr_heads_cap]
  · rw [Function.update_of_ne (Ne.symm (xr_choice_ne_dep k)), xr_heads_dep, xr_heads_dep]

private theorem xr_heads_upd_ctr {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) (X : ℤ) :
    Function.update (xr_heads hk hch hctr hcp hdp) (xr_ctr k) X = xr_heads hk hch X hcp hdp := by
  apply xr_bank_ext
  · intro j; rw [Function.update_of_ne (xr_work_ne_ctr j), xr_heads_work, xr_heads_work]
  · rw [Function.update_of_ne (xr_choice_ne_ctr k), xr_heads_choice, xr_heads_choice]
  · rw [Function.update_self, xr_heads_ctr]
  · rw [Function.update_of_ne (Ne.symm (xr_ctr_ne_cap k)), xr_heads_cap, xr_heads_cap]
  · rw [Function.update_of_ne (Ne.symm (xr_ctr_ne_dep k)), xr_heads_dep, xr_heads_dep]

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
    (hi : hd i = 0) (w v : List Bool) (hv : v.length = w.length) (hw : tp i = FinTM.bufferTape w) :
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

private theorem xr_val_cons (b : Bool) (w : List Bool) : xr_val (b :: w) = b.toNat + 2 * xr_val w := by
  simp [xr_val, Nat.ofDigits_cons]

private theorem xr_val_lt (w : List Bool) : xr_val w < 2 ^ w.length := by
  have := Nat.ofDigits_lt_base_pow_length (b := 2) (l := w.map Bool.toNat) (by norm_num)
    (by intro x hx; obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx; cases b <;> simp)
  simpa [xr_val] using this

private theorem xr_val_inj : ∀ {w w' : List Bool}, w.length = w'.length → xr_val w = xr_val w' → w = w'
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
  /-- emit the answer and halt -/
  | answer (b : Bool)
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
  | (.answer _, _, _) => xr_St

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
  | (.answer _, _, _) => inferInstanceAs (Fintype xr_St)

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
  | (.answer _, _, _) => inferInstanceAs (DecidableEq xr_St)

/-- The direction of pass `n`: the first two passes move left, the last four right. -/
private def xr_dir (n : Fin 6) : SignType := if n.val < 2 then SignType.neg else SignType.pos

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
  | (.answer b, _, _) => xr_answerTM (N.k + 2 + 2) b

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
      some (if l then ⟨(.extC, false, false), xr_St.run⟩ else ⟨(.answer a, a, l), xr_St.start⟩)
    | _ => none
  | (.extC, a, l), s => match s with | .done b => xr_redDone C (.extC, a, l) b | _ => none
  | (.extD, a, l), s => match s with | .done b => xr_redDone C (.extD, a, l) b | _ => none
  | (.incD, a, l), s => match s with | .done _ => some ⟨(.copy, a, l), SweepPhase.sweep⟩ | _ => none
  | (.answer _, _, _), _ => none

/-- **The exhaustive replay `E`**, as a bundled machine: the phase host over the phases above,
starting at the copy with both flags down. -/
private noncomputable def xr_E {N : FinNDTM Bool} (C : xr_Clock N) : FinTM Bool :=
  ⟨N.k + 2 + 2, Σ i, xr_PhSt C i,
    phaseHostTM (xr_M C) ⟨(.copy, false, false), SweepPhase.sweep⟩ (xr_red C)⟩

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
    (xr_E C).tm.runFrom ⟨some ⟨i, s₀⟩, ip, tp, hd, []⟩ (T + 1) =
      ⟨some q', c'.inputPos, c'.workTapes, c'.workTapePos, []⟩ := by
  have hstart : (⟨some ⟨i, s₀⟩, ip, tp, hd, []⟩ : Cfg (N.k + 2 + 2) Bool (Σ i, xr_PhSt C i) z) =
      (⟨some s₀, ip, tp, hd, []⟩ : Cfg (N.k + 2 + 2) Bool (xr_PhSt C i) z).mapState (Sigma.mk i) := by
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
  sorry

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
