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
