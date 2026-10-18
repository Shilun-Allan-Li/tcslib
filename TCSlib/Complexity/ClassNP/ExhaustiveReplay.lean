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
