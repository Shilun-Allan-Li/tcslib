/-
Copyright (c) 2026 Hydroxyi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.DeriveFintype
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Code-prefix duplication

Glue for the diagonal machine of the time hierarchy theorem
[AB09, Theorem 3.1, proof].

* **Code-prefix duplication.** The universal machine of this development
  (`Turing.universal`) reads its input as `pairEncode α x` — code first. The diagonal
  machine must run the machine coded in its input *on that same input*. On an input
  of the shape `x = pairEncode α w` this is `pairEncode α x`, which is the aligned
  doubled-bit prefix of `x` (up to and including the separator) followed by all of
  `x`. The machine `preTM` computes `x ↦ scanPre x ++ x` in linear time, where
  `scanPre` is that prefix (`scanPre_pairEncode`).
* **Timed partial composition** is `Turing.FinTM.bufferedCompTM_computesInTime`
  (`TCSlib.Complexity.TuringMachine.Composition`).

## Design

* Fixing the code `α` and padding the *input* (rather than taking ever longer codes of
  the same machine, as [AB09] does via "every machine has infinitely many codes") is
  forced here: the universal machine's constant depends on the code string itself,
  with no uniform bound in its length (see `Turing.universal`), so the diagonal
  argument must simulate one fixed code on longer and longer inputs.

## Main definitions

* `Complexity.TimeHierarchy.scanPre` — the aligned doubled-bit prefix of a word.
* `Complexity.TimeHierarchy.preTM` — the prefix-duplication machine.

## Main results

* `Complexity.TimeHierarchy.preTM_computes` — `preTM` computes `x ↦ scanPre x ++ x`
  within `3|x| + 5` steps.
* `Complexity.TimeHierarchy.scanPre_pairEncode_append` — on `pairEncode α w` the
  computed word is `pairEncode α (pairEncode α w)`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4, §3.1.)
-/

namespace Complexity.TimeHierarchy

open Turing Turing.FinTM

/-- The aligned doubled-bit prefix of a word: read aligned pairs, keep them while
they are `00` or `11`, and stop after (and including) the first other pair; a final
unpaired bit is kept. On `pairEncode α w` this is the doubled `α` and the separator. -/
def scanPre : List Bool → List Bool
  | [] => []
  | [b] => [b]
  | b :: b' :: r => b :: b' :: (if b = b' then scanPre r else [])

/-- On a code-first pair, the scanned prefix is the doubled code and the separator. -/
lemma scanPre_pairEncode (α w : List Bool) :
    scanPre (pairEncode α w) = (α.flatMap fun b => [b, b]) ++ [false, true] := by
  induction α with
  | nil => simp [pairEncode, scanPre]
  | cons b α ih =>
    simp only [pairEncode, List.flatMap_cons, List.cons_append, List.nil_append,
      List.append_assoc] at ih ⊢
    simp only [scanPre, if_true]
    rw [ih]

/-- **Prefix duplication on code-first pairs:** `scanPre x ++ x = pairEncode α x` for
`x = pairEncode α w`. -/
lemma scanPre_pairEncode_append (α w : List Bool) :
    scanPre (pairEncode α w) ++ pairEncode α w = pairEncode α (pairEncode α w) := by
  rw [scanPre_pairEncode]
  simp [pairEncode]

/-- Control states of the prefix-duplication machine. -/
inductive PreState where
  | scan0 : PreState
  | scan1 : Bool → PreState
  | rwStart : PreState
  | rwScan : PreState
  | copy : PreState
  deriving DecidableEq, Fintype

/-- Transition table of the prefix-duplication machine (no work tapes): scan and emit
aligned pairs while they are doubled bits, rewind the input head, then copy the
whole input to the output. -/
def preTr (q : PreState) (inp : Option Bool) (_work : Fin 0 → Option Bool) :
    Action 0 Bool PreState :=
  match q, inp with
  | .scan0, some b => ⟨.pos, fun _ => (none, 0), some b, some (.scan1 b)⟩
  | .scan0, none => controlAction 0 (some .rwStart)
  | .scan1 b, some b' =>
    ⟨.pos, fun _ => (none, 0), some b', some (if b = b' then .scan0 else .rwStart)⟩
  | .scan1 _, none => controlAction 0 (some .rwStart)
  | .rwStart, _ => controlAction .neg (some .rwScan)
  | .rwScan, some _ => controlAction .neg (some .rwScan)
  | .rwScan, none => controlAction .pos (some .copy)
  | .copy, some b => ⟨.pos, fun _ => (none, 0), some b, some .copy⟩
  | .copy, none => ⟨0, fun _ => (none, 0), none, none⟩

/-- **The prefix-duplication machine**: on input `x` it outputs `scanPre x ++ x`. -/
def preTM : FinTM Bool where
  k := 0
  State := PreState
  tm := { q₀ := .scan0, tr := preTr }

/-- One live step applies the table. -/
private lemma preTM_step {x : List Bool} (c : Cfg 0 Bool PreState x) (q : PreState)
    (h : c.state = some q) :
    preTM.tm.step c = (preTr q c.inputSymbol c.workTapeSymbols).apply c := by
  unfold MultiTapeTM.step
  rw [h]
  rfl

/-- The scanning phase: from input position `i + 1` with `drop i x = rest`, the
machine reaches the rewind state within `|rest| + 1` steps, having appended
`scanPre rest`.

**Proof sketch.** Strong recursion on `rest`, two symbols at a time. If `rest` is
empty, the head reads a blank and one step enters the rewind state, emitting nothing
new. If `rest = [b]`, two steps read `b`, then a blank, and enter the rewind state
having emitted what `scanPre [b]` prescribes. If `rest = b :: b' :: r`, two steps read
the pair and emit `b, b'`; when `b = b'` the machine is back in the scanning state two
cells further on, and the recursive call on `r` gives the rest of the run (with step
count `2 + t ≤ |rest| + 1`); when `b ≠ b'` the pair is the terminator of the prefix and
the machine is already in the rewind state after two steps. -/
private theorem pre_scan (x : List Bool) : ∀ (rest : List Bool) (i : ℕ)
    (c : Cfg 0 Bool PreState x), x.drop i = rest → i ≤ x.length →
    c.state = some .scan0 → c.inputPos.val = i + 1 →
    ∃ t ≤ rest.length + 1, (preTM.tm.runFrom c t).state = some .rwStart ∧
      (preTM.tm.runFrom c t).output = c.output ++ scanPre rest
  | [], i, c, hd, hi, hs, hp => by
    have hin : c.inputSymbol = none := by
      rw [inputSymbol_at c i hi hp, ← List.head?_drop, hd]; rfl
    refine ⟨1, le_refl _, ?_, ?_⟩
    · change (preTM.tm.step c).state = _
      rw [preTM_step c _ hs, hin]; rfl
    · change (preTM.tm.step c).output = _
      rw [preTM_step c _ hs, hin]; simp [preTr, controlAction, scanPre]
  | [b], i, c, hd, hi, hs, hp => by
    have hlt : i < x.length := by
      have := congrArg List.length hd; simp at this; omega
    have hin : c.inputSymbol = some b := by
      rw [inputSymbol_at c i hi hp, ← List.head?_drop, hd]; rfl
    let c1 := preTM.tm.step c
    have hc1 : c1 = (preTr .scan0 (some b) c.workTapeSymbols).apply c := by
      simp only [c1]; rw [preTM_step c _ hs, hin]
    have hp1 : c1.inputPos.val = (i + 1) + 1 := by
      rw [hc1]; simp only [preTr, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]; simp [hp]
    have hin1 : c1.inputSymbol = none := by
      rw [inputSymbol_at c1 (i + 1) (by omega) hp1, ← List.head?_drop]
      have : x.drop (i + 1) = [] := by rw [← List.drop_drop, hd]; rfl
      rw [this]; rfl
    have hs1 : c1.state = some (.scan1 b) := by rw [hc1]; rfl
    refine ⟨2, le_refl _, ?_, ?_⟩
    · change (preTM.tm.step c1).state = _
      rw [preTM_step c1 _ hs1, hin1]; rfl
    · change (preTM.tm.step c1).output = _
      rw [preTM_step c1 _ hs1, hin1, hc1]
      simp [preTr, controlAction, scanPre]
  | b :: b' :: r, i, c, hd, hi, hs, hp => by
    have hlt : i + 1 < x.length := by
      have := congrArg List.length hd; simp at this; omega
    have hin : c.inputSymbol = some b := by
      rw [inputSymbol_at c i hi hp, ← List.head?_drop, hd]; rfl
    let c1 := preTM.tm.step c
    have hc1 : c1 = (preTr .scan0 (some b) c.workTapeSymbols).apply c := by
      simp only [c1]; rw [preTM_step c _ hs, hin]
    have hp1 : c1.inputPos.val = (i + 1) + 1 := by
      rw [hc1]; simp only [preTr, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]; simp [hp]
    have hd1 : x.drop (i + 1) = b' :: r := by rw [← List.drop_drop, hd]; rfl
    have hin1 : c1.inputSymbol = some b' := by
      rw [inputSymbol_at c1 (i + 1) (by omega) hp1, ← List.head?_drop, hd1]; rfl
    have hs1 : c1.state = some (.scan1 b) := by rw [hc1]; rfl
    let c2 := preTM.tm.step c1
    have hc2 : c2 = (preTr (.scan1 b) (some b') c1.workTapeSymbols).apply c1 := by
      simp only [c2]; rw [preTM_step c1 _ hs1, hin1]
    have hp2 : c2.inputPos.val = (i + 2) + 1 := by
      rw [hc2]; simp only [preTr, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]; simp [hp1]
    have hout2 : c2.output = c.output ++ [b, b'] := by
      rw [hc2, hc1]; simp [preTr]
    have hrun2 : preTM.tm.runFrom c 2 = c2 := rfl
    by_cases hbb : b = b'
    · have hs2 : c2.state = some .scan0 := by rw [hc2]; simp [preTr, hbb]
      have hd2 : x.drop (i + 2) = r := by rw [← List.drop_drop, hd]; rfl
      obtain ⟨t, ht, h1, h2⟩ := pre_scan x r (i + 2) c2 hd2 (by omega) hs2 hp2
      refine ⟨2 + t, by simp; omega, ?_, ?_⟩
      · rw [MultiTapeTM.runFrom_add, hrun2]; exact h1
      · rw [MultiTapeTM.runFrom_add, hrun2, h2, hout2]
        simp [scanPre, hbb]
    · have hs2 : c2.state = some .rwStart := by rw [hc2]; simp [preTr, hbb]
      refine ⟨2, by simp, ?_, ?_⟩
      · rw [hrun2]; exact hs2
      · rw [hrun2, hout2]; simp [scanPre, hbb]

/-- The copying phase: from input position `i + 1` with `drop i x = rest`, the machine
halts after exactly `|rest| + 1` steps, having appended `rest`.

**Proof sketch.** Recursion on `rest`. On an empty remainder the head reads a blank
and the machine halts in one step without output. On `b :: r` one step copies `b` to
the output and advances the input head, staying in the copy state; the recursive call
on `r` from position `i + 2` accounts for the remaining `|r| + 1` steps. -/
private theorem pre_copy (x : List Bool) : ∀ (rest : List Bool) (i : ℕ)
    (c : Cfg 0 Bool PreState x), x.drop i = rest → i ≤ x.length →
    c.state = some .copy → c.inputPos.val = i + 1 →
    (preTM.tm.runFrom c (rest.length + 1)).state = none ∧
      (preTM.tm.runFrom c (rest.length + 1)).output = c.output ++ rest
  | [], i, c, hd, hi, hs, hp => by
    have hin : c.inputSymbol = none := by
      rw [inputSymbol_at c i hi hp, ← List.head?_drop, hd]; rfl
    change (preTM.tm.step c).state = none ∧ (preTM.tm.step c).output = _
    rw [preTM_step c _ hs, hin]
    simp [preTr]
  | b :: r, i, c, hd, hi, hs, hp => by
    have hlt : i < x.length := by
      have := congrArg List.length hd; simp at this; omega
    have hin : c.inputSymbol = some b := by
      rw [inputSymbol_at c i hi hp, ← List.head?_drop, hd]; rfl
    let c1 := preTM.tm.step c
    have hc1 : c1 = (preTr .copy (some b) c.workTapeSymbols).apply c := by
      simp only [c1]; rw [preTM_step c _ hs, hin]
    have hp1 : c1.inputPos.val = (i + 1) + 1 := by
      rw [hc1]; simp only [preTr, Action.apply]
      rw [moveInputPos_pos_of_ne_right _ (by omega)]; simp [hp]
    have hd1 : x.drop (i + 1) = r := by rw [← List.drop_drop, hd]; rfl
    have hs1 : c1.state = some .copy := by rw [hc1]; rfl
    obtain ⟨h1, h2⟩ := pre_copy x r (i + 1) c1 hd1 (by omega) hs1 hp1
    have hrun : preTM.tm.runFrom c ((b :: r).length + 1) =
        preTM.tm.runFrom c1 (r.length + 1) := by
      rw [List.length_cons, MultiTapeTM.runFrom_succ_eq_step]
    rw [hrun]
    refine ⟨h1, ?_⟩
    rw [h2, hc1]
    simp [preTr]

/-- **Prefix duplication** [glue for AB09, Theorem 3.1]: `preTM` computes
`x ↦ scanPre x ++ x` within `3|x| + 5` steps.

**Proof sketch.** Scan (`pre_scan`, at most `|x| + 1` steps, emitting `scanPre x`),
rewind the input head (`Turing.FinTM.timed_rewind`, at most `|x| + 3` steps), and copy
(`pre_copy`, exactly `|x| + 1` steps, emitting `x`). -/
theorem preTM_computes (x : List Bool) :
    preTM.ComputesInTime x (scanPre x ++ x) (3 * x.length + 5) := by
  obtain ⟨t₁, ht₁, h1, h2⟩ := pre_scan x x 0 (preTM.tm.initCfg x) (by simp) (by omega) rfl rfl
  let c₁ := preTM.tm.runFrom (preTM.tm.initCfg x) t₁
  obtain ⟨r, hr, hrun⟩ := timed_rewind preTM.tm PreState.rwStart PreState.rwScan
    (some .copy) (fun inp _ => by cases inp <;> rfl) (fun inp _ => by cases inp <;> rfl) c₁ h1
  let c₂ : Cfg 0 Bool PreState x := {c₁ with state := some .copy, inputPos := 1}
  have hc := pre_copy x x 0 c₂ (by simp) (by omega) rfl rfl
  have hrun' : preTM.tm.runFrom (preTM.tm.initCfg x) (t₁ + r + (x.length + 1)) =
      preTM.tm.runFrom c₂ (x.length + 1) := by
    rw [MultiTapeTM.runFrom_add _ (t₁ + r), MultiTapeTM.runFrom_add _ t₁ r]
    change preTM.tm.runFrom (preTM.tm.runFrom c₁ r) _ = _
    rw [hrun]
  have hcomp : preTM.ComputesInTime x (scanPre x ++ x) (t₁ + r + (x.length + 1)) := by
    rw [computesInTime_iff, hrun']
    refine ⟨hc.1, ?_⟩
    rw [hc.2]
    change c₁.output ++ x = _
    rw [h2]
    rfl
  apply hcomp.mono
  have := c₁.inputPos.isLt
  omega

end Complexity.TimeHierarchy
