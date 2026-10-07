/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassP.P

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Example: palindromes are decidable in linear time

The language `PAL` of binary palindromes is decidable in linear time, hence in `P`.
[AB09, Examples 1.1 and 1.4] This is the phase-1 sanity check that the model and class
definitions are *usable*: proving it requires constructing a concrete machine and running
the definitional semantics on it end to end.

## Deviations from [AB09]

* [AB09, Example 1.1] states "within `3n` steps". We state `PAL ∈ DTIME (n + 1)`: the
  `∃ c` in `DTIME` absorbs the leading constant, and the `+ 1` covers the empty input, on
  which every machine needs at least one step to halt (`3 · 0 = 0` is unachievable — the
  book ignores this degenerate case).

## Main definitions

* `Complexity.PAL` — the palindrome language. [AB09, Example 1.1]

## Main results

* `Complexity.PAL_mem_DTIME_linear` — `PAL ∈ DTIME (n + 1)`. [AB09, Example 1.4]
* `Complexity.PAL_mem_P` — `PAL ∈ P`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Examples 1.1, 1.4.)
-/

namespace Complexity

open Turing

/-- The language of binary palindromes. [AB09, Example 1.1] -/
def PAL : Language Bool := {x | x.reverse = x}

/-- The audited copy/rewind/test transition table; states are numbered 0, 1, 2.
[AB09, Example 1.1], with the boundary transitions from the phase-1 audit. -/
private def palTM : FinTM Bool where
  k := 1
  State := Fin 3
  tm :=
    { q₀ := 0
      tr := fun q inp work =>
        if q = 0 then
          match inp with
          | some b => ⟨.pos, fun _ => (some (some b), .pos), none, some 0⟩
          | none => ⟨.neg, fun _ => (none, .zero), none, some 1⟩
        else if q = 1 then
          match inp with
          | some _ => ⟨.neg, fun _ => (none, .zero), none, some 1⟩
          | none => ⟨.pos, fun _ => (none, .neg), none, some 2⟩
        else
          match inp with
          | none => ⟨.zero, fun _ => (none, .zero), some true, none⟩
          | some b =>
            if work 0 = some b then
              ⟨.pos, fun _ => (none, .neg), none, some 2⟩
            else ⟨.zero, fun _ => (none, .zero), some false, none⟩ }

/-- The input word restricted to nonnegative cells below `t`. -/
private def palTape (x : List Bool) (t : ℕ) (z : ℤ) : Option Bool :=
  if 0 ≤ z ∧ z < (t : ℤ) then x[z.toNat]? else none

/-- Canonical live configurations used in the three phase invariants. -/
private def palCfg (x : List Bool) (q : Fin 3) (p : Fin (x.length + 2))
    (w : ℤ) (t : ℕ) : Cfg 1 Bool (Fin 3) x :=
  ⟨some q, p, fun _ => palTape x t, fun _ => w, []⟩

/-- Writing the next input bit extends the copied prefix by one cell. -/
private lemma palTape_write (x : List Bool) (t : ℕ) (ht : t < x.length) :
    Function.update (palTape x t) (t : ℤ) (some x[t]) = palTape x (t + 1) := by
  funext z
  by_cases hz : z = (t : ℤ)
  · subst z
    simp [palTape, ht]
  · rw [Function.update_of_ne hz]
    simp only [palTape]
    by_cases hlt : 0 ≤ z ∧ z < (t : ℤ)
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]

/-- A copy transition writes at the old head, then advances both heads. -/
private lemma pal_copy_step (x : List Bool) (t : ℕ) (ht : t < x.length) :
    palTM.tm.step (palCfg x 0 ⟨t + 1, by omega⟩ t t) =
      palCfg x 0 ⟨t + 2, by omega⟩ (t + 1) (t + 1) := by
  have hs : (palCfg x 0 ⟨t + 1, by omega⟩ t t).inputSymbol = some x[t] :=
    inputSymbolInner t (by simp only [palCfg]; omega) ht
  simp only [MultiTapeTM.step, palCfg] at hs ⊢
  rw [hs]
  apply Cfg.ext
  · simp [palTM, Action.apply]
  · apply Fin.ext
    simp only [palTM, Action.apply, ↓reduceIte]
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  · funext j
    simpa [palTM, Action.apply] using palTape_write x t ht
  · funext j
    simp [palTM, Action.apply]
  · simp [palTM, Action.apply]

/-- Copy invariant, including the untouched blank cells outside the prefix.
**Proof sketch.** At time zero the prefix is empty. Each subsequent transition
extends it by the next input bit, using `pal_copy_step`. -/
private lemma pal_copy (x : List Bool) : ∀ t (ht : t ≤ x.length),
    palTM.tm.runFrom (palTM.tm.initCfg x) t =
      palCfg x 0 ⟨t + 1, by omega⟩ t t := by
  intro t
  induction t with
  | zero =>
    intro ht
    apply Cfg.ext
    · rfl
    · rfl
    · funext j z
      simp only [MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg, Cfg.init, palCfg, palTape]
      rw [if_neg (by omega)]
    · rfl
    · rfl
  | succ t ih =>
    intro ht
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    exact pal_copy_step x t (by omega)

/-- The right blank starts the rewind with the input head at position `n`. -/
private lemma pal_copy_end (x : List Bool) :
    palTM.tm.step (palCfg x 0 ⟨x.length + 1, by omega⟩ x.length x.length) =
      palCfg x 1 ⟨x.length, by omega⟩ x.length x.length := by
  have hs : (palCfg x 0 ⟨x.length + 1, by omega⟩ x.length x.length).inputSymbol =
      none := by simp [Cfg.inputSymbol, palCfg]
  simp only [MultiTapeTM.step, palCfg] at hs ⊢
  rw [hs]
  apply Cfg.ext
  · simp [palTM, Action.apply]
  · apply Fin.ext
    simp only [palTM, Action.apply, ↓reduceIte]
    rw [moveInputPos_neg_of_ne_left _ (by simp)]
    simp
  · rfl
  · funext j; simp [palTM, Action.apply]
  · rfl

/-- Rewinding does not move or change the copied work tape. -/
private lemma pal_rewind_step (x : List Bool) (i : ℕ) (hi : i < x.length) :
    palTM.tm.step (palCfg x 1 ⟨i + 1, by omega⟩ x.length x.length) =
      palCfg x 1 ⟨i, by omega⟩ x.length x.length := by
  have hs : (palCfg x 1 ⟨i + 1, by omega⟩ x.length x.length).inputSymbol =
      some x[i] := inputSymbolInner i (by simp only [palCfg]; omega) hi
  simp only [MultiTapeTM.step, palCfg] at hs ⊢
  rw [hs]
  apply Cfg.ext
  · simp [palTM, Action.apply]
  · apply Fin.ext
    change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .neg).val = i
    rw [moveInputPos_neg_of_ne_left _ (by simp)]
    simp
  · rfl
  · funext j; simp [palTM, Action.apply]
  · rfl

/-- The input head reaches the left blank in exactly its current position's steps.
**Proof sketch.** Induct on the input position; each interior transition decreases
it by one and preserves every other field. -/
private lemma pal_rewind (x : List Bool) : ∀ i (hi : i ≤ x.length),
    palTM.tm.runFrom (palCfg x 1 ⟨i, by omega⟩ x.length x.length) i =
      palCfg x 1 0 x.length x.length := by
  intro i
  induction i with
  | zero => intro hi; rfl
  | succ i ih =>
    intro hi
    rw [MultiTapeTM.runFrom_succ_eq_step, pal_rewind_step x i (by omega)]
    exact ih (by omega)

/-- The left boundary transition aligns the input and reversed work-tape scans,
including work position `-1` on empty input. -/
private lemma pal_test_start (x : List Bool) :
    palTM.tm.step (palCfg x 1 0 x.length x.length) =
      palCfg x 2 1 ((x.length : ℤ) - 1) x.length := by
  have hs : (palCfg x 1 0 x.length x.length).inputSymbol = none := by
    simp [Cfg.inputSymbol, palCfg]
  simp only [MultiTapeTM.step, palCfg] at hs ⊢
  rw [hs]
  apply Cfg.ext
  · simp [palTM, Action.apply]
  · apply Fin.ext
    change (moveInputPos (0 : Fin (x.length + 2)) .pos).val = (1 : Fin (x.length + 2)).val
    rw [moveInputPos_pos_of_ne_right _ (by simp)]
    rfl
  · rfl
  · funext j; simp [palTM, Action.apply, sub_eq_add_neg]
  · rfl

/-- In the comparison phase, the work read is the corresponding bit of `reverse`. -/
private lemma pal_test_read (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (palCfg x 2 ⟨i + 1, by omega⟩ ((x.length : ℤ) - 1 - i) x.length).workTapeSymbols 0 =
      some (x.reverse[i]'(by simpa using hi)) := by
  have hz : (x.length : ℤ) - 1 - i = ((x.length - 1 - i : ℕ) : ℤ) := by omega
  simp only [palCfg, Cfg.workTapeSymbols, palTape, hz, Int.toNat_natCast]
  rw [if_pos (by omega), List.getElem?_eq_getElem (by omega), List.getElem_reverse]

/-- A matched pair advances the opposing comparison heads. -/
private lemma pal_test_step (x : List Bool) (i : ℕ) (hi : i < x.length)
    (heq : x.reverse[i]'(by simpa using hi) = x[i]) :
    palTM.tm.step (palCfg x 2 ⟨i + 1, by omega⟩ ((x.length : ℤ) - 1 - i) x.length) =
      palCfg x 2 ⟨i + 2, by omega⟩ ((x.length : ℤ) - 1 - (i + 1)) x.length := by
  have hs : (palCfg x 2 ⟨i + 1, by omega⟩ ((x.length : ℤ) - 1 - i) x.length).inputSymbol =
      some x[i] := inputSymbolInner i (by simp only [palCfg]; omega) hi
  have hw := pal_test_read x i hi
  rw [heq] at hw
  unfold MultiTapeTM.step
  change (palTM.tm.tr (2 : Fin 3) _ _).apply _ = _
  rw [hs]
  simp only [palTM, show (2 : Fin 3) ≠ 0 from by decide,
    show (2 : Fin 3) ≠ 1 from by decide, ↓reduceIte, hw]
  apply Cfg.ext
  · rfl
  · apply Fin.ext
    change (moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) .pos).val = i + 2
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
  · rfl
  · funext j
    simp only [Action.apply, palCfg, SignType.neg_eq_neg_one, SignType.coe_neg_one]
    omega
  · rfl

/-- All opposing pairs at or after position `i` agree. -/
private def palMatches (x : List Bool) (i : ℕ) : Prop :=
  ∀ j (hj : j < x.length), i ≤ j → x.reverse[j]'(by simpa using hj) = x[j]

/-- After a matching comparison, the remaining condition starts at the next bit. -/
private lemma palMatches_succ (x : List Bool) (i : ℕ) (hi : i < x.length)
    (heq : x.reverse[i]'(by simpa using hi) = x[i]) :
    palMatches x i ↔ palMatches x (i + 1) := by
  constructor
  · intro h j hj hij; exact h j hj (by omega)
  · intro h j hj hij
    by_cases hji : j = i
    · subst j; exact heq
    · exact h j hj (by omega)

open Classical in
/-- The comparison phase decides the remaining pointwise equalities in at most
one step per pair plus the final blank transition.
**Proof sketch.** Induct on the number of pairs left. A matching pair reduces to
the induction hypothesis. A mismatch emits false immediately, and halting absorbs
the unused steps. At zero remaining pairs, the right blank emits true. -/
private lemma pal_test (x : List Bool) : ∀ r i (hi : i ≤ x.length)
    (hr : x.length = i + r),
    let c := palTM.tm.runFrom
      (palCfg x 2 ⟨i + 1, by omega⟩ ((x.length : ℤ) - 1 - i) x.length) (r + 1)
    c.state = none ∧ c.output = [if palMatches x i then true else false] := by
  intro r
  induction r with
  | zero =>
    intro i hi hr
    have he : i = x.length := by omega
    subst i
    have hm : palMatches x x.length := by intro j hj hij; omega
    have hs : (palCfg x 2 ⟨x.length + 1, by omega⟩
        ((x.length : ℤ) - 1 - x.length) x.length).inputSymbol = none := by
      simp [Cfg.inputSymbol, palCfg]
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((palTM.tm.tr (2 : Fin 3) _ _).apply _).state = none ∧ _
    rw [hs]
    simp [palTM, Action.apply, palCfg, hm]
  | succ r ih =>
    intro i hi hr
    have hi' : i < x.length := by omega
    by_cases heq : x.reverse[i]'(by simpa using hi') = x[i]
    · simp only [MultiTapeTM.runFrom_succ_eq_step,
        pal_test_step x i hi' heq]
      simpa only [palMatches_succ x i hi' heq] using
        ih (i + 1) (by omega) (by omega)
    · have hs : (palCfg x 2 ⟨i + 1, by omega⟩
          ((x.length : ℤ) - 1 - i) x.length).inputSymbol = some x[i] :=
        inputSymbolInner i (by simp only [palCfg]; omega) hi'
      have hw := pal_test_read x i hi'
      have hm : ¬palMatches x i := fun h => heq (h i hi' (le_refl _))
      let c := palTM.tm.step
        (palCfg x 2 ⟨i + 1, by omega⟩ ((x.length : ℤ) - 1 - i) x.length)
      have hc : c.state = none ∧ c.output = [false] := by
        dsimp only [c]
        unfold MultiTapeTM.step
        change ((palTM.tm.tr (2 : Fin 3) _ _).apply _).state = none ∧ _
        rw [hs]
        simp only [palTM, show (2 : Fin 3) ≠ 0 from by decide,
          show (2 : Fin 3) ≠ 1 from by decide, ↓reduceIte, hw]
        rw [if_neg (by simpa only [Option.some.injEq] using heq)]
        exact ⟨rfl, rfl⟩
      change (palTM.tm.runFrom c (r + 1)).state = none ∧
        (palTM.tm.runFrom c (r + 1)).output = [if palMatches x i then true else false]
      rw [MultiTapeTM.runFrom_of_halt _ hc.1]
      simpa only [if_neg hm] using hc

/-- Palindromes are decidable in linear time. [AB09, Examples 1.1 and 1.4]

**Proof sketch.** Adapt the machine of [AB09, Example 1.1] to our model (bidirectional
tapes, no start symbol, blank = `none`): a one-work-tape machine with states
`{copy, rewind, test}`.

1. *Copy* (`n + 1` steps): move the input head and the work head right in unison, copying
   each input symbol to the work tape, until the input head reads blank (one cell past the
   input). The work head now sits one cell right of the copied string.
2. *Rewind* (`n + 1` steps): move the input head left back to the left boundary cell while
   the work head stays put; then step the work head one cell left onto the last symbol.
3. *Test* (`n + 1` steps): move the input head right and the work head left in unison,
   comparing the input symbol against the work symbol. On a mismatch, emit `false` and
   halt. When the input head reads blank again (all positions matched), emit `true` and
   halt.

Each phase takes at most `n + 1` steps, so some constant `c` (e.g. `c = 4`) gives
`c · (n + 1) ≥ 3n + 3` total steps, witnessing the `DTIME (n + 1)` bound. The formal
proof constructs the machine's transition function explicitly and establishes the
three-phase invariants by induction on the step count. -/
theorem PAL_mem_DTIME_linear : PAL ∈ DTIME fun n => n + 1 := by
  classical
  refine ⟨3, palTM, fun x => ?_⟩
  have hstart : palTM.tm.runFrom (palTM.tm.initCfg x)
      (x.length + 1 + x.length + 1) =
      palCfg x 2 1 ((x.length : ℤ) - 1) x.length := by
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_succ_eq_step', pal_copy x x.length (le_refl _),
      pal_copy_end, pal_rewind x x.length (le_refl _), pal_test_start]
  have hm : palMatches x 0 ↔ x ∈ PAL := by
    constructor
    · intro h
      apply List.ext_getElem List.length_reverse
      intro j hj hj'
      exact h j hj' (Nat.zero_le _)
    · intro h j hj _
      change x.reverse = x at h
      simp only [h]
  have htest := pal_test x x.length 0 (Nat.zero_le _) (by omega)
  have ht : 3 * (x.length + 1) = (x.length + 1 + x.length + 1) + (x.length + 1) := by
    omega
  refine ⟨_, ?_, ?_, rfl⟩
  · dsimp only
    rw [ht, MultiTapeTM.runFrom_add, hstart]
    simpa only [Nat.cast_zero, sub_zero] using htest.1
  · dsimp only
    rw [ht, MultiTapeTM.runFrom_add, hstart]
    simpa only [Nat.cast_zero, sub_zero, MultiTapeTM.indicator, hm] using htest.2

/-- Palindromes are decidable in polynomial time. -/
theorem PAL_mem_P : PAL ∈ P :=
  mem_P_of_dtime_le PAL_mem_DTIME_linear 1 1 fun n => by simp [pow_one]

end Complexity
