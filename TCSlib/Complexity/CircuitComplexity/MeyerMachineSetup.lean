/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.MeyerMachineParse

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Meyer's theorem: the tableau machine's setup phase

The run analysis of the setup phase of `Complexity.Meyer.tabTM`: reading the two
pair-coded fields, copying the input suffix, and rewinding the three auxiliary tapes.
The result `Complexity.Meyer.tabTM_setup` says that on every input the machine either
rejects within `|y| + 1` steps (truncated query) or reaches the counter-loop entry with
the parsed fields on its tapes within `2|y| + 4` steps.

## Main definitions

None; the configurations are those of `MeyerMachineParse.lean`.

## Main results

* `Complexity.Meyer.field_some`, `Complexity.Meyer.field_none` — reading a field.
* `Complexity.Meyer.cpy_run` — copying the input.
* `Complexity.Meyer.rewX_run`, `Complexity.Meyer.rewC_run`, `Complexity.Meyer.rewO_run` —
  the rewinds.
* `Complexity.Meyer.tabTM_setup` — the setup phase.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.4, Theorem 6.20, pp. 114–115.)
-/

namespace Complexity.Meyer

open Turing Turing.FinTM Complexity.TimeHierarchy

variable (M : FinTM Bool)

/-- Reading through a drop. -/
theorem getElem?_of_drop {y rest : List Bool} {p : ℕ} (h : y.drop (p - 1) = rest) (i : ℕ) :
    y[p - 1 + i]? = rest[i]? := by
  rw [← h, List.getElem?_drop]

/-- **Reading a complete field**: from the field-reading state at position `p`, a coded
field `w` followed by an end pair is read in `2|w| + 2` steps and appended to the field's
tape (`C` for `f = false`, `O` for `f = true`).

**Proof sketch.** Recursion following `readField`: a data pair `(b, true)` takes two steps
and appends `b` to the field's tape; an end pair `(e, false)` takes two steps and moves to
the next phase. -/
theorem field_some {y : List Bool} (f : Bool) (bits : Fin (nbits M) → Bool) :
    ∀ (rest : List Bool) (p : ℕ) (wC wO w r : List Bool), 1 ≤ p → y.drop (p - 1) = rest →
      readField rest = some (w, r) →
      (tabTM M).tm.runFrom (pcfg M (.fA f bits) (fpos y p) [] wC wO) (2 * w.length + 2) =
        pcfg M (if f then .cpy bits else .fA true bits) (fpos y (p + 2 * w.length + 2)) []
          (if f then wC else wC ++ w) (if f then wO ++ w else wO)
  | b :: true :: r', p, wC, wO, w, r, h1, hd, hr => by
    simp only [readField, Option.map_eq_some_iff] at hr
    obtain ⟨⟨w', r''⟩, hw', he⟩ := hr
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    have hl : p - 1 + 2 ≤ y.length := by
      have := congrArg List.length hd; simp at this; omega
    have r0 : y[p - 1]? = some b := by simpa using getElem?_of_drop hd 0
    have r1 : y[p + 1 - 1]? = some true := by
      have := getElem?_of_drop hd 1; rw [show p - 1 + 1 = p + 1 - 1 by omega] at this; simpa using this
    have hd' : y.drop (p + 2 - 1) = r' := by
      rw [show p + 2 - 1 = (p - 1) + 2 by omega, ← List.drop_drop, hd]; rfl
    have ih := field_some f bits r' (p + 2) (if f then wC else wC ++ [b])
      (if f then wO ++ [b] else wO) w' r'' (by omega) hd' hw'
    rw [show 2 * (b :: w').length + 2 = (2 * w'.length + 2) + 1 + 1 by simp; ring,
      MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_succ_eq_step,
      pcfg_fA M f bits p h1 (by omega) b r0,
      pcfg_fB_true M f b bits (p + 1) (by omega) (by omega) r1]
    rw [show p + 1 + 1 = p + 2 by omega, ih,
      show p + 2 + 2 * w'.length + 2 = p + 2 * (b :: w').length + 2 by simp; ring]
    cases f <;> simp
  | e :: false :: r', p, wC, wO, w, r, h1, hd, hr => by
    simp only [readField, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    have hl : p - 1 + 2 ≤ y.length := by
      have := congrArg List.length hd; simp at this; omega
    have r0 : y[p - 1]? = some e := by simpa using getElem?_of_drop hd 0
    have r1 : y[p + 1 - 1]? = some false := by
      have := getElem?_of_drop hd 1; rw [show p - 1 + 1 = p + 1 - 1 by omega] at this; simpa using this
    rw [show 2 * ([] : List Bool).length + 2 = 0 + 1 + 1 by rfl,
      MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_succ_eq_step,
      pcfg_fA M f bits p h1 (by omega) e r0,
      pcfg_fB_false M f e bits (p + 1) (by omega) (by omega) r1, MultiTapeTM.runFrom_zero]
    cases f <;> simp
  | [], _, _, _, _, _, _, _, hr => by simp [readField] at hr
  | [_], _, _, _, _, _, _, _, hr => by simp [readField] at hr

/-- A halted rejection persists. -/
theorem reject_persist {y : List Bool} (c : Cfg (tabTM M).k Bool (tabTM M).State y) (s : ℕ)
    (h : ((tabTM M).tm.runFrom c s).state = none ∧ ((tabTM M).tm.runFrom c s).output = [false])
    (s' : ℕ) (hs : s ≤ s') :
    ((tabTM M).tm.runFrom c s').state = none ∧ ((tabTM M).tm.runFrom c s').output = [false] := by
  rw [show s' = s + (s' - s) by omega, MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_of_halt _ h.1]
  exact h

/-- **A truncated field is rejected** within `|rest| + 1` steps.

**Proof sketch.** Recursion following `readField`: data pairs are consumed as in
`field_some`; a truncated end (no symbol, or a lone first symbol) is read as a blank and
rejected (`pcfg_reject`). -/
theorem field_none {y : List Bool} (f : Bool) (bits : Fin (nbits M) → Bool) :
    ∀ (rest : List Bool) (p : ℕ) (wC wO : List Bool), 1 ≤ p → p + rest.length = y.length + 1 →
      y.drop (p - 1) = rest → readField rest = none →
      ∃ s ≤ rest.length + 1,
        ((tabTM M).tm.runFrom (pcfg M (.fA f bits) (fpos y p) [] wC wO) s).state = none ∧
        ((tabTM M).tm.runFrom (pcfg M (.fA f bits) (fpos y p) [] wC wO) s).output = [false]
  | b :: true :: r', p, wC, wO, h1, hlen, hd, hr => by
    simp only [readField, Option.map_eq_none_iff] at hr
    have r0 : y[p - 1]? = some b := by simpa using getElem?_of_drop hd 0
    have r1 : y[p + 1 - 1]? = some true := by
      have := getElem?_of_drop hd 1; rw [show p - 1 + 1 = p + 1 - 1 by omega] at this; simpa using this
    have hd' : y.drop (p + 2 - 1) = r' := by
      rw [show p + 2 - 1 = (p - 1) + 2 by omega, ← List.drop_drop, hd]; rfl
    simp only [List.length_cons] at hlen
    obtain ⟨s, hs, h⟩ := field_none f bits r' (p + 2) (if f then wC else wC ++ [b])
      (if f then wO ++ [b] else wO) (by omega) (by omega) hd' hr
    refine ⟨s + 1 + 1, by simp; omega, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_succ_eq_step,
      pcfg_fA M f bits p h1 (by omega) b r0,
      pcfg_fB_true M f b bits (p + 1) (by omega) (by omega) r1, show p + 1 + 1 = p + 2 by omega]
    exact h
  | _ :: false :: r', _, _, _, _, _, _, hr => by simp [readField] at hr
  | [], p, wC, wO, h1, hlen, hd, _ => by
    have r0 : y[p - 1]? = none := by simpa using getElem?_of_drop hd 0
    refine ⟨0 + 1, by simp, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    exact pcfg_reject M _ (fun _ => rfl) p h1 (by simp at hlen; omega) r0 _ _ _
  | [b], p, wC, wO, h1, hlen, hd, _ => by
    have r0 : y[p - 1]? = some b := by simpa using getElem?_of_drop hd 0
    have r1 : y[p + 1 - 1]? = none := by
      have := getElem?_of_drop hd 1; rw [show p - 1 + 1 = p + 1 - 1 by omega] at this; simpa using this
    simp only [List.length_cons, List.length_nil] at hlen
    refine ⟨0 + 1 + 1, by simp, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero, pcfg_fA M f bits p h1 (by omega) b r0]
    exact pcfg_reject M _ (fun _ => rfl) (p + 1) (by omega) (by omega) r1 _ _ _

/-- **Copying the input suffix** onto the copy tape, then stepping its head back onto the
last copied cell.

**Proof sketch.** Induction on the remaining input: each input bit is written to the copy
tape; at the right blank the copy head steps back and the rewind starts. -/
theorem cpy_run {y : List Bool} (bits : Fin (nbits M) → Bool) :
    ∀ (rest : List Bool) (p : ℕ) (wX wC wO : List Bool), 1 ≤ p →
      p + rest.length = y.length + 1 → y.drop (p - 1) = rest →
      (tabTM M).tm.runFrom (pcfg M (.cpy bits) (fpos y p) wX wC wO) (rest.length + 1) =
        acfg M (some (.rewX bits)) (fpos y (y.length + 1)) (bufferTape (wX ++ rest))
          (bufferTape wC) (bufferTape wO) ((wX ++ rest).length - 1) wC.length wO.length []
  | [], p, wX, wC, wO, h1, hlen, hd => by
    have r0 : y[p - 1]? = none := by simpa using getElem?_of_drop hd 0
    simp only [List.length_nil] at hlen
    rw [MultiTapeTM.runFrom_succ_eq_step, List.length_nil, MultiTapeTM.runFrom_zero,
      pcfg_step M _ p h1 (by omega), r0]
    simp only [tabTr]
    rw [pcfg, tact_idle_apply]
    simp only [one_0_0, one_0_1, one_0_2, wr_none, SignType.coe_zero, add_zero, List.append_nil,
      Option.toList, moveInputPos_zero]
    congr 1
    ext; simp [fpos]; omega
  | b :: r, p, wX, wC, wO, h1, hlen, hd => by
    have r0 : y[p - 1]? = some b := by simpa using getElem?_of_drop hd 0
    have hd' : y.drop (p + 1 - 1) = r := by
      rw [show p + 1 - 1 = (p - 1) + 1 by omega, ← List.drop_drop, hd]; rfl
    simp only [List.length_cons] at hlen ⊢
    have hstep : (tabTM M).tm.step (pcfg M (.cpy bits) (fpos y p) wX wC wO) =
        pcfg M (.cpy bits) (fpos y (p + 1)) (wX ++ [b]) wC wO := by
      rw [pcfg_step M _ p h1 (by omega), r0]
      simp only [tabTr]
      rw [pcfg, tact_idle_apply, moveInputPos_fpos (by omega)]
      simp [pcfg, bufferTape_write]
    rw [MultiTapeTM.runFrom_succ_eq_step, hstep,
      cpy_run bits r (p + 1) (wX ++ [b]) wC wO (by omega) (by omega) hd']
    simp

/-! ### Rewinding the auxiliary tapes -/

section rewind

variable {y : List Bool} (bits : Fin (nbits M) → Bool) (P : Fin (y.length + 2))

/-- Reading auxiliary tape `0` in block form. -/
@[simp] theorem aux_read0 {α : Type} (f : Fin M.k → α) (a b c : α) :
    (Fin.addCases f ![a, b, c] : Fin (M.k + 3) → α) (Fin.natAdd M.k 0) = a := by
  simp [Fin.addCases_right]
/-- Reading auxiliary tape `1` in block form. -/
@[simp] theorem aux_read1 {α : Type} (f : Fin M.k → α) (a b c : α) :
    (Fin.addCases f ![a, b, c] : Fin (M.k + 3) → α) (Fin.natAdd M.k 1) = b := by
  simp [Fin.addCases_right]
/-- Reading auxiliary tape `2` in block form. -/
@[simp] theorem aux_read2 {α : Type} (f : Fin M.k → α) (a b c : α) :
    (Fin.addCases f ![a, b, c] : Fin (M.k + 3) → α) (Fin.natAdd M.k 2) = c := by
  simp [Fin.addCases_right]

/-- A stored word read at cell `j - 1` for `1 ≤ j ≤ |w|`. -/
theorem bufferTape_pred (w : List Bool) (j : ℕ) (hj : j < w.length) :
    bufferTape w (((j + 1 : ℕ) : ℤ) - 1) = some w[j] := by
  rw [show (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) by omega, bufferTape_nat,
    List.getElem?_eq_getElem hj]

/-- **Rewinding the copy tape** from cell `j - 1` takes `j + 1` steps and starts the
counter rewind.

**Proof sketch.** Induction on `j`: move left over stored symbols; at cell `-1` move the
copy head to `0` and start rewinding the counter. -/
theorem rewX_run (w : List Bool) (τ1 τ2 : ℤ → Option Bool) (z1 z2 : ℤ) :
    ∀ j, j ≤ w.length →
      (tabTM M).tm.runFrom (acfg M (some (.rewX bits)) P (bufferTape w) τ1 τ2 ((j : ℤ) - 1)
        z1 z2 []) (j + 1) =
        acfg M (some (.rewC bits)) P (bufferTape w) τ1 τ2 0 (z1 - 1) z2 [] := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, acfg_step]
    simp only [tabTr, aux_read0, Nat.cast_zero, zero_sub, bufferTape_left]
    rw [tact_idle_apply]
    simp [SignType.neg_eq_neg_one, sub_eq_add_neg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, acfg_step]
    simp only [tabTr, aux_read0, bufferTape_pred w j (by omega)]
    rw [tact_idle_apply]
    simp only [one_0_0, one_0_1, one_0_2, wr_none, SignType.coe_zero, add_zero, List.append_nil,
      Option.toList, moveInputPos_zero, SignType.neg_eq_neg_one, SignType.coe_neg_one]
    rw [show ((j + 1 : ℕ) : ℤ) - 1 + -1 = (j : ℤ) - 1 by omega]
    exact ih (by omega)

/-- **Rewinding the counter** from cell `j - 1` takes `j + 1` steps and starts the
offset rewind.

**Proof sketch.** As `rewX_run`, on the counter. -/
theorem rewC_run (w : List Bool) (τ0 τ2 : ℤ → Option Bool) (z0 z2 : ℤ) :
    ∀ j, j ≤ w.length →
      (tabTM M).tm.runFrom (acfg M (some (.rewC bits)) P τ0 (bufferTape w) τ2 z0 ((j : ℤ) - 1)
        z2 []) (j + 1) =
        acfg M (some (.rewO bits)) P τ0 (bufferTape w) τ2 z0 0 (z2 - 1) [] := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, acfg_step]
    simp only [tabTr, aux_read1, Nat.cast_zero, zero_sub, bufferTape_left]
    rw [tact_idle_apply]
    simp [SignType.neg_eq_neg_one, sub_eq_add_neg]
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, acfg_step]
    simp only [tabTr, aux_read1, bufferTape_pred w j (by omega)]
    rw [tact_idle_apply]
    simp only [one_1_0, one_1_1, one_1_2, wr_none, SignType.coe_zero, add_zero, List.append_nil,
      Option.toList, moveInputPos_zero, SignType.neg_eq_neg_one, SignType.coe_neg_one]
    rw [show ((j + 1 : ℕ) : ℤ) - 1 + -1 = (j : ℤ) - 1 by omega]
    exact ih (by omega)

/-- **Rewinding the offset tape** from cell `j - 1` takes `j + 1` steps and enters the
counter loop with `M`'s initial state.

**Proof sketch.** As `rewX_run`, on the offset tape; at the end the counter loop starts with
`M`'s initial state. -/
theorem rewO_run (w : List Bool) (τ0 τ1 : ℤ → Option Bool) (z0 z1 : ℤ) :
    ∀ j, j ≤ w.length →
      (tabTM M).tm.runFrom (acfg M (some (.rewO bits)) P τ0 τ1 (bufferTape w) z0 z1
        ((j : ℤ) - 1) []) (j + 1) =
        acfg M (some (.dec bits M.tm.q₀ .empty true)) P τ0 τ1 (bufferTape w) z0 z1 0 [] := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero, acfg_step]
    simp only [tabTr, aux_read2, Nat.cast_zero, zero_sub, bufferTape_left]
    rw [tact_idle_apply]
    simp
  | succ j ih =>
    intro hj
    rw [MultiTapeTM.runFrom_succ_eq_step, acfg_step]
    simp only [tabTr, aux_read2, bufferTape_pred w j (by omega)]
    rw [tact_idle_apply]
    simp only [one_2_0, one_2_1, one_2_2, wr_none, SignType.coe_zero, add_zero, List.append_nil,
      Option.toList, moveInputPos_zero, SignType.neg_eq_neg_one, SignType.coe_neg_one]
    rw [show ((j + 1 : ℕ) : ℤ) - 1 + -1 = (j : ℤ) - 1 by omega]
    exact ih (by omega)

end rewind

/-! ### The setup phase -/

/-- The blank tape is the empty stored word. -/
theorem bl_eq : bl = bufferTape [] := by simp

/-- The setup configuration with nothing written. -/
theorem pcfg_nil {y : List Bool} (st : St M) (p : Fin (y.length + 2)) :
    pcfg M st p [] [] [] = acfg M (some st) p bl bl bl 0 0 0 [] := by
  simp [pcfg]

/-- **The setup phase of the tableau machine.** On a truncated query the machine rejects
within `|y| + 1` steps; on a query parsing as `(bits, t, a, x)` it reaches, within
`2|y| + 4` steps, the counter-loop entry: state `dec bits q₀ empty true`, the words `x`,
`t`, `a` on the copy tape, counter and offset tape with all three heads on cell `0`,
`M`'s tapes blank, empty output.

**Proof sketch.** Compose the phase lemmas: selector bits (`sel_done`/`sel_reject`),
the two fields (`field_some`/`field_none`), the copy (`cpy_run`) and the three rewinds
(`rewX_run`, `rewC_run`, `rewO_run`). The positions are tracked through
`readField_eq_some`; the step count is `|y| + |x| + |t| + |a| + 4`. -/
theorem tabTM_setup (y : List Bool) :
    (parseQ (nbits M) y = none → ∃ s ≤ y.length + 1,
      ((tabTM M).tm.runFrom ((tabTM M).tm.initCfg y) s).state = none ∧
      ((tabTM M).tm.runFrom ((tabTM M).tm.initCfg y) s).output = [false]) ∧
    (∀ bits t a x, parseQ (nbits M) y = some (bits, t, a, x) → ∃ s ≤ 2 * y.length + 4,
      (tabTM M).tm.runFrom ((tabTM M).tm.initCfg y) s =
        acfg M (some (.dec bits M.tm.q₀ .empty true)) (fpos y (y.length + 1)) (bufferTape x)
          (bufferTape t) (bufferTape a) 0 0 0 []) := by
  constructor
  · intro hparse
    by_cases hlen : nbits M ≤ y.length
    · have hsel := sel_done M y hlen
      rw [← pcfg_nil] at hsel
      have hd0 : y.drop (nbits M + 1 - 1) = y.drop (nbits M) := by simp
      simp only [parseQ, if_pos hlen] at hparse
      cases h1 : readField (y.drop (nbits M)) with
      | none =>
        obtain ⟨s, hs, h⟩ := field_none M false (fun j => y.getD j false) (y.drop (nbits M)) (nbits M + 1)
          [] [] (by omega) (by simp; omega) hd0 h1
        refine ⟨nbits M + s, by simp at hs; omega, ?_⟩
        rw [MultiTapeTM.runFrom_add, hsel]
        exact h
      | some tr =>
        obtain ⟨t, r⟩ := tr
        rw [h1] at hparse
        simp only at hparse
        cases h2 : readField r with
        | some ax => rw [h2] at hparse; simp at hparse
        | none =>
          obtain ⟨e, he⟩ := readField_eq_some h1
          have hft := field_some M false (fun j => y.getD j false) (y.drop (nbits M)) (nbits M + 1) [] [] t r
            (by omega) hd0 h1
          have hlr : (y.drop (nbits M)).length = 2 * t.length + 2 + r.length := by
            rw [he]; simp; ring
          have hdr : y.drop (nbits M + 1 + 2 * t.length + 2 - 1) = r := by
            rw [show nbits M + 1 + 2 * t.length + 2 - 1 = nbits M + (2 * t.length + 2) by omega,
              ← List.drop_drop, he]
            simp [List.drop_append]
          obtain ⟨s, hs, h⟩ := field_none M true (fun j => y.getD j false) r
            (nbits M + 1 + 2 * t.length + 2) t [] (by omega) (by simp at hlr; omega) hdr h2
          refine ⟨nbits M + (2 * t.length + 2) + s, by simp at hlr; omega, ?_⟩
          rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hsel, hft]
          simpa using h
    · have := sel_reject M y (by omega)
      exact ⟨y.length + 1, le_rfl, this⟩
  · intro bits t0 a0 x0 hparse
    have hlen : nbits M ≤ y.length := by
      by_contra h; simp [parseQ, h] at hparse
    simp only [parseQ, if_pos hlen] at hparse
    cases h1 : readField (y.drop (nbits M)) with
    | none => rw [h1] at hparse; simp at hparse
    | some tr =>
      obtain ⟨t, r⟩ := tr
      rw [h1] at hparse
      simp only at hparse
      cases h2 : readField r with
      | none => rw [h2] at hparse; simp at hparse
      | some ax =>
        obtain ⟨a, x⟩ := ax
        rw [h2] at hparse
        simp only [Option.some.injEq, Prod.mk.injEq] at hparse
        obtain ⟨hb, ht, ha, hx⟩ := hparse
        subst hb ht ha hx
        obtain ⟨e, he⟩ := readField_eq_some h1
        obtain ⟨e', he'⟩ := readField_eq_some h2
        have hy : y = y.take (nbits M) ++ (fcode t ++ e :: false :: (fcode a ++ e' :: false :: x)) := by
          rw [← he', ← he, List.take_append_drop]
        have hylen : y.length = nbits M + 2 * t.length + 2 * a.length + 4 + x.length := by
          conv_lhs => rw [hy]
          simp; omega
        have hsel := sel_done M y hlen
        rw [← pcfg_nil] at hsel
        have hd0 : y.drop (nbits M + 1 - 1) = y.drop (nbits M) := by simp
        have hft := field_some M false (fun j => y.getD j false) (y.drop (nbits M)) (nbits M + 1) [] [] t r
          (by omega) hd0 h1
        have hdr : y.drop (nbits M + 1 + 2 * t.length + 2 - 1) = r := by
          rw [show nbits M + 1 + 2 * t.length + 2 - 1 = nbits M + (2 * t.length + 2) by omega,
            ← List.drop_drop, he]
          simp [List.drop_append]
        have hfa := field_some M true (fun j => y.getD j false) r (nbits M + 1 + 2 * t.length + 2)
          t [] a x (by omega) hdr h2
        have hdx : y.drop (nbits M + 1 + 2 * t.length + 2 + 2 * a.length + 2 - 1) = x := by
          have hrest : y.drop (nbits M) = (fcode t ++ [e, false] ++ fcode a ++ [e', false]) ++ x := by
            rw [he, he']; simp
          rw [show nbits M + 1 + 2 * t.length + 2 + 2 * a.length + 2 - 1 =
            nbits M + (2 * t.length + 2 + (2 * a.length + 2)) by omega, ← List.drop_drop, hrest]
          exact List.drop_left' (by simp; ring)
        have hcp := cpy_run M (fun j => y.getD j false) x
          (nbits M + 1 + 2 * t.length + 2 + 2 * a.length + 2) [] t a (by omega) (by omega) hdx
        simp only [List.nil_append] at hcp
        have hrx := rewX_run M (fun j => y.getD j false) (fpos y (y.length + 1)) x
          (bufferTape t) (bufferTape a) (t.length : ℤ) (a.length : ℤ) x.length le_rfl
        have hrc := rewC_run M (fun j => y.getD j false) (fpos y (y.length + 1)) t
          (bufferTape x) (bufferTape a) 0 (a.length : ℤ) t.length le_rfl
        have hro := rewO_run M (fun j => y.getD j false) (fpos y (y.length + 1)) a
          (bufferTape x) (bufferTape t) 0 0 a.length le_rfl
        have s2 : (tabTM M).tm.runFrom ((tabTM M).tm.initCfg y) (nbits M + (2 * t.length + 2)) =
            pcfg M (.fA true (fun j => y.getD j false)) (fpos y (nbits M + 1 + 2 * t.length + 2))
              [] t [] := by
          rw [MultiTapeTM.runFrom_add, hsel, hft]; simp
        have s3 : (tabTM M).tm.runFrom ((tabTM M).tm.initCfg y)
            (nbits M + (2 * t.length + 2) + (2 * a.length + 2)) =
            pcfg M (.cpy (fun j => y.getD j false))
              (fpos y (nbits M + 1 + 2 * t.length + 2 + 2 * a.length + 2)) [] t a := by
          rw [MultiTapeTM.runFrom_add, s2, hfa]; simp
        have s4 : (tabTM M).tm.runFrom ((tabTM M).tm.initCfg y)
            (nbits M + (2 * t.length + 2) + (2 * a.length + 2) + (x.length + 1)) =
            acfg M (some (.rewX (fun j => y.getD j false))) (fpos y (y.length + 1)) (bufferTape x)
              (bufferTape t) (bufferTape a) ((x.length : ℤ) - 1) t.length a.length [] := by
          rw [MultiTapeTM.runFrom_add, s3, hcp]
        have s5 : (tabTM M).tm.runFrom ((tabTM M).tm.initCfg y)
            (nbits M + (2 * t.length + 2) + (2 * a.length + 2) + (x.length + 1) + (x.length + 1)) =
            acfg M (some (.rewC (fun j => y.getD j false))) (fpos y (y.length + 1)) (bufferTape x)
              (bufferTape t) (bufferTape a) 0 ((t.length : ℤ) - 1) a.length [] := by
          rw [MultiTapeTM.runFrom_add, s4, hrx]
        have s6 : (tabTM M).tm.runFrom ((tabTM M).tm.initCfg y)
            (nbits M + (2 * t.length + 2) + (2 * a.length + 2) + (x.length + 1) + (x.length + 1) +
              (t.length + 1)) =
            acfg M (some (.rewO (fun j => y.getD j false))) (fpos y (y.length + 1)) (bufferTape x)
              (bufferTape t) (bufferTape a) 0 0 ((a.length : ℤ) - 1) [] := by
          rw [MultiTapeTM.runFrom_add, s5, hrc]
        refine ⟨nbits M + (2 * t.length + 2) + (2 * a.length + 2) + (x.length + 1) + (x.length + 1) +
          (t.length + 1) + (a.length + 1), by omega, ?_⟩
        rw [MultiTapeTM.runFrom_add, s6, hro]

end Complexity.Meyer
