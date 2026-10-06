/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.CircuitComplexity.MeyerMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Meyer's theorem: the tableau machine's query format and parsing steps

The query format of `Complexity.Meyer.tabTM` (selector bits, two pair-coded fields, the
verbatim input) with its decoder, and the single-step lemmas of the parsing phase:
reading the selector bits, the pairs of a field, and rejecting a truncated query. The
multi-step runs and the whole setup phase are in `MeyerMachineSetup.lean`.

## Main definitions

* `Complexity.Meyer.fcode` — the pair code of a field.
* `Complexity.Meyer.readField` — decoding one pair-coded field.
* `Complexity.Meyer.query`, `Complexity.Meyer.parseQ` — queries and their decoder.
* `Complexity.Meyer.acfg`, `Complexity.Meyer.pcfg` — setup-phase configurations.

## Main results

* `Complexity.Meyer.readField_fcode`, `Complexity.Meyer.parseQ_query` — the decoders
  invert the encoders.
* `Complexity.Meyer.sel_done`, `Complexity.Meyer.sel_reject` — reading the selector bits.
* `Complexity.Meyer.pcfg_fA`, `Complexity.Meyer.pcfg_fB_true`,
  `Complexity.Meyer.pcfg_fB_false` — one parsing step.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.4, Theorem 6.20, pp. 114–115.)
-/

namespace Complexity.Meyer

open Turing Turing.FinTM Complexity.TimeHierarchy

/-! ### The query format -/

/-- **The pair code of a field**: each bit `b` becomes the pair `(b, true)`; a field ends
with a pair `(e, false)`. -/
def fcode (w : List Bool) : List Bool := w.flatMap fun b => [b, true]

/-- The pair code doubles the length. -/
@[simp] theorem length_fcode (w : List Bool) : (fcode w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [fcode] at ih ⊢; omega

/-- **Decoding one field**: read data pairs `(b, true)` up to an end pair `(_, false)`;
return the field and the rest, or `none` on a truncated string. -/
def readField : List Bool → Option (List Bool × List Bool)
  | b :: true :: rest => (readField rest).map fun p => (b :: p.1, p.2)
  | _ :: false :: rest => some ([], rest)
  | _ => none

/-- Decoding a coded field followed by an end pair. -/
@[simp] theorem readField_fcode (w : List Bool) (e : Bool) (rest : List Bool) :
    readField (fcode w ++ e :: false :: rest) = some (w, rest) := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [fcode, readField] at ih ⊢; simp [ih]

/-- A decoded field is a coded field followed by an end pair. -/
theorem readField_eq_some {s w rest : List Bool} (h : readField s = some (w, rest)) :
    ∃ e, s = fcode w ++ e :: false :: rest := by
  induction s using readField.induct generalizing w rest with
  | case1 b r ih =>
    simp only [readField, Option.map_eq_some_iff] at h
    obtain ⟨⟨w', r'⟩, hw, he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨e, he⟩ := ih hw
    exact ⟨e, by simp [fcode, he]⟩
  | case2 e r =>
    simp only [readField, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨e, rfl⟩
  | case3 s h1 h2 => simp [readField] at h

/-- **A query string** (see the module docstring of `MeyerMachine.lean`). -/
def query {nb : ℕ} (bits : Fin nb → Bool) (t a x : List Bool) : List Bool :=
  List.ofFn bits ++ (fcode t ++ false :: false :: (fcode a ++ false :: false :: x))

/-- The length of a query. -/
@[simp] theorem length_query {nb : ℕ} (bits : Fin nb → Bool) (t a x : List Bool) :
    (query bits t a x).length = nb + 2 * t.length + 2 * a.length + 4 + x.length := by
  simp [query]; omega

/-- **Decoding a query**: the first `nb` bits, two fields and the verbatim rest, or
`none` on a truncated string. -/
def parseQ (nb : ℕ) (y : List Bool) :
    Option ((Fin nb → Bool) × List Bool × List Bool × List Bool) :=
  if nb ≤ y.length then
    match readField (y.drop nb) with
    | none => none
    | some (t, r) =>
      match readField r with
      | none => none
      | some (a, x) => some (fun j => y.getD j false, t, a, x)
  else none

/-- The decoder inverts the query encoder. -/
@[simp] theorem parseQ_query {nb : ℕ} (bits : Fin nb → Bool) (t a x : List Bool) :
    parseQ nb (query bits t a x) = some (bits, t, a, x) := by
  have hd : (query bits t a x).drop nb = fcode t ++ false :: false :: (fcode a ++ false :: false :: x) := by
    simp [query]
  simp only [parseQ, length_query, show nb ≤ nb + 2 * t.length + 2 * a.length + 4 + x.length by omega,
    if_true, hd, readField_fcode]
  congr
  funext j
  simp [query, List.getD_eq_getElem?_getD, List.getElem?_append_left]

/-! ### Setup-phase configurations -/

variable (M : FinTM Bool)

/-- A real input position, clamped into range. -/
def fpos (y : List Bool) (p : ℕ) : Fin (y.length + 2) := ⟨min p (y.length + 1), by omega⟩

/-- Moving right from an in-range position. -/
theorem moveInputPos_fpos {y : List Bool} {p : ℕ} (hp : p ≤ y.length) :
    moveInputPos (fpos y p) .pos = fpos y (p + 1) := by
  have h := moveInputPos_pos_of_ne_right (fpos y p) (by simp [fpos]; omega)
  rw [h]; ext; simp [fpos]; omega

/-- Reading at an in-range position. -/
theorem inputSymbol_fpos {k : ℕ} {S : Type} {y : List Bool} (c : Cfg k Bool S y) {p : ℕ}
    (h1 : 1 ≤ p) (hp : p ≤ y.length + 1) (hc : c.inputPos = fpos y p) :
    c.inputSymbol = y[p - 1]? :=
  inputSymbol_at c (p - 1) (by omega) (by rw [hc]; simp [fpos]; omega)

/-- A configuration with `M`'s tapes blank and auxiliary tapes `τ` with heads `z`. -/
def acfg {y : List Bool} (st : Option (St M)) (p : Fin (y.length + 2))
    (τ0 τ1 τ2 : ℤ → Option Bool) (z0 z1 z2 : ℤ) (out : List Bool) :
    Cfg (tabTM M).k Bool (tabTM M).State y :=
  tcfg M st p (fun _ _ => none) (fun _ => 0) ![τ0, τ1, τ2] ![z0, z1, z2] out

/-- **A step from a blank-`M`-block configuration** applies the transition table to the
input read and the three auxiliary reads. -/
theorem acfg_step {y : List Bool} (q : St M) (p : Fin (y.length + 2))
    (τ0 τ1 τ2 : ℤ → Option Bool) (z0 z1 z2 : ℤ) (out : List Bool) :
    (tabTM M).tm.step (acfg M (some q) p τ0 τ1 τ2 z0 z1 z2 out) =
      (tabTr M q (acfg M (some q) p τ0 τ1 τ2 z0 z1 z2 out).inputSymbol
        (Fin.addCases (fun _ => none) ![τ0 z0, τ1 z1, τ2 z2])).apply
        (acfg M (some q) p τ0 τ1 τ2 z0 z1 z2 out) := by
  rw [acfg, tabTM_step]
  congr 2
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp
  · intro j; simp only [Fin.addCases_right]; fin_cases j <;> rfl

/-- **Applying an action that leaves `M`'s block idle** to a blank-`M`-block
configuration. -/
theorem tact_idle_apply {y : List Bool} (im : SignType)
    (aw : Fin 3 → Option (Option Bool) × SignType) (o : Option Bool) (q : Option (St M))
    (st : Option (St M)) (p : Fin (y.length + 2))
    (τ0 τ1 τ2 : ℤ → Option Bool) (z0 z1 z2 : ℤ) (out : List Bool) :
    (tact M im idle aw o q).apply (acfg M st p τ0 τ1 τ2 z0 z1 z2 out) =
      acfg M q (moveInputPos p im) (wr (aw 0).1 τ0 z0) (wr (aw 1).1 τ1 z1)
        (wr (aw 2).1 τ2 z2) (z0 + (aw 0).2) (z1 + (aw 1).2) (z2 + (aw 2).2)
        (out ++ o.toList) := by
  rw [acfg, tact_apply, acfg]
  congr 1 <;> funext i <;> first | rfl | simp [idle] | (fin_cases i <;> rfl)

section evals

variable (a a' : Option (Option Bool) × SignType)

/-- The idle block action does nothing on every tape. -/
@[simp] theorem idle_apply {n : ℕ} (j : Fin n) : (idle j : Option (Option Bool) × SignType) = (none, 0) := rfl
/-- Evaluation of a one- or two-tape block action at a fixed tape (`one_0_0`). -/
@[simp] theorem one_0_0 : one (0 : Fin 3) a 0 = a := rfl
/-- Evaluation of a one- or two-tape block action at a fixed tape (`one_0_1`). -/
@[simp] theorem one_0_1 : one (0 : Fin 3) a 1 = (none, 0) := rfl
/-- Evaluation of a one- or two-tape block action at a fixed tape (`one_0_2`). -/
@[simp] theorem one_0_2 : one (0 : Fin 3) a 2 = (none, 0) := rfl
/-- Evaluation of a one- or two-tape block action at a fixed tape (`one_1_0`). -/
@[simp] theorem one_1_0 : one (1 : Fin 3) a 0 = (none, 0) := rfl
/-- Evaluation of a one- or two-tape block action at a fixed tape (`one_1_1`). -/
@[simp] theorem one_1_1 : one (1 : Fin 3) a 1 = a := rfl
/-- Evaluation of a one- or two-tape block action at a fixed tape (`one_1_2`). -/
@[simp] theorem one_1_2 : one (1 : Fin 3) a 2 = (none, 0) := rfl
/-- Evaluation of a one- or two-tape block action at a fixed tape (`one_2_0`). -/
@[simp] theorem one_2_0 : one (2 : Fin 3) a 0 = (none, 0) := rfl
/-- Evaluation of a one- or two-tape block action at a fixed tape (`one_2_1`). -/
@[simp] theorem one_2_1 : one (2 : Fin 3) a 1 = (none, 0) := rfl
/-- Evaluation of a one- or two-tape block action at a fixed tape (`one_2_2`). -/
@[simp] theorem one_2_2 : one (2 : Fin 3) a 2 = a := rfl
/-- Evaluation of a one- or two-tape block action at a fixed tape (`two_01_0`). -/
@[simp] theorem two_01_0 : two (0 : Fin 3) a 1 a' 0 = a := rfl
/-- Evaluation of a one- or two-tape block action at a fixed tape (`two_01_1`). -/
@[simp] theorem two_01_1 : two (0 : Fin 3) a 1 a' 1 = a' := rfl
/-- Evaluation of a one- or two-tape block action at a fixed tape (`two_01_2`). -/
@[simp] theorem two_01_2 : two (0 : Fin 3) a 1 a' 2 = (none, 0) := rfl
/-- Evaluation of a one- or two-tape block action at a fixed tape (`two_12_0`). -/
@[simp] theorem two_12_0 : two (1 : Fin 3) a 2 a' 0 = (none, 0) := rfl
/-- Evaluation of a one- or two-tape block action at a fixed tape (`two_12_1`). -/
@[simp] theorem two_12_1 : two (1 : Fin 3) a 2 a' 1 = a := rfl
/-- Evaluation of a one- or two-tape block action at a fixed tape (`two_12_2`). -/
@[simp] theorem two_12_2 : two (1 : Fin 3) a 2 a' 2 = a' := rfl
/-- Evaluation of a one- or two-tape block action at a fixed tape (`two_02_0`). -/
@[simp] theorem two_02_0 : two (0 : Fin 3) a 2 a' 0 = a := rfl
/-- Evaluation of a one- or two-tape block action at a fixed tape (`two_02_1`). -/
@[simp] theorem two_02_1 : two (0 : Fin 3) a 2 a' 1 = (none, 0) := rfl
/-- Evaluation of a one- or two-tape block action at a fixed tape (`two_02_2`). -/
@[simp] theorem two_02_2 : two (0 : Fin 3) a 2 a' 2 = a' := rfl

/-- No write leaves the tape unchanged. -/
@[simp] theorem wr_none (τ : ℤ → Option Bool) (z : ℤ) : wr none τ z = τ := rfl
/-- A write updates the tape at the head. -/
@[simp] theorem wr_some (s : Option Bool) (τ : ℤ → Option Bool) (z : ℤ) :
    wr (some s) τ z = Function.update τ z s := rfl

end evals

/-! ### Reading the selector bits -/

/-- The blank tape. -/
abbrev bl : ℤ → Option Bool := fun _ => none

/-- The initial configuration in block form. -/
theorem init_eq (y : List Bool) :
    (tabTM M).tm.initCfg y =
      acfg M (some (.sel ⟨0, nbitsOf_pos _ _⟩ (fun _ => false))) (fpos y 1) bl bl bl 0 0 0 [] := by
  refine Cfg.ext rfl ?_ ?_ ?_ rfl
  · ext; simp [fpos, acfg, tcfg]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [acfg, tcfg]
    · intro j; simp only [acfg, tcfg, Fin.addCases_right]; fin_cases j <;> rfl
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro j; simp [acfg, tcfg]
    · intro j; simp only [acfg, tcfg, Fin.addCases_right]; fin_cases j <;> rfl

/-- The selector bits read after `m` steps. -/
def selPart (y : List Bool) (m : ℕ) : Fin (nbits M) → Bool :=
  fun j => if j.val < m then y.getD j false else false

/-- Reading one more selector bit. -/
theorem selPart_succ (y : List Bool) (m : ℕ) (hm : m < nbits M) (hy : m < y.length) :
    Function.update (selPart M y m) ⟨m, hm⟩ (y[m]'hy) = selPart M y (m + 1) := by
  funext j
  by_cases hj : j.val = m
  · have : j = ⟨m, hm⟩ := Fin.ext hj
    subst this
    simp [selPart, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy]
  · rw [Function.update_of_ne (fun h => hj (by rw [h]))]
    simp only [selPart]
    split_ifs <;> first | rfl | omega

/-- **Reading the selector bits**: after `m < nbits` steps on an input of length at
least `m`, the machine has read `m` raw bits.

**Proof sketch.** Induction on `m`: each step reads input bit `m` (in range) and records it
in the selector accumulator (`selPart_succ`). -/
theorem sel_run (y : List Bool) : ∀ m (hm : m < nbits M), m ≤ y.length →
    (tabTM M).tm.runFrom ((tabTM M).tm.initCfg y) m =
      acfg M (some (.sel ⟨m, hm⟩ (selPart M y m))) (fpos y (m + 1)) bl bl bl 0 0 0 [] := by
  intro m
  induction m with
  | zero =>
    intro hm _
    rw [MultiTapeTM.runFrom_zero, init_eq]
    congr
  | succ m ih =>
    intro hm hy
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega) (by omega), acfg_step,
      inputSymbol_fpos _ (by omega) (by omega) rfl]
    have hget : y[m + 1 - 1]? = some (y[m]'(by omega)) := by
      simp [List.getElem?_eq_getElem (show m < y.length by omega)]
    rw [hget]
    simp only [tabTr, dif_pos hm]
    rw [tact_idle_apply, moveInputPos_fpos (by omega)]
    simp only [idle_apply, wr_none, SignType.coe_zero, add_zero, List.append_nil, Option.toList]
    rw [selPart_succ M y m (by omega) (by omega)]

/-- **Selector bits read**: on an input with at least `nbits` symbols, after `nbits`
steps the machine starts reading the first field, with the first `nbits` input bits in
its control.

**Proof sketch.** Run `nbits - 1` steps by `sel_run`, then the last selector bit moves to
the first field state; the accumulated bits are all of `y`'s first `nbits` bits. -/
theorem sel_done (y : List Bool) (h : nbits M ≤ y.length) :
    (tabTM M).tm.runFrom ((tabTM M).tm.initCfg y) (nbits M) =
      acfg M (some (.fA false (fun j => y.getD j false))) (fpos y (nbits M + 1))
        bl bl bl 0 0 0 [] := by
  have hpos : 0 < nbits M := nbitsOf_pos M.State M.k
  set m := nbits M - 1 with hmdef
  have hm : m + 1 = nbits M := by omega
  have hrun : (tabTM M).tm.runFrom ((tabTM M).tm.initCfg y) (nbits M) =
      (tabTM M).tm.runFrom ((tabTM M).tm.initCfg y) (m + 1) := by rw [hm]
  rw [hrun, MultiTapeTM.runFrom_succ_eq_step', sel_run M y m (by omega) (by omega), acfg_step,
    inputSymbol_fpos _ (by omega) (by omega) rfl]
  have hget : y[m + 1 - 1]? = some (y[m]'(by omega)) := by
    simp [List.getElem?_eq_getElem (show m < y.length by omega)]
  rw [hget]
  simp only [tabTr, dif_neg (show ¬ m + 1 < nbits M by omega)]
  rw [tact_idle_apply, moveInputPos_fpos (by omega)]
  simp only [idle_apply, wr_none, SignType.coe_zero, add_zero, List.append_nil, Option.toList]
  rw [selPart_succ M y m (by omega) (by omega), hm]
  congr
  funext j
  simp only [selPart, show j.val < nbits M from j.isLt, if_true]

/-- **A query too short for its selector bits is rejected** within `|y| + 1` steps. -/
theorem sel_reject (y : List Bool) (h : y.length < nbits M) :
    ((tabTM M).tm.runFrom ((tabTM M).tm.initCfg y) (y.length + 1)).state = none ∧
      ((tabTM M).tm.runFrom ((tabTM M).tm.initCfg y) (y.length + 1)).output = [false] := by
  rw [MultiTapeTM.runFrom_succ_eq_step', sel_run M y y.length h le_rfl, acfg_step,
    inputSymbol_fpos _ (by omega) (by omega) rfl]
  have hget : y[y.length + 1 - 1]? = none := by simp
  rw [hget]
  simp only [tabTr, reject]
  rw [tact_idle_apply]
  simp [acfg, tcfg]

/-! ### Reading the fields and copying the input -/

/-- A setup-phase configuration: `M`'s tapes blank, the words `wX`, `wC`, `wO` written
on the auxiliary tapes from cell `0`, each head on the cell after its word. -/
def pcfg {y : List Bool} (st : St M) (p : Fin (y.length + 2)) (wX wC wO : List Bool) :
    Cfg (tabTM M).k Bool (tabTM M).State y :=
  acfg M (some st) p (bufferTape wX) (bufferTape wC) (bufferTape wO) wX.length wC.length
    wO.length []

/-- A setup step reading `inp` at an in-range position. -/
theorem pcfg_step {y : List Bool} (st : St M) (p : ℕ) (h1 : 1 ≤ p) (hp : p ≤ y.length + 1)
    (wX wC wO : List Bool) :
    (tabTM M).tm.step (pcfg M st (fpos y p) wX wC wO) =
      (tabTr M st y[p - 1]? (Fin.addCases (fun _ => none)
        ![bufferTape wX wX.length, bufferTape wC wC.length, bufferTape wO wO.length])).apply
        (pcfg M st (fpos y p) wX wC wO) := by
  rw [pcfg, acfg_step, inputSymbol_fpos _ h1 hp rfl]

/-- The right blank of a stored word. -/
@[simp] theorem bufferTape_length (w : List Bool) : bufferTape w (w.length : ℤ) = none := by
  rw [bufferTape_nat]; simp

/-- Writing at the right blank of a stored word extends it. -/
theorem bufferTape_write (w : List Bool) (b : Bool) :
    Function.update (bufferTape w) (w.length : ℤ) (some b) = bufferTape (w ++ [b]) :=
  (bufferTape_append w b).symm

/-- Rejection on a truncated query, from any field-reading state. -/
theorem pcfg_reject {y : List Bool} (st : St M) (hst : ∀ work, tabTr M st none work = reject M)
    (p : ℕ) (h1 : 1 ≤ p) (hp : p ≤ y.length + 1) (hnone : y[p - 1]? = none)
    (wX wC wO : List Bool) :
    ((tabTM M).tm.step (pcfg M st (fpos y p) wX wC wO)).state = none ∧
      ((tabTM M).tm.step (pcfg M st (fpos y p) wX wC wO)).output = [false] := by
  rw [pcfg_step M st p h1 hp, hnone, hst, reject, pcfg, tact_idle_apply]
  simp [acfg, tcfg]

/-- Reading the first symbol of a pair. -/
theorem pcfg_fA {y : List Bool} (f : Bool) (bits : Fin (nbits M) → Bool) (p : ℕ)
    (h1 : 1 ≤ p) (hp : p ≤ y.length) (b : Bool) (hr : y[p - 1]? = some b)
    (wX wC wO : List Bool) :
    (tabTM M).tm.step (pcfg M (.fA f bits) (fpos y p) wX wC wO) =
      pcfg M (.fB f b bits) (fpos y (p + 1)) wX wC wO := by
  rw [pcfg_step M _ p h1 (by omega), hr]
  simp only [tabTr]
  rw [pcfg, tact_idle_apply, moveInputPos_fpos hp]
  simp [pcfg]

/-- Completing a data pair: its bit is appended to the field's tape. -/
theorem pcfg_fB_true {y : List Bool} (f b : Bool) (bits : Fin (nbits M) → Bool) (p : ℕ)
    (h1 : 1 ≤ p) (hp : p ≤ y.length) (hr : y[p - 1]? = some true)
    (wX wC wO : List Bool) :
    (tabTM M).tm.step (pcfg M (.fB f b bits) (fpos y p) wX wC wO) =
      pcfg M (.fA f bits) (fpos y (p + 1)) wX (if f then wC else wC ++ [b])
        (if f then wO ++ [b] else wO) := by
  rw [pcfg_step M _ p h1 (by omega), hr]
  simp only [tabTr]
  rw [pcfg, tact_idle_apply, moveInputPos_fpos hp]
  cases f
  · simp [pcfg, bufferTape_write]
  · simp [pcfg, bufferTape_write]

/-- Completing an end pair: the field is complete. -/
theorem pcfg_fB_false {y : List Bool} (f b : Bool) (bits : Fin (nbits M) → Bool) (p : ℕ)
    (h1 : 1 ≤ p) (hp : p ≤ y.length) (hr : y[p - 1]? = some false)
    (wX wC wO : List Bool) :
    (tabTM M).tm.step (pcfg M (.fB f b bits) (fpos y p) wX wC wO) =
      pcfg M (if f then .cpy bits else .fA true bits) (fpos y (p + 1)) wX wC wO := by
  rw [pcfg_step M _ p h1 (by omega), hr]
  simp only [tabTr]
  rw [pcfg, tact_idle_apply, moveInputPos_fpos hp]
  simp [pcfg]

end Complexity.Meyer
