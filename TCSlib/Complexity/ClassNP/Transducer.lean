/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.TuringMachine.Simulation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# One-pass transducers run in linear time

A *one-pass transducer* (a Mealy machine) reads its input once from left to right in a
finite control state, emitting at most one bit per input bit. This file realizes every
such transducer as a work-tape-free Turing machine running in time `|x| + 1`, so its
string function is polynomial-time computable. It is the machine-side tool behind
several reductions of [AB09, ch. 6]: the validator and output-clause stages of
`CKT-SAT ≤p 3SAT` ([AB09, Lem 6.11], `CircuitComplexity/CircuitSatReduction.lean`), the
marker stripping of the Karp–Lipton prefix language, and the field recoding of Meyer's
verifier.

## Main definitions

* `Complexity.transduce` — the string function of a transducer with transition `δ` and
  emission `o`.
* `Complexity.transducerTM` — the machine running it.
* `Complexity.transducerFinalTM` — the machine with a final emission: at the right end it
  also emits one optional bit depending on the state reached.

## Main results

* `Complexity.transduce_nil`, `Complexity.transduce_cons` — the function's case lemmas;
  `Complexity.transduce_of_copy` — a state that copies and is kept gives the identity.
* `Complexity.transducerTM_computes` — the machine computes the transducer's function
  within `|x| + 1` steps.
* `Complexity.polyTimeComputable_transduce` — hence it is in FP.
* `Complexity.transducerFinalTM_computes`, `Complexity.polyTimeComputable_transduce_final` —
  the same for a transducer with a final emission.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the multi-tape machine; §6.1.2, Lemma 6.11.)
-/

namespace Complexity

open Turing

variable {σ : Type}

/-- The string function of a one-pass transducer: from control state `q`, each input
bit `b` emits `o q b` (one bit or nothing) and moves to `δ q b`. -/
def transduce (δ : σ → Bool → σ) (o : σ → Bool → Option Bool) : σ → List Bool → List Bool
  | _, [] => []
  | q, b :: l => (o q b).toList ++ transduce δ o (δ q b) l

/-- A transducer emits nothing on the empty word: `transduce δ o q [] = []`. -/
theorem transduce_nil (δ : σ → Bool → σ) (o : σ → Bool → Option Bool) (q : σ) :
    transduce δ o q [] = [] := rfl

/-- On `b :: l` a transducer emits `o q b` and continues from `δ q b`:
`transduce δ o q (b :: l) = (o q b).toList ++ transduce δ o (δ q b) l`. -/
theorem transduce_cons (δ : σ → Bool → σ) (o : σ → Bool → Option Bool) (q : σ) (b : Bool)
    (l : List Bool) :
    transduce δ o q (b :: l) = (o q b).toList ++ transduce δ o (δ q b) l := rfl

/-- The transducer on a concatenation: run the first part, then the second part from the
state reached. -/
theorem transduce_append (δ : σ → Bool → σ) (o : σ → Bool → Option Bool) (q : σ)
    (l₁ l₂ : List Bool) :
    transduce δ o q (l₁ ++ l₂) =
      transduce δ o q l₁ ++ transduce δ o (l₁.foldl δ q) l₂ := by
  induction l₁ generalizing q with
  | nil => rfl
  | cons b l ih => simp [transduce, ih]

/-- **A copying state copies**: if from the state `q` every bit is emitted unchanged
(`o q b = some b`) and `q` is kept (`δ q b = q`), then the transducer started in `q` is the
identity, `transduce δ o q l = l`.

**Proof sketch.** Induction on `l`, by `Complexity.transduce_nil` and
`Complexity.transduce_cons`. -/
theorem transduce_of_copy (δ : σ → Bool → σ) (o : σ → Bool → Option Bool) (q : σ)
    (hδ : ∀ b, δ q b = q) (ho : ∀ b, o q b = some b) (l : List Bool) :
    transduce δ o q l = l := by
  induction l with
  | nil => exact transduce_nil δ o q
  | cons b l ih =>
    rw [transduce_cons, hδ, ho, ih]
    rfl

/-- The transition table of the transducer machine: on a bit, emit, move right and change
state; on the right blank, halt. -/
def transducerTr (δ : σ → Bool → σ) (o : σ → Bool → Option Bool) :
    σ → Option Bool → (Fin 0 → Option Bool) → Action 0 Bool σ
  | q, some b, _ => ⟨.pos, fun _ => (none, 0), o q b, some (δ q b)⟩
  | _, none, _ => ⟨0, fun _ => (none, 0), none, none⟩

/-- **The transducer machine**: no work tapes, control states `σ`, started in `q₀`. -/
def transducerTM [Fintype σ] [DecidableEq σ] (δ : σ → Bool → σ)
    (o : σ → Bool → Option Bool) (q₀ : σ) : FinTM Bool where
  k := 0
  State := σ
  tm := { q₀ := q₀, tr := transducerTr δ o }

/-- The run of the transducer machine: from state `q` reading the suffix `x.drop i`, it
halts after `|x| - i + 1` steps having appended `transduce δ o q (x.drop i)`.

**Proof sketch.** Induction on the suffix: on a bit the machine emits `o q b` and steps
right (`inputSymbol_at` reads `x[i]`), on the right blank it halts. -/
theorem transducer_run [Fintype σ] [DecidableEq σ] (δ : σ → Bool → σ)
    (o : σ → Bool → Option Bool) (q₀ : σ) (x : List Bool) :
    ∀ (l : List Bool) (q : σ) (cfg : Cfg 0 Bool σ x) (i : ℕ), l = x.drop i → i ≤ x.length →
      cfg.state = some q → cfg.inputPos.val = i + 1 →
      ((transducerTM δ o q₀).tm.runFrom cfg (l.length + 1)).state = none ∧
      ((transducerTM δ o q₀).tm.runFrom cfg (l.length + 1)).output =
        cfg.output ++ transduce δ o q l := by
  intro l
  induction l with
  | nil =>
    intro q cfg i hl hi hq hp
    have hix : i = x.length := by
      have := congrArg List.length hl
      simp at this
      omega
    have hsym : cfg.inputSymbol = none := by
      rw [FinTM.inputSymbol_at cfg i hi hp]; simp [hix]
    simp only [List.length_nil, Nat.zero_add, MultiTapeTM.runFrom_one]
    unfold MultiTapeTM.step
    rw [hq]
    simp only
    rw [hsym]
    simp [transducerTM, transducerTr, transduce]
  | cons b l ih =>
    intro q cfg i hl hi hq hp
    have hlt : i < x.length := by
      by_contra h
      rw [List.drop_eq_nil_of_le (by omega)] at hl
      exact List.cons_ne_nil _ _ hl
    have hb : x[i]? = some b := by
      have := congrArg List.head? hl
      simpa [List.head?_drop] using this.symm
    have hsym : cfg.inputSymbol = some b := by
      rw [FinTM.inputSymbol_at cfg i hi hp, hb]
    have hl' : l = x.drop (i + 1) := by
      have := congrArg List.tail hl
      simpa [List.tail_drop] using this
    rw [List.length_cons, MultiTapeTM.runFrom_succ_eq_step]
    have hstep : (transducerTM δ o q₀).tm.step cfg =
        ⟨some (δ q b), moveInputPos cfg.inputPos .pos, cfg.workTapes,
          fun i => cfg.workTapePos i + 0, cfg.output ++ (o q b).toList⟩ := by
      unfold MultiTapeTM.step
      rw [hq]
      simp only
      rw [hsym]
      simp only [transducerTM, transducerTr, Action.apply]
      congr 1
    have hp' : (moveInputPos cfg.inputPos .pos).val = i + 1 + 1 := by
      rw [moveInputPos_pos_of_ne_right _ (by omega)]
      simp [hp]
    obtain ⟨h1, h2⟩ := ih (δ q b) ((transducerTM δ o q₀).tm.step cfg) (i + 1) hl' (by omega)
      (by rw [hstep]) (by rw [hstep]; exact hp')
    refine ⟨h1, ?_⟩
    rw [h2, hstep]
    simp [transduce]

/-- **The transducer machine computes the transducer's function** within `|x| + 1` steps. -/
theorem transducerTM_computes [Fintype σ] [DecidableEq σ] (δ : σ → Bool → σ)
    (o : σ → Bool → Option Bool) (q₀ : σ) :
    (transducerTM δ o q₀).ComputesFunInTime (transduce δ o q₀) fun n => n + 1 := by
  intro x
  obtain ⟨h1, h2⟩ := transducer_run δ o q₀ x x q₀ ((transducerTM δ o q₀).tm.initCfg x) 0
    (by simp) (by simp) rfl rfl
  exact (FinTM.computesInTime_iff _ _ _ _).mpr ⟨h1, by rw [h2]; rfl⟩

/-- A one-pass transducer computes a polynomial-time function. -/
theorem polyTimeComputable_transduce [Fintype σ] [DecidableEq σ] (δ : σ → Bool → σ)
    (o : σ → Bool → Option Bool) (q₀ : σ) :
    PolyTimeComputable (transduce δ o q₀) :=
  polyTimeComputable_of_linear
    ⟨transducerTM δ o q₀, 1, fun x => by
      simpa only [Nat.one_mul] using transducerTM_computes δ o q₀ x⟩

/-! ### Transducers with a final emission -/

/-- **The transducer machine with a final emission**: as `transducerTM`, but its halting
transition at the right blank also emits `f q` for the control state `q` reached there. -/
def transducerFinalTM [Fintype σ] [DecidableEq σ] (δ : σ → Bool → σ)
    (o : σ → Bool → Option Bool) (f : σ → Option Bool) (q₀ : σ) : FinTM Bool where
  k := 0
  State := σ
  tm := {
    q₀ := q₀
    tr := fun q inp _ => match inp with
      | some b => ⟨.pos, Fin.elim0, o q b, some (δ q b)⟩
      | none => ⟨0, Fin.elim0, f q, none⟩ }

/-- The final-emission machine in state `q` just before input bit `i`, having emitted `out`. -/
private def finalCfg (x : List Bool) (q : σ) (i : ℕ) (hi : i ≤ x.length) (out : List Bool) :
    Cfg 0 Bool σ x :=
  ⟨some q, ⟨i + 1, by omega⟩, Fin.elim0, Fin.elim0, out⟩

/-- Before the right end, one step consumes input bit `i` and appends its emission. -/
private lemma transducerFinalTM_step [Fintype σ] [DecidableEq σ] (δ : σ → Bool → σ)
    (o : σ → Bool → Option Bool) (f : σ → Option Bool) (q₀ : σ)
    (x : List Bool) (q : σ) (i : ℕ) (hi : i < x.length) (out : List Bool) :
    (transducerFinalTM δ o f q₀).tm.step (finalCfg x q i hi.le out) =
      finalCfg x (δ q x[i]) (i + 1) hi (out ++ (o q x[i]).toList) := by
  have hin : (finalCfg x q i hi.le out).inputSymbol = some x[i] := by
    rw [FinTM.inputSymbol_at _ i hi.le rfl, List.getElem?_eq_getElem hi]
  rw [MultiTapeTM.step_of_some (q := q) rfl, hin]
  apply Cfg.ext_zero_tapes
  · rw [Action.apply_state]; rfl
  · rw [Action.apply_inputPos]
    exact moveInputPos_pos_of_ne_right _ (show i + 1 ≠ x.length + 1 by omega)
  · rw [Action.apply_output]; rfl

/-- At the right end, one step halts and appends the final emission. -/
private lemma transducerFinalTM_step_end [Fintype σ] [DecidableEq σ] (δ : σ → Bool → σ)
    (o : σ → Bool → Option Bool) (f : σ → Option Bool) (q₀ : σ)
    (x : List Bool) (q : σ) (i : ℕ) (hi : i ≤ x.length) (he : i = x.length) (out : List Bool) :
    ((transducerFinalTM δ o f q₀).tm.step (finalCfg x q i hi out)).state = none ∧
      ((transducerFinalTM δ o f q₀).tm.step (finalCfg x q i hi out)).output =
        out ++ (f q).toList := by
  have hin : (finalCfg x q i hi out).inputSymbol = none := by
    rw [FinTM.inputSymbol_at _ i hi rfl, List.getElem?_eq_none (by omega)]
  rw [MultiTapeTM.step_of_some (q := q) rfl, hin, Action.apply_state, Action.apply_output]
  exact ⟨rfl, rfl⟩

/-- From bit `|pre|` of `x = pre ++ rest` in state `q`, the final-emission machine halts after
`|rest| + 1` steps, having appended `transduce δ o q rest` and then `f (rest.foldl δ q)`.

**Proof sketch.** Induction on the unread suffix: an input bit is one step appending its
emission (`transducerFinalTM_step`); the right blank is the halting step appending the final
emission (`transducerFinalTM_step_end`). -/
private lemma transducerFinalTM_run [Fintype σ] [DecidableEq σ] (δ : σ → Bool → σ)
    (o : σ → Bool → Option Bool) (f : σ → Option Bool) (q₀ : σ) (x rest : List Bool) :
    ∀ pre (hx : x = pre ++ rest) q out,
      ((transducerFinalTM δ o f q₀).tm.runFrom
        (finalCfg x q pre.length (by simp [hx]) out) (rest.length + 1)).state = none ∧
      ((transducerFinalTM δ o f q₀).tm.runFrom
        (finalCfg x q pre.length (by simp [hx]) out) (rest.length + 1)).output =
          out ++ (transduce δ o q rest ++ (f (rest.foldl δ q)).toList) := by
  induction rest with
  | nil =>
    intro pre hx q out
    simp only [List.length_nil, Nat.zero_add, MultiTapeTM.runFrom_one, transduce_nil,
      List.nil_append, List.foldl_nil]
    exact transducerFinalTM_step_end δ o f q₀ x q pre.length _ (by simp [hx]) out
  | cons b rest ih =>
    intro pre hx q out
    have hi : pre.length < x.length := by simp [hx]
    have hb : x[pre.length] = b := by simp [hx]
    have hs := transducerFinalTM_step δ o f q₀ x q pre.length hi out
    rw [hb] at hs
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, transduce_cons, List.foldl_cons]
    simpa only [List.length_append, List.length_singleton, List.append_assoc] using
      ih (pre ++ [b]) (by simpa [List.append_assoc] using hx) (δ q b) (out ++ (o q b).toList)

/-- **The final-emission machine computes its function** within `|x| + 1` steps: it outputs
`transduce δ o q₀ x` followed by the final emission `f` of the state `x.foldl δ q₀` reached at
the right end.

**Proof sketch.** The initial configuration is the machine's configuration before bit `0`
with empty output; the run lemma over the whole input gives the halt and the output. -/
theorem transducerFinalTM_computes [Fintype σ] [DecidableEq σ] (δ : σ → Bool → σ)
    (o : σ → Bool → Option Bool) (f : σ → Option Bool) (q₀ : σ) :
    (transducerFinalTM δ o f q₀).ComputesFunInTime
      (fun x => transduce δ o q₀ x ++ (f (x.foldl δ q₀)).toList) fun n => n + 1 := by
  refine (FinTM.computesFunInTime_iff _ _ _).mpr fun x => ?_
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  have hi : (transducerFinalTM δ o f q₀).tm.initCfg x = finalCfg x q₀ 0 (Nat.zero_le _) [] := by
    rw [MultiTapeTM.initCfg_eq]
    apply Cfg.ext_zero_tapes
    · rw [Cfg.init_state]; rfl
    · rw [Cfg.init_inputPos]; rfl
    · rw [Cfg.init_output]; rfl
  rw [hi]
  simpa only [List.length_nil, List.nil_append] using
    transducerFinalTM_run δ o f q₀ x x [] (by simp) q₀ []

/-- A one-pass transducer with a final emission computes a polynomial-time function:
`x ↦ transduce δ o q₀ x ++ (f (x.foldl δ q₀)).toList` is in FP. -/
theorem polyTimeComputable_transduce_final [Fintype σ] [DecidableEq σ] (δ : σ → Bool → σ)
    (o : σ → Bool → Option Bool) (f : σ → Option Bool) (q₀ : σ) :
    PolyTimeComputable (fun x => transduce δ o q₀ x ++ (f (x.foldl δ q₀)).toList) :=
  polyTimeComputable_of_linear ⟨transducerFinalTM δ o f q₀, 1, by
    simpa only [Nat.one_mul] using transducerFinalTM_computes δ o f q₀⟩

end Complexity
