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

## Main results

* `Complexity.transducerTM_computes` — the machine computes the transducer's function
  within `|x| + 1` steps.
* `Complexity.polyTimeComputable_transduce` — hence it is in FP.

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

/-- The transducer on a concatenation: run the first part, then the second part from the
state reached. -/
theorem transduce_append (δ : σ → Bool → σ) (o : σ → Bool → Option Bool) (q : σ)
    (l₁ l₂ : List Bool) :
    transduce δ o q (l₁ ++ l₂) =
      transduce δ o q l₁ ++ transduce δ o (l₁.foldl δ q) l₂ := by
  induction l₁ generalizing q with
  | nil => rfl
  | cons b l ih => simp [transduce, ih]

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
    simp only [List.length_nil, Nat.zero_add, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero]
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

end Complexity
