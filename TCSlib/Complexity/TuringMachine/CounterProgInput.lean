/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.TuringMachine.CounterProgRun

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Shifting the input of a counter program

Counter programs read their input from left to right. Once a prefix has been consumed,
executing on the remaining suffix is equivalent to executing on the original input with
the input position shifted by the prefix length.

## Main definitions

* `Complexity.CounterProg.shiftInput` shifts an abstract state's input position.

## Main results

* `Complexity.CounterProg.run_shiftInput` transports a run from a suffix to a prefixed input.
* `Complexity.CounterProg.Goes.prepend_input` transports the bounded run relation.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: the machine model.)

The lemmas below are technical facts about the counter-program implementation, rather
than additional textbook claims.
-/

namespace Complexity.CounterProg

variable {R : ℕ} {Λ : Type}

/-- Shift only the input position of an abstract state by `n`. -/
def shiftInput (n : ℕ) (s : St R Λ) : St R Λ :=
  { s with pos := n + s.pos }

/-- Indexing after a prefix reads the corresponding symbol of the suffix. -/
theorem getElem?_append_length_add (prefix suffix : List Bool) (p : ℕ) :
    (prefix ++ suffix)[prefix.length + p]? = suffix[p]? := by
  rw [List.getElem?_append_right (Nat.le_add_right _ _)]
  simp

/-- A program step after a consumed prefix is the corresponding suffix step with its
input position shifted. -/
theorem step_shiftInput (P : Λ → Instr R Λ) (prefix suffix : List Bool) (s : St R Λ) :
    step P (prefix ++ suffix) (shiftInput prefix.length s) =
      shiftInput prefix.length (step P suffix s) := by
  rcases s with ⟨lbl, ρ, p, o⟩
  cases lbl with
  | none => rfl
  | some l =>
    cases hP : P l <;> simp only [step, shiftInput, hP]
    all_goals try rfl
    rw [getElem?_append_length_add]
    cases hread : suffix[p]? with
    | none => rfl
    | some b => cases b <;> simp [shiftInput, Nat.add_assoc]

/-- A run after a consumed prefix is the corresponding suffix run with its input
position shifted.

**Proof sketch.** Induct on the number of steps, using the one-step input-shift identity. -/
theorem run_shiftInput (P : Λ → Instr R Λ) (prefix suffix : List Bool)
    (s : St R Λ) (t : ℕ) :
    run P (prefix ++ suffix) (shiftInput prefix.length s) t =
      shiftInput prefix.length (run P suffix s t) := by
  induction t generalizing s with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, step_shiftInput, ih, run_succ]

/-- A bounded suffix run remains valid after prepending input already consumed; its
initial and final input positions both increase by the prefix length. -/
theorem Goes.prepend_input {P : Λ → Instr R Λ} {suffix : List Bool} {l : Λ}
    {l' : Option Λ} {ρ ρ' : Fin R → ℕ} {p p' : ℕ} {e : List Bool} {b : ℕ}
    (h : Goes P suffix l ρ p l' ρ' p' e b) (prefix : List Bool) :
    Goes P (prefix ++ suffix) l ρ (prefix.length + p) l' ρ' (prefix.length + p') e b := by
  intro o
  obtain ⟨t, ht, hrun⟩ := h o
  refine ⟨t, ht, ?_⟩
  change run P (prefix ++ suffix) (shiftInput prefix.length ⟨some l, ρ, p, o⟩) t =
    shiftInput prefix.length ⟨l', ρ', p', o ++ e⟩
  rw [run_shiftInput, hrun]

end Complexity.CounterProg
