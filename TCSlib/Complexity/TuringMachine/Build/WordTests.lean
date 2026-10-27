/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine-construction library: linear-time word tests

Two Boolean deciders in linear time, as one-bit outputs `[decide (…)]`, the form the timed
conditional `Turing.FinTM.computesFunInTime_cond` takes as its test:
* **equality with a fixed word** (`Turing.FinTM.computesFunInTime_decideEq`), the one-bit reading
  of the fixed-word comparison `Turing.FinTM.computesFunInTime_ifEq`;
* **the all-`true` word** (`Turing.FinTM.computesFunInTime_allTrue`), from the fixed-width
  increment `Turing.FinTM.computesFunInTime_incFixed`, which fails exactly on that word: its
  output is then empty, and only then.

Two facts about the increment's output support the second: a successful increment is never empty
(`Turing.incFixed_ne_some_nil`), so the output with the empty default is empty exactly on the
all-`true` word (`Turing.incFixed_getD_eq_nil_iff`), the overflow criterion
`Turing.incFixed_eq_none_iff_replicate` in that form.

## Main results

* `Turing.incFixed_ne_some_nil`, `Turing.incFixed_getD_eq_nil_iff` — the increment's output.
* `Turing.FinTM.computesFunInTime_decideEq` — equality with a fixed word, in linear time.
* `Turing.FinTM.computesFunInTime_allTrue` — the all-`true` test, in linear time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2: Turing machines computing functions in time.)
-/

namespace Turing

/-- **A successful increment is never empty**: `incFixed w ≠ some []`, since a successful
increment keeps the width and the empty word overflows.

**Proof sketch.** A successful increment of `w` has `w`'s length (`incFixed_length`), so an empty
result forces `w = []`, which overflows (`incFixed_nil`). -/
theorem incFixed_ne_some_nil (w : List Bool) : incFixed w ≠ some [] := by
  intro h
  have hlen := incFixed_length h
  rw [List.length_nil] at hlen
  have hw : w = [] := List.length_eq_zero_iff.mp hlen.symm
  subst hw
  rw [incFixed_nil] at h
  cases h

/-- **The overflow criterion with the empty default**: the increment's output, read with the
empty word as its default, is empty exactly on the all-`true` word (the empty word included).

**Proof sketch.** On overflow the default is read, and overflow is the all-`true` word
(`incFixed_eq_none_iff_replicate`); a successful increment is never empty
(`incFixed_ne_some_nil`). -/
theorem incFixed_getD_eq_nil_iff (w : List Bool) :
    (incFixed w).getD [] = [] ↔ w = List.replicate w.length true := by
  rw [← incFixed_eq_none_iff_replicate]
  cases hi : incFixed w with
  | none => simp only [Option.getD_none]
  | some y =>
    simp only [Option.getD_some]
    constructor
    · intro hy
      subst hy
      exact absurd hi (incFixed_ne_some_nil w)
    · intro h
      cases h

namespace FinTM

/-- **Equality with a fixed word, in linear time** [AB09, §1.2]: for every fixed word `w` one
machine outputs `[true]` on `w` and `[false]` elsewhere, within `c · (n + 1)`.

**Proof sketch.** The fixed-word comparison `computesFunInTime_ifEq w [true] [false]`, whose
output `if x = w then [true] else [false]` is `[decide (x = w)]`. -/
theorem computesFunInTime_decideEq (w : List Bool) :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => [decide (x = w)]) fun n => c * (n + 1) := by
  obtain ⟨E, a, hE⟩ := computesFunInTime_ifEq w [true] [false]
  refine ⟨E, a, ?_⟩
  convert hE using 1
  funext x
  by_cases hx : x = w <;> simp only [hx, if_true, if_false, decide_true, decide_false]

/-- **The all-`true` test, in linear time** [AB09, §1.2]: one machine outputs `[true]` on the
all-`true` words (the empty word included) and `[false]` elsewhere, within `c · (n + 1)`.

**Proof sketch.** Compose the fixed-width increment (`computesFunInTime_incFixed`, its output read
with the empty default) with the test for the empty word (`computesFunInTime_decideEq []`); the
increment's output is at most as long as its input, so the composite stays linear. By
`incFixed_getD_eq_nil_iff` the composite's bit is the all-`true` test. -/
theorem computesFunInTime_allTrue :
    ∃ (M : FinTM Bool) (c : ℕ),
      M.ComputesFunInTime (fun x => [decide (x = List.replicate x.length true)])
        fun n => c * (n + 1) := by
  obtain ⟨I, a, hI⟩ := computesFunInTime_incFixed
  obtain ⟨E, b, hE⟩ := computesFunInTime_ifEq [] [true] [false]
  obtain ⟨U, c, hU⟩ := computesFunInTime_comp hI hE
    (fun _ _ h => Nat.mul_le_mul_left b (Nat.add_le_add_right h 1))
  refine ⟨U, c * (a + b * a + b + 1), (computesFunInTime_iff _ _ _).mpr ?_⟩
  intro x
  have hx := (computesFunInTime_iff _ _ _).mp hU x
  have hout : (if (incFixed x).getD [] = [] then [true] else [false]) =
      [decide (x = List.replicate x.length true)] := by
    simp only [incFixed_getD_eq_nil_iff x]
    by_cases he : x = List.replicate x.length true
    · simp only [if_pos he, decide_eq_true he]
    · simp only [if_neg he, decide_eq_false he]
  simp only [Function.comp_apply, hout] at hx
  apply hx.mono
  calc
    _ ≤ c * ((a + b * a + b + 1) * (x.length + 1)) := by
      apply Nat.mul_le_mul_left
      have h1 : b ≤ b * (x.length + 1) := Nat.le_mul_of_pos_right b (Nat.succ_pos _)
      have e1 : a * (x.length + 1) + b * (a * (x.length + 1) + 1) + 1 =
          (a * (x.length + 1) + b * a * (x.length + 1)) + (b + 1) := by ring
      have e2 : (a + b * a + b + 1) * (x.length + 1) =
          (a * (x.length + 1) + b * a * (x.length + 1)) + (b * (x.length + 1) + (x.length + 1)) := by
        ring
      rw [e1, e2]
      exact Nat.add_le_add_left (Nat.add_le_add h1 (by omega)) _
    _ = _ := by ring

end FinTM

end Turing
