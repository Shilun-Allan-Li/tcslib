/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.Ring
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.TuringMachine.CounterProgRun

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Counter programs in polynomial time

A counter program (`TCSlib.Complexity.TuringMachine.CounterProg`) that halts within
polynomially many abstract steps computes a polynomial-time function: its compiled
machine simulates `t` abstract steps within `t (2t + 3)` machine steps
(`Complexity.CounterProg.exists_tm`). This is how the emitters of [AB09, Remark 6.7] are
shown to run in polynomial time.

## Main results

* `Complexity.CounterProg.polyTimeComputable` — polynomially many abstract steps give a
  polynomial-time computable function.
* `Complexity.CounterProg.polyTimeComputable_of_goes` — the same, in the `Goes` form.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.2, Remark 6.7.)
-/

namespace Complexity

namespace CounterProg

variable {R : ℕ} {Λ : Type}

section SimRun

variable (P : Λ → Instr R Λ) [Fintype Λ] [DecidableEq Λ] (l₀ : Λ)

/-- **Counter programs running in polynomially many steps compute polynomial-time
functions**: if on every input `x` the program halts within `C (|x| + 1)^c` abstract steps
with output `f x`, then `f` is polynomial-time computable.

**Proof sketch.** `exists_tm` gives the machine, within `t (2t + 3) ≤ (2C² + 3C) (n + 1)^{2c}`
steps. -/
theorem polyTimeComputable (f : List Bool → List Bool) (C c : ℕ)
    (h : ∀ x : List Bool, ∃ t ≤ C * (x.length + 1) ^ c,
      (run P x (init l₀) t).lbl = none ∧ (run P x (init l₀) t).out = f x) :
    PolyTimeComputable f := by
  refine ⟨toTM P l₀, 2 * C * C + 3 * C, 2 * c, fun x => ?_⟩
  obtain ⟨t, ht, hl, ho⟩ := h x
  have hM := exists_tm P l₀ x t hl
  rw [ho] at hM
  refine hM.mono ?_
  show t * (2 * t + 3) ≤ (2 * C * C + 3 * C) * (x.length + 1) ^ (2 * c)
  set N := (x.length + 1) ^ c
  have hN : (x.length + 1) ^ (2 * c) = N * N := by rw [← pow_add]; ring_nf
  have h1 : 1 ≤ N := Nat.one_le_pow _ _ (by omega)
  rw [hN]
  calc t * (2 * t + 3) ≤ (C * N) * (2 * (C * N) + 3 * N) := by
        apply Nat.mul_le_mul ht; nlinarith
    _ = (2 * C * C + 3 * C) * (N * N) := by ring

end SimRun

/-! ## Halting programs are polynomial-time -/

variable [Fintype Λ] [DecidableEq Λ]

/-- **A counter program that halts within polynomially many steps computes a
polynomial-time function**: if from the start label with all registers `0` the program
halts on every `x` within `C (|x| + 1)^c` steps printing `f x`, then `f` is in FP.
(`polyTimeComputable` in the `Goes` form.) -/
theorem polyTimeComputable_of_goes (P : Λ → Instr R Λ) (l₀ : Λ) (f : List Bool → List Bool)
    (C c : ℕ) (h : ∀ x : List Bool, ∃ (ρ : Fin R → ℕ) (p : ℕ),
      Goes P x l₀ (fun _ => 0) 0 none ρ p (f x) (C * (x.length + 1) ^ c)) :
    PolyTimeComputable f := by
  refine polyTimeComputable P l₀ f C c fun x => ?_
  obtain ⟨ρ, p, hg⟩ := h x
  obtain ⟨t, ht, hrun⟩ := hg []
  exact ⟨t, ht, by simp [init, hrun], by simp [init, hrun]⟩

end CounterProg

end Complexity
