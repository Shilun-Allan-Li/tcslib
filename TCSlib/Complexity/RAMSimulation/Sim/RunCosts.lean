/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.RunHost

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uniform phase costs for the RAM host

The finite program has one maximum phase coefficient. The induction uses it with the final
table's cell bound, so its time grows with the number of phases while its head envelope does
not. Startup is counted separately to retain its leading witness costs.

## Main definitions

* `WordRAM.Sim.RunSetup.phaseCost`: the maximum instruction-phase coefficient.
* `WordRAM.Sim.RunSetup.blockTime`, `WordRAM.Sim.RunSetup.blockRadius`: one uniform phase
  bound, including its possible dispatch.

## Main results

* `WordRAM.Sim.RunSetup.phase_cost_le`: each phase's coefficient is at most the maximum.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; Definition 4.1.)
-/

namespace WordRAM.Sim.RunSetup

variable {P : XProgram} {fn : Bool} {Mw : Turing.FinTM Bool} (A : RunSetup P fn Mw)

/-- The largest resource coefficient among the program's finitely many instruction phases. -/
def phaseCost : ℕ := Finset.univ.sup (fun p : Fin (P.length + 1) => (A.phases p).cost)

/-- The maximum phase coefficient is the finite supremum of the individual coefficients. -/
theorem phaseCost_eq : A.phaseCost =
    Finset.univ.sup (fun p : Fin (P.length + 1) => (A.phases p).cost) := rfl

/-- Every individual instruction coefficient is bounded by the fixed maximum. -/
theorem phase_cost_le (p : Fin (P.length + 1)) : (A.phases p).cost ≤ A.phaseCost := by
  rw [phaseCost_eq]
  exact Finset.le_sup (f := fun q : Fin (P.length + 1) => (A.phases q).cost) (Finset.mem_univ p)

/-- Time for one phase over a table whose cell set has size `m`, plus one possible dispatch. -/
def blockTime (n W m : ℕ) : ℕ :=
  A.phaseCost * ((m + 1) * (W + 1) + W ^ 2 + n + 1) + 1

/-- The uniform phase time, as its explicit polynomial. -/
theorem blockTime_eq (n W m : ℕ) : A.blockTime n W m =
    A.phaseCost * ((m + 1) * (W + 1) + W ^ 2 + n + 1) + 1 := rfl

/-- Head radius for a phase over a table whose cell set has size `m`. -/
def blockRadius (n W m : ℕ) : ℕ :=
  A.phaseCost * ((m + 1) * (W + 1) + (Nat.bits n).length + 1)

/-- The uniform phase radius, as its explicit polynomial. -/
theorem blockRadius_eq (n W m : ℕ) : A.blockRadius n W m =
    A.phaseCost * ((m + 1) * (W + 1) + (Nat.bits n).length + 1) := rfl

/-- A phase's time bound, with one dispatch, is at most the common block-time bound. -/
theorem phase_time_le (p : Fin (P.length + 1)) (n W m : ℕ) :
    (A.phases p).cost * ((m + 1) * (W + 1) + W ^ 2 + n + 1) + 1 ≤ A.blockTime n W m :=
  Nat.add_le_add_right (Nat.mul_le_mul_right _ (A.phase_cost_le p)) 1

/-- A phase's radius is at most the common block radius. -/
theorem phase_radius_le (p : Fin (P.length + 1)) (n W m : ℕ) :
    (A.phases p).cost * ((m + 1) * (W + 1) + (Nat.bits n).length + 1) ≤ A.blockRadius n W m :=
  Nat.mul_le_mul_right _ (A.phase_cost_le p)

/-- Increasing the table's cell bound can only increase the uniform block-time bound. -/
theorem blockTime_mono (n W : ℕ) {m m' : ℕ} (hm : m ≤ m') :
    A.blockTime n W m ≤ A.blockTime n W m' := by
  rw [blockTime_eq, blockTime_eq]
  have h : (m + 1) * (W + 1) ≤ (m' + 1) * (W + 1) :=
    Nat.mul_le_mul_right _ (Nat.succ_le_succ hm)
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _
    (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right h (W ^ 2)) n) 1)) 1

/-- Increasing the table's cell bound can only increase the common head radius. -/
theorem blockRadius_mono (n W : ℕ) {m m' : ℕ} (hm : m ≤ m') :
    A.blockRadius n W m ≤ A.blockRadius n W m' := by
  rw [blockRadius_eq, blockRadius_eq]
  have h : (m + 1) * (W + 1) ≤ (m' + 1) * (W + 1) :=
    Nat.mul_le_mul_right _ (Nat.succ_le_succ hm)
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right
    (Nat.add_le_add_right h (Nat.bits n).length) 1)

end WordRAM.Sim.RunSetup
