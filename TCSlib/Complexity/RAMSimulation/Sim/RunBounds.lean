/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.RAMSimulation.Sim.RunCosts
import TCSlib.Complexity.RAMSimulation.WordSize

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Absorbing the simulation's fixed coefficients

The finite setup supplies fixed startup and instruction coefficients and a fixed number of
tapes. One constant absorbs those coefficients into the stated time and space polynomials.
The word-size computation's time and space retain coefficient one.

## Main definitions

* `WordRAM.Sim.RunSetup.boundCost`: one coefficient for both final bounds.

## Main results

* `WordRAM.Sim.RunSetup.time_total_le`: startup and the instruction blocks fit the time bound.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Exercise 1.9; Definition 4.1.)
-/

namespace WordRAM.Sim.RunSetup

variable {P : XProgram} {fn : Bool} {Mw : Turing.FinTM Bool} (A : RunSetup P fn Mw)

/-- A program-dependent coefficient large enough for startup, phases and visited intervals. -/
def boundCost : ℕ :=
  A.startCost + 3 * A.phaseCost + (8 + A.extraTapes) * (6 * A.phaseCost + 1) + 3

/-- The final coefficient is its explicit expression in the fixed setup costs. -/
theorem boundCost_eq : A.boundCost =
    A.startCost + 3 * A.phaseCost + (8 + A.extraTapes) * (6 * A.phaseCost + 1) + 3 := rfl

/-- Startup, its dispatch and fewer than `t` ordinary instruction blocks fit the final
simulation time polynomial when the table contains at most `f+1` cells.

**Proof sketch.** A natural word width satisfies `W ≤ W²`. Thus replacing the table size by
`f+1` bounds each raw phase polynomial by three times the target polynomial. Its dispatch
cost is absorbed by the target polynomial's constant term. Multiply by at most `t` blocks,
add startup and its dispatch, and use the fixed coefficient `boundCost`. -/
theorem time_total_le (n W tw t f m steps : ℕ) (hm : m ≤ f + 1) (hs : steps < t) :
    tw + A.startCost * (n + W ^ 2 + 1) + 1 +
        (steps + 1) * A.blockTime n W m ≤
      tw + A.boundCost * (t + 1) * (f * (W + 1) + W ^ 2 + n + 1) := by
  let Q := f * (W + 1) + W ^ 2 + n + 1
  have hQ : 1 ≤ Q := by dsimp only [Q]; omega
  have hW : W ≤ W ^ 2 := by
    cases W with
    | zero => decide
    | succ W => nlinarith
  have hraw : (m + 1) * (W + 1) + W ^ 2 + n + 1 ≤ 3 * Q := by
    dsimp only [Q]
    nlinarith [Nat.mul_le_mul_right (W + 1) (Nat.succ_le_succ hm)]
  have hb : A.blockTime n W m ≤ (3 * A.phaseCost + 1) * Q := by
    rw [blockTime_eq]
    nlinarith [Nat.mul_le_mul_left A.phaseCost hraw]
  have hblocks : (steps + 1) * A.blockTime n W m ≤ t * ((3 * A.phaseCost + 1) * Q) :=
    Nat.mul_le_mul (Nat.succ_le_iff.mpr hs) hb
  have hstart : A.startCost * (n + W ^ 2 + 1) ≤ A.startCost * Q :=
    Nat.mul_le_mul_left _ (by dsimp only [Q]; omega)
  have hcost : A.startCost + 3 * A.phaseCost + 2 ≤ A.boundCost := by
    rw [boundCost_eq]; omega
  have hcoef : A.startCost + 1 + t * (3 * A.phaseCost + 1) ≤ A.boundCost * (t + 1) := by
    nlinarith [Nat.mul_le_mul_right (t + 1) hcost]
  calc
    _ ≤ tw + A.startCost * Q + Q + t * ((3 * A.phaseCost + 1) * Q) := by omega
    _ = tw + (A.startCost + 1 + t * (3 * A.phaseCost + 1)) * Q := by ring
    _ ≤ tw + (A.boundCost * (t + 1)) * Q := Nat.add_le_add_left (Nat.mul_le_mul_right Q hcoef) tw

/-- Startup space and one interval of the common phase radius on each tape fit the final
simulation space polynomial. The initial space `sw` is added only once.

**Proof sketch.** `length_bits_le_log` bounds the binary input length by `logSpace`.
With at most `f+1` table cells the phase radius is at most three times the phase coefficient
times the target space polynomial. Each tape adds at most twice that radius plus one cell.
The expression `boundCost` absorbs these intervals and startup's additional space. -/
theorem space_total_le (n W sw f m : ℕ) (hm : m ≤ f + 1) :
    sw + A.startCost * (W + (Nat.bits n).length + 1) +
        (8 + A.extraTapes) * (2 * A.blockRadius n W m + 1) ≤
      sw + A.boundCost * (f * (W + 1) + W + Complexity.logSpace n + 1) := by
  let Q := f * (W + 1) + W + Complexity.logSpace n + 1
  have hQ : 1 ≤ Q := by dsimp only [Q]; omega
  have hbits : (Nat.bits n).length ≤ Complexity.logSpace n := by
    rw [Complexity.logSpace_eq]
    exact Complexity.LogProg.length_bits_le_log n
  have hraw : (m + 1) * (W + 1) + (Nat.bits n).length + 1 ≤ 3 * Q := by
    dsimp only [Q]
    nlinarith [Nat.mul_le_mul_right (W + 1) (Nat.succ_le_succ hm)]
  have hr : A.blockRadius n W m ≤ 3 * A.phaseCost * Q := by
    rw [blockRadius_eq]
    nlinarith [Nat.mul_le_mul_left A.phaseCost hraw]
  have hi : 2 * A.blockRadius n W m + 1 ≤ (6 * A.phaseCost + 1) * Q := by nlinarith
  have hstart : A.startCost * (W + (Nat.bits n).length + 1) ≤ A.startCost * Q :=
    Nat.mul_le_mul_left _ (by dsimp only [Q]; omega)
  have hcost : A.startCost + (8 + A.extraTapes) * (6 * A.phaseCost + 1) ≤ A.boundCost := by
    rw [boundCost_eq]; omega
  calc
    _ ≤ sw + A.startCost * Q + (8 + A.extraTapes) * ((6 * A.phaseCost + 1) * Q) :=
      Nat.add_le_add (Nat.add_le_add_left hstart sw) (Nat.mul_le_mul_left _ hi)
    _ = sw + (A.startCost + (8 + A.extraTapes) * (6 * A.phaseCost + 1)) * Q := by ring
    _ ≤ sw + A.boundCost * Q := Nat.add_le_add_left (Nat.mul_le_mul_right Q hcost) sw

end WordRAM.Sim.RunSetup
