/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A timed computation bounds every work head

The coarse head envelope follows from a completed computation: before its
time bound every head is within that many cells of its initial position;
afterward the halted run is constant. This is the native-initial-configuration
version of the clean-module envelope, stated without a clean seam hypothesis.

## Main results

* `Complexity.SeedMajority.envelope_of_computesInTime`: the all-times head bound.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009, §1.2, multitape machines.
-/

namespace Complexity.SeedMajority

open Turing

/-- A finite machine computing `y` on `x` by time `t` keeps each work head
within `t` cells at every time `v`:
`|(M.tm.runFrom (M.tm.initCfg x) v).workTapePos j| ≤ (t : ℤ)`.
[AB09, §1.2]

**Proof sketch.** The published interval bound puts the head within `u`
cells of its start after `u ≤ t` steps, and `Cfg.init_workTapePos` makes the
start zero. For `v > t`, the computation reader says the configuration at
`t` is halted; split the run there and use `runFrom_of_halt`. -/
theorem envelope_of_computesInTime {M : FinTM Bool} {x y : List Bool} {t : ℕ}
    (h : M.ComputesInTime x y t) (v : ℕ) (j : Fin M.k) :
    |(M.tm.runFrom (M.tm.initCfg x) v).workTapePos j| ≤ (t : ℤ) := by
  have bound (u : ℕ) (hu : u ≤ t) :
      |(M.tm.runFrom (M.tm.initCfg x) u).workTapePos j| ≤ (t : ℤ) := by
    have hp := M.tm.workTapePos_runFrom_mem_Icc (M.tm.initCfg x) u j
    rw [Finset.mem_Icc] at hp
    simp only [MultiTapeTM.initCfg_eq, Cfg.init_workTapePos, zero_sub, zero_add] at hp
    have hut : (u : ℤ) ≤ t := by exact_mod_cast hu
    rw [MultiTapeTM.initCfg_eq]
    exact abs_le.mpr ⟨by omega, by omega⟩
  by_cases hv : v ≤ t
  · exact bound v hv
  · have hh := ((FinTM.computesInTime_iff M x y t).mp h).1
    have heq : M.tm.runFrom (M.tm.initCfg x) v = M.tm.runFrom (M.tm.initCfg x) t := by
      rw [show v = t + (v - t) by omega, MultiTapeTM.runFrom_add,
        MultiTapeTM.runFrom_of_halt _ hh]
    rw [heq]
    exact bound t le_rfl

end Complexity.SeedMajority
