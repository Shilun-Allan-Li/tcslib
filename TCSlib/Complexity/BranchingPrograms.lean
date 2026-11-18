/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.BranchingPrograms.Defs
import TCSlib.Complexity.BranchingPrograms.Eval
import TCSlib.Complexity.BranchingPrograms.Barrington
import TCSlib.Complexity.BranchingPrograms.BarringtonConverse
import TCSlib.Complexity.BranchingPrograms.NC1

/-!
# Bounded-width branching programs

Branching programs of bounded width in the general model of [Bar89, §1] (instructions produce
maps `[w] → [w]`; permutation programs are a predicate), the host `BranchingProgram.evalWith`
that runs a program on state vectors (registry row H18), and both directions of Barrington's
results, namely formulas of depth `d` to width-5 permutation programs of length `≤ 4^d`, programs
of length `l` to formulas of depth `O(log l)`, and BWBP = nonuniform NC¹ = PBP₅.

## Contents

- `BranchingPrograms.Defs`: instructions, programs, `yield` in program order, `IsPermutation`,
  `conj`, `complementLast`, families with accepting sets, the classes `InBWBP` and `InPBP`.
- `BranchingPrograms.Eval`: the push-form host `evalWith`, `evalWith_rel`, the Boolean semantics.
- `BranchingPrograms.Barrington`: five-cycle recognition, Lemmas 1–3, the explicit conjugator and
  the computable construction `barrington` (Thm 1).
- `BranchingPrograms.BarringtonConverse`: the composition-tree formula `toFormula` (Thm 2).
- `BranchingPrograms.NC1`: the `DAGCircuit` corollary, NC¹ ⊆ PBP₅, BWBP ⊆ NC¹ and the Corollary.

## References

* [Bar89] D. A. Mix Barrington, *Bounded-width polynomial-size branching programs recognize
  exactly those languages in NC¹*, J. Comput. System Sci. 38(1):150–164, 1989.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
