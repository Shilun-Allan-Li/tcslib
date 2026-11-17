/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.BranchingPrograms.Barrington
import TCSlib.Complexity.BranchingPrograms.BarringtonConverse
import TCSlib.Complexity.CircuitComplexity.NCAC
import TCSlib.Complexity.CircuitComplexity.TreeDAG

/-!
# Bounded-width branching programs and NC¹

The class-level consequences of Barrington's two theorems [Bar89, §3]: the `DAGCircuit` form of
Theorem 1 (length `≤ 4^depth`), NC¹ ⊆ polynomial-length width-5 permutation programs, BWBP ⊆ NC¹
(Theorem 2 for families), and Barrington's Corollary BWBP = nonuniform NC¹ = PBP₅.  The classes
`Language.InBWBP`, `Language.InPBP` are defined in `Defs.lean`; `Language.InNC` is the book's
`DAGCircuit` class (`NCAC.lean`).  Both directions go through the formula class
`Language.InTreeNC 1` (`Language.inNC_one_iff`).

## Main definitions

None: the classes are defined in `Defs.lean`, the constructions in `Barrington.lean` and
`BarringtonConverse.lean`.

## Main results

All are statements of the 6a statement phase (targets admitted with `sorry`).

* `BranchingProgram.exists_fiveCycleRecognizes_of_dagCircuit` — Thm 1 for `DAGCircuit`s (C22).
* `Language.InNC.inPBP_five` — NC¹ ⊆ PBP₅ (C23).
* `Language.InBWBP.inNC_one` — BWBP ⊆ NC¹ (C24).
* `Language.inNC_one_iff_inBWBP`, `Language.inNC_one_iff_inPBP_five` — the Corollary (C25).

## Deviations

* Inputs of length `0` have no variable for Barrington's constants to read (`[NeZero n]`); the
  family statements handle `n = 0` through the accepting set (the empty program yields `id`, and
  `F_0` is `{id}` or `∅` according to whether `[] ∈ L`).
* The circuit of Theorem 2 is a formula (P6-Q18); it reaches `Language.InNC 1` through
  `Language.InTreeNC.inNC`.

## References

* [Bar89] D. A. Mix Barrington, *Bounded-width polynomial-size branching programs recognize
  exactly those languages in NC¹*, J. Comput. System Sci. 38(1):150–164, 1989.
* [BV14] Z. Brakerski, V. Vaikuntanathan, *Lattice-based FHE as secure as PKE*, ITCS 2014,
  pp. 1–12; IACR ePrint 2013/541.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BranchingProgram

open BoolCircuit Equiv

/-- **C22.** **The `DAGCircuit` corollary of Theorem 1**: a fan-in-two circuit `C` on `n ≥ 1`
inputs is five-cycle recognized, with any five-cycle output `σ`, by a width-5 permutation program
of length at most `4 ^ C.depth`:
`∃ B, B.IsPermutation ∧ B.length ≤ 4 ^ C.depth ∧ FiveCycleRecognizes B (fun x => C.eval x = true) σ`
[BV14, Thm 3.5, p014-b001; Bar89, Thm 1, p003-b002].
Deviation: Bar89 and BV14 start from a circuit of AND/OR (BV14: NAND) gates; here the circuit is
unfolded to a formula first (`DAGCircuit.toTree`, depth-preserving), P6-Q2.

**Proof sketch.** Take `B = barrington C.toTree σ`.  From `hC` (`DAGCircuit.isFaninTwo_iff`, and
the reader `DAGCircuit.isWellFormed_iff`, missing at the base and proposed) get
well-formedness and fan-in `≤ 2` of every gate; then `toTree_maxFanin_le` gives
`C.toTree.maxFanin ≤ 2`, `toTree_depth_le` gives `C.toTree.depth ≤ C.depth`, and `toTree_eval`
gives `C.toTree.eval x = C.eval x`.  Conclude by `isPermutation_barrington`,
`barrington_length_le` with `Nat.pow_le_pow_right`, and `barrington_recognizes`. -/
theorem exists_fiveCycleRecognizes_of_dagCircuit {n : ℕ} [NeZero n] (C : DAGCircuit n)
    (hC : C.IsFaninTwo) {σ : Perm (Fin 5)} (hσ : IsFiveCycle σ) :
    ∃ B : BranchingProgram 5 n, B.IsPermutation ∧ B.length ≤ 4 ^ C.depth ∧
      FiveCycleRecognizes B (fun x => C.eval x = true) σ := by
  sorry

end BranchingProgram

open BoolCircuit BranchingProgram

/-- **C23.** **NC¹ ⊆ polynomial-length width-5 permutation programs**: `L.InNC 1 → L.InPBP 5`
[Bar89, Corollary, p004-b004; abstract, p001-b001].
Deviation: inputs of length `0` are handled by the accepting set (Thm 1 needs `n ≥ 1`).

**Proof sketch.** `Language.InNC.inTreeNC_one` gives a fan-in-2 formula family `C` with depth
`≤ b·(log₂ n + 1)`, deciding `L` (read through readers of `Language.InTreeNC`,
`TreeCircuitFamily.HasFaninTwo` and `HasPolylogDepth`, missing at the base and proposed).
Define the family with `program n = barrington (C.circuit n) sigma1` for `n ≥ 1` (`NeZero`
from `n ≠ 0`) and `⟨[]⟩` for `n = 0`; `accept n = {sigma1}` for `n ≥ 1`, and `{id}` or `∅`
at `n = 0` according to `[] ∈ L` (classical).  Permutation: `isPermutation_barrington`
(`BranchingProgramFamily.isPermutation_iff`).
Length: `barrington_length_le` and `4 ^ (b·(log₂ n + 1)) ≤ 4 ^ b · (n + 1) ^ (2b)`
(`Nat.pow_le_pow_right`, `Nat.pow_log_le_self`), so `BranchingProgramFamily.isPolyLength_iff`.
Language: `BranchingProgramFamily.mem_language_iff`, `barrington_recognizes` with
`isFiveCycle_sigma1`, `TreeCircuitFamily.mem_language_iff`; at `n = 0`, `yield_nil`.
Conclude with `Language.inPBP_iff`. -/
theorem Language.InNC.inPBP_five {L : Language Bool} (h : L.InNC 1) : L.InPBP 5 := by
  sorry

/-- **C24.** **BWBP ⊆ NC¹**, Theorem 2 for families: `L.InBWBP → L.InNC 1`
[Bar89, Thm 2, p004-b003; abstract, p001-b001: "any bounded-width polynomial-size branching
program can be simulated by an `NC¹` circuit"].
Deviation: the circuits are fan-in-2 formulas (P6-Q18), compiled to `DAGCircuit`s by
`Language.InTreeNC.inNC`.

**Proof sketch.** From `Language.inBWBP_iff` get `w`, `P` and a length bound `a·(n+1)^k`
(`BranchingProgramFamily.isPolyLength_iff`).  The formula family `n ↦ (P.program n).toFormula
(P.accept n)` decides `P.language` (`toFormula_eval`, `BranchingProgramFamily.mem_language_iff`,
`TreeCircuitFamily.mem_language_iff`), has fan-in 2 (`maxFanin_toFormula_le`), and depth
`≤ (⌈log₂ w⌉ + 2)·⌈log₂ (a(n+1)^k)⌉ + topDepth w ≤ b·(log₂ n + 1)` for a constant `b`
(`depth_toFormula_le`, `Nat.clog_mono_right`, `BoolCircuit.clog_poly_le`); its size is
`≤ 2 ^ (depth + 1)` (`TreeCircuit.size_succ_le_two_pow`), hence polynomial.  This gives
`L.InTreeNC 1` (through the proposed readers of `Language.InTreeNC` and the `TreeCircuitFamily`
predicates, missing at the base), and `Language.InTreeNC.inNC` gives `L.InNC 1`. -/
theorem Language.InBWBP.inNC_one {L : Language Bool} (h : L.InBWBP) : L.InNC 1 := by
  sorry

/-- **C25.** **Barrington's Corollary**, first equality: nonuniform NC¹ is BWBP,
`L.InNC 1 ↔ L.InBWBP` [Bar89, Corollary, p004-b004].

**Proof sketch.** `→`: `Language.InNC.inPBP_five`, then forget permutation-ness and take `w = 5`
(`Language.inPBP_iff`, `Language.inBWBP_iff`).  `←`: `Language.InBWBP.inNC_one`. -/
theorem Language.inNC_one_iff_inBWBP (L : Language Bool) : L.InNC 1 ↔ L.InBWBP := by
  sorry

/-- **C25.** **Barrington's Corollary**, second equality: nonuniform NC¹ is the class of
polynomial-length width-5 permutation programs, `L.InNC 1 ↔ L.InPBP 5`
[Bar89, Corollary, p004-b004].

**Proof sketch.** `→`: `Language.InNC.inPBP_five`.  `←`: a `PBP₅` family is a BWBP family
(`Language.inPBP_iff`, `Language.inBWBP_iff`), then `Language.InBWBP.inNC_one`. -/
theorem Language.inNC_one_iff_inPBP_five (L : Language Bool) : L.InNC 1 ↔ L.InPBP 5 := by
  sorry
