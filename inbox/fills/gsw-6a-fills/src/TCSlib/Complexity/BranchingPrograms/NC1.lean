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

All are statements of the 6a statement phase, proved in the fill phase (gsw-6a-fills).

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
the reader `DAGCircuit.isWellFormed_iff`) get
well-formedness and fan-in `≤ 2` of every gate; then `toTree_maxFanin_le` gives
`C.toTree.maxFanin ≤ 2`, `toTree_depth_le` gives `C.toTree.depth ≤ C.depth`, and `toTree_eval`
gives `C.toTree.eval x = C.eval x`.  Conclude by `isPermutation_barrington`,
`barrington_length_le` with `Nat.pow_le_pow_right`, and `barrington_recognizes`. -/
theorem exists_fiveCycleRecognizes_of_dagCircuit {n : ℕ} [NeZero n] (C : DAGCircuit n)
    (hC : C.IsFaninTwo) {σ : Perm (Fin 5)} (hσ : IsFiveCycle σ) :
    ∃ B : BranchingProgram 5 n, B.IsPermutation ∧ B.length ≤ 4 ^ C.depth ∧
      FiveCycleRecognizes B (fun x => C.eval x = true) σ := by
  have hF := (DAGCircuit.isFaninTwo_iff C).1 hC
  have hwf : C.IsWellFormed := (DAGCircuit.isWellFormed_iff C).2 hF.1
  have hmf : C.toTree.maxFanin ≤ 2 := C.toTree_maxFanin_le hwf hF.2
  refine ⟨barrington C.toTree σ, isPermutation_barrington C.toTree σ,
    (barrington_length_le hmf σ).trans
      (Nat.pow_le_pow_right (by norm_num) (C.toTree_depth_le hwf)), ?_⟩
  have h := barrington_recognizes C.toTree hmf hσ
  rw [fiveCycleRecognizes_iff] at h ⊢
  refine ⟨h.1, fun x => ?_⟩
  rw [← C.toTree_eval hwf x]
  exact h.2 x

end BranchingProgram

open BoolCircuit BranchingProgram

/-- **C23.** **NC¹ ⊆ polynomial-length width-5 permutation programs**: `L.InNC 1 → L.InPBP 5`
[Bar89, Corollary, p004-b004; abstract, p001-b001].
Deviation: inputs of length `0` are handled by the accepting set (Thm 1 needs `n ≥ 1`).

**Proof sketch.** `Language.InNC.inTreeNC_one` gives a fan-in-2 formula family `C` with depth
`≤ b·(log₂ n + 1)`, deciding `L` (read through the readers `Language.inTreeNC_iff`,
`TreeCircuitFamily.hasFaninTwo_iff` and `hasPolylogDepth_iff`).
Define the family with `program n = barrington (C.circuit n) sigma1` for `n ≥ 1` (`NeZero`
from `n ≠ 0`) and `⟨[]⟩` for `n = 0`; `accept n = {sigma1}` for `n ≥ 1`, and `{id}` or `∅`
at `n = 0` according to `[] ∈ L` (classical).  Permutation: `isPermutation_barrington`
(`BranchingProgramFamily.isPermutation_iff`).
Length: `barrington_length_le` and `4 ^ (b·(log₂ n + 1)) ≤ 4 ^ b · (n + 1) ^ (2b)`
(`Nat.pow_le_pow_right`, `Nat.pow_log_le_self`), so `BranchingProgramFamily.isPolyLength_iff`.
Language: `BranchingProgramFamily.mem_language_iff`, `barrington_recognizes` with
`isFiveCycle_sigma1`, `TreeCircuitFamily.mem_language_iff`, and `⇑sigma1 ≠ id` (a five-cycle
has `cycleType {5}`: `isFiveCycle_iff`, `Equiv.Perm.cycleType_one`); at `n = 0`, `yield_nil`.
Conclude with `Language.inPBP_iff`. -/
theorem Language.InNC.inPBP_five {L : Language Bool} (h : L.InNC 1) : L.InPBP 5 := by
  classical
  obtain ⟨C, hF, -, hD, hL⟩ := (Language.inTreeNC_iff 1 L).1 h.inTreeNC_one
  obtain ⟨b, hb⟩ := (TreeCircuitFamily.hasPolylogDepth_iff C 1).1 hD
  have hF' := (TreeCircuitFamily.hasFaninTwo_iff C).1 hF
  -- the identity is not the five-cycle `sigma1`
  have hσ1 : (⇑sigma1 : Fin 5 → Fin 5) ≠ id := by
    intro h1
    have h2 : sigma1 = 1 := Equiv.ext fun i => congrFun h1 i
    have h3 := (isFiveCycle_iff sigma1).1 isFiveCycle_sigma1
    rw [h2, Equiv.Perm.cycleType_one] at h3
    exact Multiset.zero_ne_singleton 5 h3
  refine (Language.inPBP_iff 5 L).2
    ⟨⟨fun n => if h0 : n = 0 then ⟨[]⟩ else
        haveI : NeZero n := ⟨h0⟩; barrington (C.circuit n) sigma1,
      fun n => if n = 0 then (if ([] : List Bool) ∈ L then {id} else ∅) else {⇑sigma1}⟩,
      ?_, ?_, ?_⟩
  · -- permutation programs
    refine (BranchingProgramFamily.isPermutation_iff _).2 fun n => ?_
    dsimp only
    by_cases h0 : n = 0
    · rw [dif_pos h0, isPermutation_iff]
      intro ι hι
      exact absurd hι List.not_mem_nil
    · rw [dif_neg h0]
      haveI : NeZero n := ⟨h0⟩
      exact isPermutation_barrington (C.circuit n) sigma1
  · -- polynomial length: `4 ^ (b·(log₂ n + 1)) ≤ 4 ^ b · (n + 1) ^ (2b)`
    refine (BranchingProgramFamily.isPolyLength_iff _).2 ⟨4 ^ b, 2 * b, fun n => ?_⟩
    dsimp only
    by_cases h0 : n = 0
    · rw [dif_pos h0, length_eq]
      exact Nat.zero_le _
    · rw [dif_neg h0]
      haveI : NeZero n := ⟨h0⟩
      have hd : (C.circuit n).depth ≤ b * (Nat.log 2 n + 1) := by
        simpa only [pow_one] using hb n
      have h2 : (2 : ℕ) ^ Nat.log 2 n ≤ n + 1 :=
        (Nat.pow_log_le_self 2 h0).trans (Nat.le_succ n)
      calc (barrington (C.circuit n) sigma1).length ≤ 4 ^ (C.circuit n).depth :=
            barrington_length_le (hF' n) sigma1
        _ ≤ 4 ^ (b * (Nat.log 2 n + 1)) := Nat.pow_le_pow_right (by norm_num) hd
        _ = 4 ^ b * ((2 : ℕ) ^ Nat.log 2 n) ^ (2 * b) := by
            rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add]
            ring
        _ ≤ 4 ^ b * (n + 1) ^ (2 * b) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 _)
  · -- the language: `[]` through the accepting set, `n ≥ 1` through Theorem 1
    ext u
    rw [BranchingProgramFamily.mem_language_iff]
    by_cases h0 : u.length = 0
    · obtain rfl : u = [] := List.eq_nil_of_length_eq_zero h0
      dsimp only
      rw [dif_pos h0, if_pos h0, yield_nil]
      by_cases hL0 : ([] : List Bool) ∈ L
      · rw [if_pos hL0]
        exact iff_of_true (Finset.mem_singleton_self _) hL0
      · rw [if_neg hL0]
        exact iff_of_false (Finset.notMem_empty _) hL0
    · dsimp only
      rw [dif_neg h0, if_neg h0, Finset.mem_singleton, ← hL, TreeCircuitFamily.mem_language_iff]
      haveI : NeZero u.length := ⟨h0⟩
      have hr := ((fiveCycleRecognizes_iff _ _ _).1
        (barrington_recognizes (C.circuit u.length) (hF' u.length) isFiveCycle_sigma1)).2 u.get
      by_cases he : (C.circuit u.length).eval u.get = true
      · exact iff_of_true (by rw [hr.1 he]) he
      · rw [hr.2 he]
        exact iff_of_false (fun h1 => hσ1 h1.symm) he

/-- **C24.** **BWBP ⊆ NC¹**, Theorem 2 for families: `L.InBWBP → L.InNC 1`
[Bar89, Thm 2, p004-b003; abstract, p001-b001: "any bounded-width polynomial-size branching
program can be simulated by an `NC¹` circuit"].
Deviation: the circuits are fan-in-2 formulas (P6-Q18), compiled to `DAGCircuit`s by
`Language.InTreeNC.inNC`.

**Proof sketch.** From `Language.inBWBP_iff` get `w`, `P` and a length bound `a·(n+1)^k`
(`BranchingProgramFamily.isPolyLength_iff`).  The formula family `n ↦ (P.program n).toFormula
(P.accept n)` decides `P.language` (`toFormula_eval`, `BranchingProgramFamily.mem_language_iff`,
`TreeCircuitFamily.mem_language_iff`), has fan-in 2 (`maxFanin_toFormula_le`), and depth
`≤ (⌈log₂ w⌉ + 2)·⌈log₂ (a(n+1)^k)⌉ + topDepth w ≤ b·(log₂ n + 1)` with
`b = (⌈log₂ w⌉ + 2)(a + k) + topDepth w` (`depth_toFormula_le`, `Nat.clog_mono_right`,
`BoolCircuit.clog_poly_le`); its size is
`≤ 2 ^ (depth + 1)` (`TreeCircuit.size_succ_le_two_pow`), hence polynomial.  This gives
`L.InTreeNC 1` (through the readers `Language.inTreeNC_iff`, `TreeCircuitFamily.hasFaninTwo_iff`,
`isPolySize_iff` and `hasPolylogDepth_iff`), and `Language.InTreeNC.inNC` gives `L.InNC 1`. -/
theorem Language.InBWBP.inNC_one {L : Language Bool} (h : L.InBWBP) : L.InNC 1 := by
  obtain ⟨w, P, hP, hL⟩ := (Language.inBWBP_iff L).1 h
  obtain ⟨a, k, ha⟩ := (BranchingProgramFamily.isPolyLength_iff P).1 hP
  -- Step 1: the depth bound `b·(log₂ n + 1)` with `b = (⌈log₂ w⌉ + 2)(a + k) + topDepth w`
  have hdepth : ∀ n, ((P.program n).toFormula (P.accept n)).depth ≤
      ((Nat.clog 2 w + 2) * (a + k) + topDepth w) * (Nat.log 2 n + 1) := by
    intro n
    have hc : Nat.clog 2 (P.program n).length ≤ a + k * (Nat.log 2 n + 1) :=
      (Nat.clog_mono_right 2 (ha n)).trans (BoolCircuit.clog_poly_le a k n)
    have h1 : 1 ≤ Nat.log 2 n + 1 := Nat.le_add_left 1 _
    calc ((P.program n).toFormula (P.accept n)).depth
        ≤ (Nat.clog 2 w + 2) * Nat.clog 2 (P.program n).length + topDepth w :=
          depth_toFormula_le _ _
      _ ≤ (Nat.clog 2 w + 2) * (a + k * (Nat.log 2 n + 1)) + topDepth w :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ hc) _
      _ ≤ ((Nat.clog 2 w + 2) * (a + k) + topDepth w) * (Nat.log 2 n + 1) := by
          have ha1 : a ≤ a * (Nat.log 2 n + 1) := Nat.le_mul_of_pos_right a h1
          have ht1 : topDepth w ≤ topDepth w * (Nat.log 2 n + 1) :=
            Nat.le_mul_of_pos_right _ h1
          have hm := Nat.mul_le_mul_left (Nat.clog 2 w + 2)
            (Nat.add_le_add_right ha1 (k * (Nat.log 2 n + 1)))
          calc (Nat.clog 2 w + 2) * (a + k * (Nat.log 2 n + 1)) + topDepth w
              ≤ (Nat.clog 2 w + 2) * (a * (Nat.log 2 n + 1) + k * (Nat.log 2 n + 1)) +
                  topDepth w * (Nat.log 2 n + 1) := Nat.add_le_add hm ht1
            _ = ((Nat.clog 2 w + 2) * (a + k) + topDepth w) * (Nat.log 2 n + 1) := by ring
  -- Step 2: the formula family is in `NC¹` (fan-in, size `≤ 2 ^ (depth + 1)`, depth, language)
  refine Language.InTreeNC.inNC ((Language.inTreeNC_iff 1 L).2
    ⟨⟨fun n => (P.program n).toFormula (P.accept n)⟩, ?_, ?_, ?_, ?_⟩)
  · exact (TreeCircuitFamily.hasFaninTwo_iff _).2 fun n => maxFanin_toFormula_le _ _
  · refine (TreeCircuitFamily.isPolySize_iff _).2
      ⟨2 ^ ((Nat.clog 2 w + 2) * (a + k) + topDepth w + 1),
        (Nat.clog 2 w + 2) * (a + k) + topDepth w, fun n => ?_⟩
    have hs := TreeCircuit.size_succ_le_two_pow _ (maxFanin_toFormula_le (P.program n) (P.accept n))
    have h2 : (2 : ℕ) ^ Nat.log 2 n ≤ n + 1 := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp only [Nat.log_zero_right, pow_zero, zero_add, le_refl]
      · exact (Nat.pow_log_le_self 2 hn.ne').trans (Nat.le_succ n)
    set B := (Nat.clog 2 w + 2) * (a + k) + topDepth w
    calc ((P.program n).toFormula (P.accept n)).size
        ≤ 2 ^ (((P.program n).toFormula (P.accept n)).depth + 1) := by omega
      _ ≤ 2 ^ (B * (Nat.log 2 n + 1) + 1) := Nat.pow_le_pow_right (by norm_num)
          (Nat.add_le_add_right (hdepth n) 1)
      _ = 2 ^ (B + 1) * ((2 : ℕ) ^ Nat.log 2 n) ^ B := by
          rw [← pow_mul, ← pow_add]; ring_nf
      _ ≤ 2 ^ (B + 1) * (n + 1) ^ B := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 _)
  · exact (TreeCircuitFamily.hasPolylogDepth_iff _ 1).2
      ⟨_, fun n => by rw [pow_one]; exact hdepth n⟩
  · ext u
    rw [TreeCircuitFamily.mem_language_iff, ← hL, BranchingProgramFamily.mem_language_iff]
    dsimp only
    rw [toFormula_eval, decide_eq_true_iff]

/-- **C25.** **Barrington's Corollary**, first equality: nonuniform NC¹ is BWBP,
`L.InNC 1 ↔ L.InBWBP` [Bar89, Corollary, p004-b004].

**Proof sketch.** `→`: `Language.InNC.inPBP_five`, then forget permutation-ness and take `w = 5`
(`Language.inPBP_iff`, `Language.inBWBP_iff`).  `←`: `Language.InBWBP.inNC_one`. -/
theorem Language.inNC_one_iff_inBWBP (L : Language Bool) : L.InNC 1 ↔ L.InBWBP := by
  refine ⟨fun h => ?_, fun h => h.inNC_one⟩
  obtain ⟨P, -, hP, hL⟩ := (Language.inPBP_iff 5 L).1 h.inPBP_five
  exact (Language.inBWBP_iff L).2 ⟨5, P, hP, hL⟩

/-- **C25.** **Barrington's Corollary**, second equality: nonuniform NC¹ is the class of
polynomial-length width-5 permutation programs, `L.InNC 1 ↔ L.InPBP 5`
[Bar89, Corollary, p004-b004].

**Proof sketch.** `→`: `Language.InNC.inPBP_five`.  `←`: a `PBP₅` family is a BWBP family
(`Language.inPBP_iff`, `Language.inBWBP_iff`), then `Language.InBWBP.inNC_one`. -/
theorem Language.inNC_one_iff_inPBP_five (L : Language Bool) : L.InNC 1 ↔ L.InPBP 5 := by
  refine ⟨fun h => h.inPBP_five, fun h => ?_⟩
  obtain ⟨P, -, hP, hL⟩ := (Language.inPBP_iff 5 L).1 h
  exact ((Language.inBWBP_iff L).2 ⟨5, P, hP, hL⟩).inNC_one
