/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.DAGFanin
import TCSlib.Complexity.CircuitComplexity.TreeNCAC
import TCSlib.Complexity.CircuitComplexity.PPoly

/-!
# The circuit classes `NC` and `AC`

[AB09, Defs 6.24 and 6.25] over the book's circuit model `BoolCircuit.DAGCircuit`, and
their relation to the formula (tree) versions `Language.InTreeNC` / `Language.InTreeAC` of
`TreeNCAC.lean`.

## Main definitions

* `Language.InNC` — [AB09, Def 6.24], `NC^d`; `BoolCircuit.NC` — `⋃_{i ≥ 1} NC^i`.
* `Language.InAC` — [AB09, Def 6.25], `AC^d`; `BoolCircuit.AC` — `⋃_{i ≥ 0} AC^i`.

## Main results

* `Language.InNC.inAC`, `Language.InAC.inNC_succ` — `NC^i ⊆ AC^i ⊆ NC^{i+1}` [AB09, p. 118],
  hence `BoolCircuit.NC_eq_AC`.  The second inclusion binarizes every gate
  (`DAGCircuit.binarize`), multiplying depth by `O(log n)`.
* `Language.InTreeNC.inNC`, `Language.InTreeAC.inAC` — every formula class is inside the
  circuit class of the same level (compile the formula, `TreeCircuit.toDAG`).
* `Language.InNC.inPPoly`, `BoolCircuit.NC_subset_PPoly` — `NC ⊆ P/poly` [AB09, §6.7.1].
* `Language.inNC_one_iff`, `Language.inAC_zero_iff` — at `NC¹` and `AC⁰` the formula and
  circuit classes coincide: unfolding a DAG of depth `O(log n)` and fan-in two, or of
  constant depth and polynomial fan-in, costs only polynomial size.  At higher levels the
  unfolding is quasi-polynomial and no such equality is known.

## Divergences from [AB09, §6.7.1]

* The model's own divergences are listed in `DAGCircuit.lean`.
* `O(log^d n)` is written `∃ b, ∀ n, depth ≤ b * (Nat.log 2 n + 1) ^ d`; the `+ 1` keeps
  `n ≤ 1`, where `Nat.log 2 n = 0`, from forcing depth `0`.  Polynomial size is
  `size ≤ a * (n + 1) ^ k`, as in `PPoly.lean`.
* Uniform `NC` needs logspace machinery and is not defined.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.7.1, Definitions 6.24 and 6.25.)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-- `L ∈ NC^d`: a polynomial-size fan-in-two circuit family of depth `O(log^d n)` decides
`L`.  [AB09, Def 6.24] -/
def Language.InNC (d : ℕ) (L : Language Bool) : Prop :=
  ∃ C : BoolCircuit.DAGCircuitFamily,
    C.HasFaninTwo ∧ C.IsPolySize ∧ C.HasPolylogDepth d ∧ C.language = L

/-- `L ∈ AC^d`: as `NC^d`, but `∧`/`∨` gates may have unbounded fan-in.
[AB09, Def 6.25] -/
def Language.InAC (d : ℕ) (L : Language Bool) : Prop :=
  ∃ C : BoolCircuit.DAGCircuitFamily,
    C.IsWellFormed ∧ C.IsPolySize ∧ C.HasPolylogDepth d ∧ C.language = L

namespace BoolCircuit

/-- `NC^d` as a set of languages. -/
def NCLevel (d : ℕ) : Set (Language Bool) := {L | L.InNC d}

/-- `AC^d` as a set of languages. -/
def ACLevel (d : ℕ) : Set (Language Bool) := {L | L.InAC d}

/-- `NC = ⋃_{i ≥ 1} NC^i`.  [AB09, Def 6.24] -/
def NC : Set (Language Bool) := ⋃ i ∈ Set.Ici 1, NCLevel i

/-- `AC = ⋃_{i ≥ 0} AC^i`.  [AB09, Def 6.25] -/
def AC : Set (Language Bool) := ⋃ i, ACLevel i

theorem mem_NC_iff (L : Language Bool) : L ∈ NC ↔ ∃ i, 1 ≤ i ∧ L.InNC i := by
  simp [NC, NCLevel, Set.mem_iUnion]

theorem mem_AC_iff (L : Language Bool) : L ∈ AC ↔ ∃ i, L.InAC i := by
  simp [AC, ACLevel, Set.mem_iUnion]

end BoolCircuit

/-- `NC^i ⊆ AC^i`: forget the fan-in bound.  [AB09, p. 118] -/
theorem Language.InNC.inAC {d : ℕ} {L : Language Bool} (h : L.InNC d) : L.InAC d := by
  obtain ⟨C, hF, hS, hD, hL⟩ := h
  exact ⟨C, hF.isWellFormed, hS, hD, hL⟩

namespace BoolCircuit

/-- `NC^i ⊆ AC^i`, as sets.  [AB09, p. 118] -/
theorem NCLevel_subset_ACLevel (i : ℕ) : NCLevel i ⊆ ACLevel i :=
  fun _ h => Language.InNC.inAC h

/-! ## Formula classes versus circuit classes -/

/-- Compiling a polynomial-size formula family gives a polynomial-size circuit family. -/
private theorem poly_add_input {a k n s : ℕ} (hs : s ≤ a * (n + 1) ^ k) :
    n + s ≤ (a + 1) * (n + 1) ^ (k + 1) := by
  have h1 : n + 1 ≤ (n + 1) ^ (k + 1) := Nat.le_self_pow (by omega) _
  have h2 : (n + 1) ^ k ≤ (n + 1) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : a * (n + 1) ^ k ≤ a * (n + 1) ^ (k + 1) := Nat.mul_le_mul_left _ h2
  nlinarith

/-- Depth grows by at most one under compilation, which `O(log^d n)` absorbs. -/
private theorem polylog_add_one {b d L t : ℕ} (ht : t ≤ b * (L + 1) ^ d) :
    t + 1 ≤ (b + 1) * (L + 1) ^ d := by
  have : 1 ≤ (L + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  nlinarith

/-- The circuit family compiled from a formula family. -/
def TreeCircuitFamily.toDAG (C : TreeCircuitFamily) : DAGCircuitFamily :=
  ⟨fun n => (C.circuit n).toDAG⟩

theorem TreeCircuitFamily.language_toDAG (C : TreeCircuitFamily) :
    C.toDAG.language = C.language := by
  ext w
  simp [TreeCircuitFamily.toDAG, DAGCircuitFamily.mem_language_iff,
    TreeCircuitFamily.mem_language_iff, TreeCircuit.toDAG_eval]

theorem TreeCircuitFamily.isPolySize_toDAG {C : TreeCircuitFamily} (h : C.IsPolySize) :
    C.toDAG.IsPolySize := by
  obtain ⟨a, k, hs⟩ := h
  exact ⟨a + 1, k + 1, fun n =>
    ((C.circuit n).toDAG_size_le).trans (poly_add_input (hs n))⟩

theorem TreeCircuitFamily.hasPolylogDepth_toDAG {C : TreeCircuitFamily} {d : ℕ}
    (h : C.HasPolylogDepth d) : C.toDAG.HasPolylogDepth d := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b + 1, fun n => ((C.circuit n).toDAG_depth_le).trans (polylog_add_one (hb n))⟩

end BoolCircuit

open BoolCircuit in
/-- Every `NC^d` formula family compiles to an `NC^d` circuit family. -/
theorem Language.InTreeNC.inNC {d : ℕ} {L : Language Bool} (h : L.InTreeNC d) :
    L.InNC d := by
  obtain ⟨C, hF, hS, hD, hL⟩ := h
  exact ⟨C.toDAG, fun n => (C.circuit n).toDAG_isFaninTwo (hF n),
    TreeCircuitFamily.isPolySize_toDAG hS, TreeCircuitFamily.hasPolylogDepth_toDAG hD,
    by rw [TreeCircuitFamily.language_toDAG, hL]⟩

open BoolCircuit in
/-- Every `AC^d` formula family compiles to an `AC^d` circuit family. -/
theorem Language.InTreeAC.inAC {d : ℕ} {L : Language Bool} (h : L.InTreeAC d) :
    L.InAC d := by
  obtain ⟨C, hS, hD, hL⟩ := h
  exact ⟨C.toDAG, fun n => (C.circuit n).toDAG_isWellFormed,
    TreeCircuitFamily.isPolySize_toDAG hS, TreeCircuitFamily.hasPolylogDepth_toDAG hD,
    by rw [TreeCircuitFamily.language_toDAG, hL]⟩

namespace BoolCircuit

/-- The formula family unfolded from a circuit family. -/
def DAGCircuitFamily.toTree (C : DAGCircuitFamily) : TreeCircuitFamily :=
  ⟨fun n => (C.circuit n).toTree⟩

theorem DAGCircuitFamily.language_toTree {C : DAGCircuitFamily} (h : C.IsWellFormed) :
    C.toTree.language = C.language := by
  ext w
  simp [DAGCircuitFamily.toTree, DAGCircuitFamily.mem_language_iff,
    TreeCircuitFamily.mem_language_iff, DAGCircuit.toTree_eval _ (h _)]

/-- `3 ^ log₂ n ≤ (n + 1) ^ 2`. -/
private theorem three_pow_log_le (n : ℕ) : 3 ^ Nat.log 2 n ≤ (n + 1) ^ 2 := by
  have h2 : 2 ^ Nat.log 2 n ≤ n + 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact (Nat.pow_log_le_self 2 hn.ne').trans (Nat.le_succ n)
  calc 3 ^ Nat.log 2 n ≤ 4 ^ Nat.log 2 n := Nat.pow_le_pow_left (by norm_num) _
    _ = (2 ^ Nat.log 2 n) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    _ ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left h2 _

end BoolCircuit

open BoolCircuit in
/-- `NC¹` circuits unfold to `NC¹` formulas: depth `b (log₂ n + 1)` and fan-in two give at
most `3 ^ (b (log₂ n + 1)) ≤ 3 ^ b (n + 1) ^ (2 b)` nodes. -/
theorem Language.InNC.inTreeNC_one {L : Language Bool} (h : L.InNC 1) : L.InTreeNC 1 := by
  obtain ⟨C, hF, hS, ⟨b, hb⟩, hL⟩ := h
  have hwf := hF.isWellFormed
  refine ⟨C.toTree, fun n => (C.circuit n).toTree_maxFanin_le (hwf n) (hF n).2,
    ⟨3 ^ b, 2 * b, fun n => ?_⟩, ⟨b, fun n => ?_⟩, by rw [C.language_toTree hwf, hL]⟩
  · have hd : (C.circuit n).depth ≤ b * (Nat.log 2 n + 1) := by simpa using hb n
    calc (C.toTree.circuit n).size ≤ (2 + 1) ^ (C.circuit n).depth :=
          (C.circuit n).toTree_size_le (hwf n) (hF n).2
      _ ≤ 3 ^ (b * (Nat.log 2 n + 1)) := Nat.pow_le_pow_right (by norm_num) hd
      _ = (3 * 3 ^ Nat.log 2 n) ^ b := by rw [mul_comm, pow_mul, pow_succ']
      _ ≤ (3 * (n + 1) ^ 2) ^ b :=
          Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (three_pow_log_le n)) _
      _ = 3 ^ b * (n + 1) ^ (2 * b) := by rw [mul_pow, ← pow_mul]
  · exact ((C.circuit n).toTree_depth_le (hwf n)).trans (hb n)

open BoolCircuit in
/-- `AC⁰` circuits unfold to `AC⁰` formulas: constant depth `b` and fan-in at most the
size `s` give at most `(s + 1) ^ b` nodes. -/
theorem Language.InAC.inTreeAC_zero {L : Language Bool} (h : L.InAC 0) : L.InTreeAC 0 := by
  obtain ⟨C, hwf, ⟨a, k, hs⟩, ⟨b, hb⟩, hL⟩ := h
  refine ⟨C.toTree, ⟨(a + 1) ^ b, k * b, fun n => ?_⟩, ⟨b, fun n => ?_⟩,
    by rw [C.language_toTree hwf, hL]⟩
  · have hd : (C.circuit n).depth ≤ b := by simpa using hb n
    calc (C.toTree.circuit n).size ≤ ((C.circuit n).size + 1) ^ (C.circuit n).depth :=
          (C.circuit n).toTree_size_le (hwf n) ((C.circuit n).args_length_le_size (hwf n))
      _ ≤ ((C.circuit n).size + 1) ^ b := Nat.pow_le_pow_right (by omega) hd
      _ ≤ ((a + 1) * (n + 1) ^ k) ^ b := by
          apply Nat.pow_le_pow_left
          have := hs n
          have : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
          nlinarith
      _ = (a + 1) ^ b * (n + 1) ^ (k * b) := by rw [mul_pow, ← pow_mul]
  · simpa using ((C.circuit n).toTree_depth_le (hwf n)).trans (by simpa using hb n)

/-- At `NC¹` the circuit and formula classes coincide. -/
theorem Language.inNC_one_iff (L : Language Bool) : L.InNC 1 ↔ L.InTreeNC 1 :=
  ⟨Language.InNC.inTreeNC_one, Language.InTreeNC.inNC⟩

/-- At `AC⁰` the circuit and formula classes coincide. -/
theorem Language.inAC_zero_iff (L : Language Bool) : L.InAC 0 ↔ L.InTreeAC 0 :=
  ⟨Language.InAC.inTreeAC_zero, Language.InTreeAC.inAC⟩

/-- `AC⁰ ⊆ NC¹`, through the formula classes.  [AB09, p. 118] -/
theorem Language.InAC.inNC_one_of_zero {L : Language Bool} (h : L.InAC 0) : L.InNC 1 :=
  (h.inTreeAC_zero.inTreeNC_succ).inNC

open BoolCircuit in
/-- `AC^i ⊆ NC^{i+1}`: binarize every gate.  A gate reads at most `size ≤ a (n + 1) ^ k`
vertices, so each becomes a tree of depth `O(log n)`.  [AB09, p. 118] -/
theorem Language.InAC.inNC_succ {d : ℕ} {L : Language Bool} (h : L.InAC d) :
    L.InNC (d + 1) := by
  obtain ⟨C, hwf, ⟨a, k, hs⟩, ⟨b, hb⟩, hL⟩ := h
  refine ⟨⟨fun n => (C.circuit n).binarize (hwf n)⟩, fun n => (C.circuit n).binarize_isFaninTwo (hwf n),
    ⟨a * (a + 2), 2 * k, fun n => ?_⟩, ⟨b * (a + k + 1), fun n => ?_⟩, ?_⟩
  · have h1 := (C.circuit n).binarize_size_le (hwf n)
    have hS := hs n
    have hG : (C.circuit n).gates.length ≤ (C.circuit n).size := by
      simp [DAGCircuit.size]
    have hn : n ≤ (C.circuit n).size := by simp [DAGCircuit.size]
    have hp : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
    calc ((C.circuit n).binarize (hwf n)).size
        ≤ n + (C.circuit n).gates.length * ((C.circuit n).size + 2) := h1
      _ ≤ (C.circuit n).size * ((C.circuit n).size + 2) := by
          have hSdef : (C.circuit n).size = n + (C.circuit n).gates.length := rfl
          rw [hSdef]; nlinarith
      _ ≤ (a * (n + 1) ^ k) * (a * (n + 1) ^ k + 2) := Nat.mul_le_mul hS (by omega)
      _ ≤ (a * (n + 1) ^ k) * ((a + 2) * (n + 1) ^ k) := by
          apply Nat.mul_le_mul_left; nlinarith
      _ = a * (a + 2) * (n + 1) ^ (2 * k) := by ring
  · have hK : Nat.clog 2 (C.circuit n).size + 1 ≤ (a + k + 1) * (Nat.log 2 n + 1) := by
      have hc : Nat.clog 2 (C.circuit n).size ≤ Nat.clog 2 (a * (n + 1) ^ k) :=
        Nat.clog_mono_right _ (hs n)
      have hpoly := BoolCircuit.clog_poly_le a k n
      have e2 : (a + k + 1) * (Nat.log 2 n + 1)
          = a * (Nat.log 2 n + 1) + k * (Nat.log 2 n + 1) + (Nat.log 2 n + 1) := by ring
      have e1 : a ≤ a * (Nat.log 2 n + 1) := Nat.le_mul_of_pos_right a (by omega)
      omega
    calc ((C.circuit n).binarize (hwf n)).depth
        ≤ (Nat.clog 2 (C.circuit n).size + 1) * (C.circuit n).depth :=
          (C.circuit n).binarize_depth_le _
      _ ≤ ((a + k + 1) * (Nat.log 2 n + 1)) * (b * (Nat.log 2 n + 1) ^ d) :=
          Nat.mul_le_mul hK (hb n)
      _ = b * (a + k + 1) * (Nat.log 2 n + 1) ^ (d + 1) := by ring
  · rw [← hL]; ext w
    simp [DAGCircuitFamily.mem_language_iff, DAGCircuit.binarize_eval]

namespace BoolCircuit

/-- `AC^i ⊆ NC^{i+1}`, as sets.  [AB09, p. 118] -/
theorem ACLevel_subset_NCLevel_succ (i : ℕ) : ACLevel i ⊆ NCLevel (i + 1) :=
  fun _ h => Language.InAC.inNC_succ h

/-- `NC = AC`.  [AB09, p. 118] -/
theorem NC_eq_AC : NC = AC := by
  ext L
  rw [mem_NC_iff, mem_AC_iff]
  constructor
  · rintro ⟨i, -, h⟩; exact ⟨i, h.inAC⟩
  · rintro ⟨i, h⟩; exact ⟨i + 1, by omega, h.inNC_succ⟩

end BoolCircuit

/-- `NC^d ⊆ P/poly`: an `NC` family is a polynomial-size fan-in-two family.
[AB09, §6.7.1] -/
theorem Language.InNC.inPPoly {d : ℕ} {L : Language Bool} (h : L.InNC d) : L.InPPoly := by
  obtain ⟨C, hF, hS, -, hL⟩ := h
  exact (Language.inPPoly_iff L).mpr ⟨C, hF, hS, hL⟩

/-- `AC^d ⊆ P/poly`, through `AC^d ⊆ NC^{d+1}`. -/
theorem Language.InAC.inPPoly {d : ℕ} {L : Language Bool} (h : L.InAC d) : L.InPPoly :=
  h.inNC_succ.inPPoly

namespace BoolCircuit

/-- `NC ⊆ P/poly`.  [AB09, §6.7.1] -/
theorem NC_subset_PPoly : NC ⊆ PPoly := by
  intro L hL
  obtain ⟨i, -, h⟩ := (mem_NC_iff L).mp hL
  exact h.inPPoly

end BoolCircuit
