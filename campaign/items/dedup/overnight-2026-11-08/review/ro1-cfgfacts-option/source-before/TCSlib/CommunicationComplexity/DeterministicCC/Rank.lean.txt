/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Real.Basic
import TCSlib.CommunicationComplexity.DeterministicCC.DetComplexity
import TCSlib.CommunicationComplexity.DeterministicCC.Rectangle
import TCSlib.CommunicationComplexity.DeterministicCC.DetRectangle

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Log-Rank Lower Bound for Deterministic Communication Complexity

The communication matrix of a Boolean function `f : X → Y → Bool` and its rank over `ℝ`
[RY20, Ch. 2], and the log-rank lower bound `⌈log₂ rank(M_f)⌉ ≤ D(f)` [RY20, Thm 2.11]
(historically due to Mehlhorn and Schmidt [MS82]). The proof goes through the observation
that a monochromatic rectangle partition with `t` parts expresses `M_f` as a sum of at most
`t` rank-one matrices, so `rank(M_f) ≤ t` [RY20, Lemma 2.10], together with the rectangle
partition induced by a protocol [RY20, Thm 1.7].

## Main definitions

- `Deterministic.Rank.boolFunctionMatrix`: the real `0/1` communication matrix of a Boolean
  function.
- `Deterministic.Rank.boolFunctionRank`: the rank of a Boolean function, defined as the rank
  of its communication matrix over `ℝ`.
- `Deterministic.Rank.rectMatrix`: the `0/1` indicator matrix of a subset of `X × Y`.

## Main results

- `Matrix.rank_add_le`, `Matrix.rank_sum_le`: matrix rank is subadditive (candidates for
  upstreaming to Mathlib).
- `Deterministic.Rank.boolFunctionRank_le_ncard`: the rank of a Boolean function is at most
  the number of parts in any monochromatic rectangle partition.
- `Deterministic.Rank.clog_boolFunctionRank_le_communicationComplexity`: the log-rank lower
  bound: the deterministic communication complexity of a Boolean function is at least the
  ceiling of the base-2 logarithm of the rank of its `0/1` matrix.

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [Rou16] T. Roughgarden, *Communication Complexity (for Algorithm Designers)*,
  Foundations and Trends in Theoretical Computer Science 11(3–4), 2016.
* [MS82] K. Mehlhorn, E. M. Schmidt, "Las Vegas is better than determinism in VLSI and
  distributed computing", *STOC 1982*.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University
  Press, 1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal.
-/

namespace CommunicationComplexity

namespace Deterministic.Rank

open Classical in
/-- The real-valued communication matrix of a Boolean function `f : X → Y → Bool`, whose
`(x, y)` entry is `1` if `f x y = true` and `0` otherwise [RY20, Ch. 2] /
[Rou16, §4.2.3 Definition (matrix representation)]. -/
noncomputable def boolFunctionMatrix {X Y : Type*}
    (f : X → Y → Bool) : Matrix X Y ℝ :=
  Matrix.of fun x y => if f x y then 1 else 0

/-- The rank of a Boolean function `f`, defined as the rank over `ℝ` of its real-valued
communication matrix [RY20, Ch. 2] / [Rou16, §4.2.3 Definition (matrix representation)]. -/
noncomputable def boolFunctionRank {X Y : Type*} [Fintype Y]
    (f : X → Y → Bool) : ℕ :=
  (boolFunctionMatrix f).rank

open Classical in
/-- The `0/1` indicator matrix of a subset `R ⊆ X × Y`: the `(x, y)` entry is `1` if
`(x, y) ∈ R` and `0` otherwise. -/
noncomputable def rectMatrix {X Y : Type*}
    (R : Set (X × Y)) : Matrix X Y ℝ :=
  Matrix.of fun x y => if (x, y) ∈ R then 1 else 0

/-- The indicator matrix of a combinatorial rectangle `R = A ×ˢ B` has rank at most `1`,
since it is the outer product of the indicator vectors of `A` and `B`. -/
theorem rank_rectMatrix_le_one {X Y : Type*} [Fintype Y]
    (R : Set (X × Y)) (hR : Rectangle.IsRectangle R) :
    (rectMatrix R).rank ≤ 1 := by
  classical
  obtain ⟨A, B, rfl⟩ := hR
  suffices rectMatrix (A ×ˢ B) =
      Matrix.vecMulVec (fun x => if x ∈ A then (1 : ℝ) else 0)
        (fun y => if y ∈ B then (1 : ℝ) else 0) by
    rw [this]; exact Matrix.rank_vecMulVec_le _ _
  ext x y; simp only [rectMatrix, Matrix.of_apply, Matrix.vecMulVec, Set.mem_prod_eq]
  cases Classical.em (x ∈ A) <;> cases Classical.em (y ∈ B) <;> simp_all

end Deterministic.Rank

end CommunicationComplexity

/-- Matrix rank is subadditive: `rank (A + B) ≤ rank A + rank B` [RY20, Fact 2.3]. Stated
for real matrices only; candidate for upstreaming to Mathlib. -/
theorem Matrix.rank_add_le {X Y : Type*} [Fintype Y]
    (A B : Matrix X Y ℝ) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank; rw [Matrix.mulVecLin_add]
  refine (Submodule.finrank_mono ?_).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  exact LinearMap.range_add_le _ _

/-- Matrix rank is subadditive over finite sums: the rank of `∑ i ∈ s, A i` is at most
`∑ i ∈ s, rank (A i)` [RY20, Fact 2.3], iterated. Stated for real matrices only; candidate
for upstreaming to Mathlib. -/
theorem Matrix.rank_sum_le {X Y : Type*} [Fintype Y]
    {ι : Type*} (s : Finset ι) (A : ι → Matrix X Y ℝ) :
    (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank := by
  classical
  induction s using Finset.induction with
  | empty => simp [Matrix.rank_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (Matrix.rank_add_le _ _).trans (Nat.add_le_add_left ih _)

namespace CommunicationComplexity

namespace Deterministic.Rank

open Rectangle in
/-- The rank of a Boolean function `f` is at most the number of rectangles in any
monochromatic rectangle partition of its input space [RY20, Lemma 2.10]. Deviation: [RY20]
states the bound `≤ 2 ^ c` for a partition into `2 ^ c` parts; here the bound is the number
of parts itself, for an arbitrary finite partition.

**Proof sketch.** Step 1: let `trueRects` be the parts of the partition that contain some
input on which `f` is `true`; by monochromaticity `f` is `true` throughout each of them.
Step 2: the communication matrix `M_f` equals the sum of the indicator matrices of the parts
in `trueRects`. Entrywise, the input `(x, y)` lies in exactly one part `R₀`, so all other
indicator matrices vanish at `(x, y)`: if `f x y = false` then `R₀` is not in `trueRects`
and every term is `0`; if `f x y = true` then `R₀` is in `trueRects` and contributes `1`.
Step 3: rank is subadditive over the sum (`Matrix.rank_sum_le`), each rectangle indicator
matrix has rank at most `1` (`rank_rectMatrix_le_one`), and `trueRects` is a subset of the
partition, so `rank(M_f) ≤ |trueRects| ≤ |Part|`. -/
theorem boolFunctionRank_le_ncard
    {X Y : Type*} [Finite X] [Fintype Y]
    (f : X → Y → Bool)
    (Part : Set (Set (X × Y)))
    (hPart : Rectangle.IsMonoPartition Part f) :
    boolFunctionRank f ≤ Set.ncard Part := by
  classical
  -- Step 1: the parts containing a `true` input
  let PF := (Set.toFinite Part).toFinset
  let trueRects := PF.filter (fun R => ∃ p ∈ R, f p.1 p.2 = true)
  -- Step 2: M_f = ∑ over true-mono rectangles of rectMatrix R
  have hsum : boolFunctionMatrix f = ∑ R ∈ trueRects, rectMatrix R := by
    ext x y
    simp only [boolFunctionMatrix, rectMatrix, Matrix.of_apply, Matrix.sum_apply]
    obtain ⟨R₀, hR₀_mem, hR₀_in⟩ := monoPartition_point_mem hPart (x, y)
    have hother : ∀ R ∈ PF, R ≠ R₀ → (x, y) ∉ R := fun R hR hne hmem =>
      hne (monoPartition_part_unique hPart
        ((Set.toFinite Part).mem_toFinset.mp hR) hR₀_mem hmem hR₀_in)
    cases hf : f x y <;> simp only [Bool.false_eq_true, ite_true, ite_false]
    · -- f x y = false: every term is 0
      symm; apply Finset.sum_eq_zero; intro R hR
      by_cases hne : R = R₀
      · subst hne; obtain ⟨⟨x', y'⟩, hpin, hftrue⟩ := (Finset.mem_filter.mp hR).2
        have hmono := monoPartition_values_eq hPart hR₀_mem hR₀_in hpin
        rw [hf] at hmono; simp [← hmono] at hftrue
      · simp [hother R (Finset.mem_filter.mp hR).1 hne]
    · -- f x y = true: only R₀ contributes 1
      symm; rw [Finset.sum_eq_single R₀
        (fun R hR hne => by simp [hother R (Finset.mem_filter.mp hR).1 hne])
        (fun h => absurd (Finset.mem_filter.mpr
          ⟨(Set.toFinite Part).mem_toFinset.mpr hR₀_mem, ⟨x, y⟩, hR₀_in, hf⟩) h)]
      simp [hR₀_in]
  -- Step 3: rank(M_f) ≤ ∑ rank(rectMatrix R) ≤ ∑ 1 = |trueRects| ≤ |Part|
  calc boolFunctionRank f
      = (∑ R ∈ trueRects, rectMatrix R).rank := by unfold boolFunctionRank; rw [← hsum]
    _ ≤ ∑ R ∈ trueRects, (rectMatrix R).rank := Matrix.rank_sum_le _ _
    _ ≤ ∑ _R ∈ trueRects, 1 := Finset.sum_le_sum fun R hR =>
        rank_rectMatrix_le_one R (hPart.1 R ((Set.toFinite Part).mem_toFinset.mp
          (Finset.mem_filter.mp hR).1))
    _ = trueRects.card := by simp
    _ ≤ PF.card := Finset.card_filter_le _ _
    _ = Set.ncard Part := (Set.ncard_eq_toFinset_card Part (Set.toFinite Part)).symm

open Rectangle in
/-- If the deterministic communication complexity of `f` is at most `n`, then the rank of
`f` is at most `2 ^ n` [RY20, Lemma 2.10]: a protocol of complexity `n` induces a
monochromatic rectangle partition with at most `2 ^ n` parts [RY20, Thm 1.7]. -/
theorem boolFunctionRank_le_pow_of_communicationComplexity_le
    {X Y : Type*} [Finite X] [Fintype Y]
    (f : X → Y → Bool) (n : ℕ)
    (h : Deterministic.communicationComplexity f ≤ n) :
    boolFunctionRank f ≤ 2 ^ n := by
  obtain ⟨Part, hPart, hCard⟩ := Deterministic.mono_partition_of_communicationComplexity_le f n h
  exact (boolFunctionRank_le_ncard f Part hPart).trans hCard

/-- The log-rank lower bound: the deterministic communication complexity of a Boolean
function `f` is at least `⌈log₂ rank(M_f)⌉` [RY20, Thm 2.11] (historically [MS82]). -/
theorem clog_boolFunctionRank_le_communicationComplexity
    {X Y : Type*} [Finite X] [Fintype Y]
    (f : X → Y → Bool) :
    (Nat.clog 2 (boolFunctionRank f) : ENat) ≤
      Deterministic.communicationComplexity f := by
  match h : Deterministic.communicationComplexity f with
  | ⊤ => exact le_top
  | (n : ℕ) =>
    exact_mod_cast (Nat.clog_le_iff_le_pow (by norm_num)).mpr
      (boolFunctionRank_le_pow_of_communicationComplexity_le f n (le_of_eq h))

end Deterministic.Rank

end CommunicationComplexity
