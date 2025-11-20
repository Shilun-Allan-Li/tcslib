import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Dual

import TCSlib.CodingTheory.QuantumHamming

open Finset
open scoped BigOperators

namespace CodingTheory

variable {α : Type*} [Field α] [Fintype α] [DecidableEq α]
variable {n : ℕ}

/-- `erased` is erasure-correctable if every logical operator supported on it
lies in the stabilizer. -/
def ErasureCorrectable (S : Stabilizer n α) (erased : Finset (Fin n)) : Prop :=
  ∀ (p : SympVec n α),
    (∀ i, i ∉ erased → p.1 i = 0 ∧ p.2 i = 0) →  -- supported on `erased`
    (∀ s ∈ S.S.toSet, symplecticForm p s = 0) →  -- in N(S)
    p ∈ S.S                                      -- must be in S

/--
If `S` has quantum distance `d`, then any set of `d-1` qubits is erasure correctable.
-/
lemma erasure_correctable_of_dist (S : Stabilizer n α) (erased : Finset (Fin n))
    (h_dist : erased.card < quantum_distance S) :
    ErasureCorrectable S erased := by
  intro p h_supp h_comm
  by_contra h_notin_S
  have h_weight : pauliWeight p ≤ erased.card := by
    simp [pauliWeight]
    apply Finset.card_le_card
    intro i hi
    simp at hi
    by_contra h_not_in
    specialize h_supp i h_not_in
    rw [h_supp.1, h_supp.2] at hi
    simp at hi
  have h_ne_zero : pauliWeight p ≠ 0 := by
    intro h0
    have : p = 0 := by
      simp [pauliWeight] at h0
      ext i
      have h_empty := Finset.eq_empty_of_card_eq_zero h0
      have h1 : p.1 i = 0 := by
        by_contra h
        have : i ∈ {x | p.1 x ≠ 0 ∨ p.2 x ≠ 0} := by simp [h]
        rw [h_empty] at this
        contradiction
      have h2 : p.2 i = 0 := by
        by_contra h
        have : i ∈ {x | p.1 x ≠ 0 ∨ p.2 x ≠ 0} := by simp [h]
        rw [h_empty] at this
        contradiction
      simp [h1, h2]
    rw [this] at h_notin_S
    exact h_notin_S (Submodule.zero_mem S.S)
  have : quantum_distance S ≤ pauliWeight p :=
    quantum_distance_le_pauliWeight (S:=S) p h_comm h_notin_S h_ne_zero
  linarith

/-- Logical operators can be cleaned off any erasure-correctable set. -/
lemma clean_logical_operator (S : Stabilizer n α) (erased : Finset (Fin n))
    (h_corr : ErasureCorrectable S erased) (L : SympVec n α)
    (h_L_comm : ∀ s ∈ S.S.toSet, symplecticForm L s = 0) :
    ∃ s ∈ S.S, ∀ i ∈ erased, (L + s).1 i = 0 ∧ (L + s).2 i = 0 := by
  sorry -- Standard result, assumed for now.

/-- Contribution of indices in `C`. -/
def symplecticFormOn (C : Finset (Fin n)) (p q : SympVec n α) : α :=
  ∑ i ∈ C, (p.1 i * q.2 i - p.2 i * q.1 i)

lemma symplecticForm_decompose (p q : SympVec n α) (A B C : Finset (Fin n))
    (h_part : Disjoint A B ∧ Disjoint A C ∧ Disjoint B C)
    (h_union : A ∪ B ∪ C = Finset.univ) :
    symplecticForm p q =
      symplecticFormOn A p q +
      symplecticFormOn B p q +
      symplecticFormOn C p q := by
  classical
  set f := fun i : Fin n => p.1 i * q.2 i - p.2 i * q.1 i
  have hAB : Disjoint A B := h_part.1
  have hAC : Disjoint A C := h_part.2.1
  have hBC : Disjoint B C := h_part.2.2
  have hAC_left := Finset.disjoint_left.1 hAC
  have hBC_left := Finset.disjoint_left.1 hBC
  have h_disj_union : Disjoint (A ∪ B) C := by
    refine Finset.disjoint_left.2 ?_
    intro x hx hxC
    have hxAorB : x ∈ A ∪ B := hx
    rcases Finset.mem_union.1 hxAorB with hxA | hxB
    · exact hAC_left hxA hxC
    · exact hBC_left hxB hxC
  have h_symm :
      symplecticForm p q = ∑ i ∈ A ∪ B ∪ C, f i := by
    simp [symplecticForm, f, h_union]
  have h_split₁ :
      ∑ i ∈ A ∪ B ∪ C, f i
        = ∑ i ∈ A ∪ B, f i + ∑ i ∈ C, f i := by
    simpa using
      (Finset.sum_union h_disj_union (fun i : Fin n => f i))
  have h_split₂ :
      ∑ i ∈ A ∪ B, f i
        = ∑ i ∈ A, f i + ∑ i ∈ B, f i := by
    simpa using
      (Finset.sum_union hAB (fun i : Fin n => f i))
  have h_comb :
      ∑ i ∈ A ∪ B ∪ C, f i
        = (∑ i ∈ A, f i + ∑ i ∈ B, f i) + ∑ i ∈ C, f i := by
    simpa [h_split₂] using h_split₁
  have h_eval :
      (∑ i ∈ A, f i + ∑ i ∈ B, f i) + ∑ i ∈ C, f i
        = symplecticFormOn A p q + symplecticFormOn B p q + symplecticFormOn C p q := by
    simp [symplecticFormOn, f, add_comm, add_left_comm, add_assoc]
  simpa [symplecticFormOn, f, h_eval] using h_symm.trans h_comb

/-- Algebraic reduction: once the rank bound holds, the inequality follows. -/
lemma quantum_singleton_bound_of_rank (n k d : ℕ) (S : Stabilizer n α)
    [FiniteDimensional α (SympVec n α)]
    (h_dim : k = quantum_code_dimension S.S)
    (h_rank : 2 * (d - 1) ≤ FiniteDimensional.finrank α S.S) :
    k ≤ n - 2 * (d - 1) := by
  classical
  have hk : k = n - FiniteDimensional.finrank α S.S := by
    simpa [quantum_code_dimension] using h_dim
  have h_le : n - FiniteDimensional.finrank α S.S ≤ n - 2 * (d - 1) :=
    Nat.sub_le_sub_left h_rank n
  simpa [hk]

lemma quantum_singleton_bound_aux (n k d : ℕ) (S : Stabilizer n α)
    [FiniteDimensional α (SympVec n α)]
    (h_dim : k = quantum_code_dimension S.S)
    (h_dist : d ≤ quantum_distance S)
    (hd : 0 < d)
    (h_n_ge : n ≥ 2 * (d - 1)) -- Needed to form disjoint sets A, B
    (A B C : Finset (Fin n))
    (h_A_card : A.card = d - 1)
    (h_B_card : B.card = d - 1)
    (h_disj : Disjoint A B)
    (h_C_def : C = (A ∪ B)ᶜ) :
    k ≤ C.card := by
  classical
  by_contra h_contra
  push_neg at h_contra

  have h_corr_A : ErasureCorrectable S A := by
    apply erasure_correctable_of_dist
    rw [h_A_card]
    linarith
  have h_corr_B : ErasureCorrectable S B := by
    apply erasure_correctable_of_dist
    rw [h_B_card]
    linarith

  -- Clean logical operators off A and B, restrict to C, and compare dimensions.
  sorry -- Formalizing the dimension counting argument requires more setup.

/-- Rank bound obtained from the distance assumption. -/
lemma stabilizer_rank_ge_of_distance (n d : ℕ) (S : Stabilizer n α)
    [FiniteDimensional α (SympVec n α)]
    (h_dist : d ≤ quantum_distance S)
    (hd : 0 < d) :
    2 * (d - 1) ≤ FiniteDimensional.finrank α S.S := by
  classical
  by_contra h_rank_low
  push_neg at h_rank_low
  let r := FiniteDimensional.finrank α S.S
  have h_k : quantum_code_dimension S.S = n - r := rfl
  let k := n - r
  have h_k_bound : n - 2 * (d - 1) < k := by
    have : 2 * (d - 1) > r := h_rank_low
    linarith

  if h_n : 2 * (d - 1) ≤ n then
    have h_fin_card : Fintype.card (Fin n) = n := Fintype.card_fin n
    -- Construct sets A, B, C
    let A : Finset (Fin n) := (Finset.univ.toList.take (d - 1)).toFinset
    let B : Finset (Fin n) := (Finset.univ.toList.drop (d - 1)).take (d - 1) |>.toFinset
    let C : Finset (Fin n) := (A ∪ B)ᶜ

    have h_A_card : A.card = d - 1 := by
      sorry -- List manipulation
    have h_B_card : B.card = d - 1 := by
      sorry -- List manipulation
    have h_disj : Disjoint A B := by
      sorry -- List manipulation

    have h_ineq := quantum_singleton_bound_aux n k d S rfl h_dist hd h_n A B C h_A_card h_B_card h_disj rfl
    -- |C| = n - 2(d-1)
    have h_C_card : C.card = n - 2 * (d - 1) := by
      sorry -- Set arithmetic

    rw [h_C_card] at h_ineq
    linarith
  else
    sorry

theorem quantum_singleton_bound (n k d : ℕ) (S : Stabilizer n α)
    [FiniteDimensional α (SympVec n α)]
    (h_dim : k = quantum_code_dimension S.S)
    (h_dist : 0 < d)
    (h_dist_le : d ≤ n)
    (h_code_dist : d ≤ quantum_distance S) :
    k ≤ n - 2 * (d - 1) := by
  classical
  have h_rank := stabilizer_rank_ge_of_distance (n:=n) (d:=d) S h_code_dist h_dist
  exact quantum_singleton_bound_of_rank (n:=n) (k:=k) (d:=d) S h_dim h_rank

end CodingTheory
