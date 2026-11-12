import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Subset Sum and Partition

## Subset Sum
The **Subset Sum** problem asks: given a weight function `w : U → ℕ` and a
target integer `T`, does there exist a subset `S ⊆ U` such that
sum of weights of elements in `S` is exactly `T`?

## Partition
The **Partition** problem asks: given a weight function `w : U → ℕ` and a
target integer `T`, does there exist a subset `S ⊆ U` such that
sum of weights of elements in `S` is same as the sum of weights of elements in
the complement of `S`?

Partition is a special case of Subset Sum where the target `T` is exactly half
of the total weight of all elements.

## Reduction from Subset Sum to Partition.

Given a Subset Sum instance, weight `w : U → ℕ` and target `T`, we create
an instance of Partition as follows:
* Augment the universe to have two new elements `U' = U ∪ {⊤, ⊥}`.
* The weight function `w' : U' → ℕ` is `w'(x) = w(x)` for `x ∈ U` and
  `w(⊤) = 2 * W - T` and `w(⊥) = W + T` where `W` is the sum of weights of all
  elements in `U`.

**Proof Sketch.**
_Completeness:_

If there exists a subset `S ⊆ U` such that `∑_{x ∈ S} w(x) = T`, then
consider `S' = S ∪ {⊤}`.
The sum of weights in `S'` is `T + (2W - T) = 2W`.
The total weight of all elements in `U'` is `W + (2W - T) + (W + T) = 4W`.
Thus, `S'` partitions `U'` into two sets of equal weight `2W`.

_Soundness:_

Suppose there is a partition `S' ⊆ U'` such that `∑_{x ∈ S'} w'(x) = 2W`.
Let `S = S' ∩ U`. Note that `∑_{x ∈ S} w(x) ≤ W`.
Consider the dummy elements:
- If `{⊤, ⊥} ⊆ S'`, sum is `≥ (2W - T) + (W + T) = 3W > 2W` (contradiction).
- If `{⊤, ⊥} ∩ S' = ∅`, sum is `≤ W < 2W` (contradiction).
- If `⊤ ∈ S'` and `⊥ ∉ S'`, sum is `(∑_{x ∈ S} w(x)) + (2W - T) = 2W`.
  This implies `∑_{x ∈ S} w(x) = T`, so `S` is a solution.
- If `⊥ ∈ S'` and `⊤ ∉ S'`, sum is `(∑_{x ∈ S} w(x)) + (W + T) = 2W`.
  This implies `∑_{x ∈ S} w(x) = W - T`. The complement `U \ S` has weight `T`.

## Main results
- `SubsetSumToPartitionReduction`: SubsetSum w T ↔ Partition (partitionWeight w T)
-/

namespace SubsetSumToPartition

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The Subset Sum problem:
  Given a weight function `w` and a target `T`, does there exist a subset `S`
  of `U` whose weights sum exactly to `T`?
-/
noncomputable def SubsetSum (w : U → ℕ) (T : ℕ) : Prop :=
  ∃ S : Finset U, (∑ a ∈ S, w a) = T

/-- The Partition problem:
  Given a finite set `U` and a weight function `v`, does there exist a subset
  `S` whose sum equals the sum of its complement `Sᶜ`?
-/
noncomputable def Partition (v : U → ℕ) : Prop :=
  ∃ S : Finset U, (∑ b ∈ S, v b) = (∑ b ∈ Sᶜ, v b)

/-- Reduction from Subset Sum to Partition.

  We create a new type `B` by taking the disjoint union of `U` and `Bool`.
  `U ⊕ Bool` acts as our new set, adding exactly two new "dummy" items:
  - `Sum.inl a` represents the original elements from `A`.
  - `Sum.inr true` represents our first dummy item 'y'.
  - `Sum.inr false` represents our second dummy item 'z'.
-/
def partitionWeight (w : U → ℕ) (T : ℕ) : U ⊕ Bool → ℕ
  | Sum.inl a => w a
  | Sum.inr true => 2 * (∑ a, w a) - T
  | Sum.inr false => (∑ a, w a) + T

/-- Completeness of reduction from Subset Sum to Partition.

Note the hypothesis `(h : T ≤ ∑ a, w a)`. Because Lean's natural numbers `ℕ`
do not support negative numbers (subtraction truncates at 0), we must assert
that the target `T` is not strictly greater than the total weight of all
items. (If it were, the Subset Sum would be trivially false anyway).
-/
theorem SubsetSumToPartitionCompleteness (w : U → ℕ) (T : ℕ) (h : T ≤ ∑ a, w a):
  SubsetSum w T → Partition (partitionWeight w T) := by
  intro ⟨S, hS⟩
  -- Witness: {inl a | a ∈ S} ∪ {inr true}
  let S' := S.image Sum.inl ∪ {Sum.inr true}
  refine ⟨S', ?_⟩
  have hDisj : Disjoint (S.image Sum.inl) ({Sum.inr true} : Finset (U ⊕ Bool))
    := by simp
  -- Step 1: Left side sums to 2W
  have hSumLHS : ∑ b ∈ S', partitionWeight w T b = 2 * (∑ a, w a) := by
    show ∑ b ∈ S.image Sum.inl ∪ {Sum.inr true}, partitionWeight w T b = 2 * (∑ a, w a)
    rw [Finset.sum_union hDisj, Finset.sum_image (Sum.inl_injective.injOn),
      Finset.sum_singleton]
    simp only [partitionWeight]
    omega
  -- Step 2: Total sum is 4W
  have hTotalSum : ∑ b : U ⊕ Bool, partitionWeight w T b = 4 * (∑ a, w a) := by
    rw [Fintype.sum_sum_type, Fintype.sum_bool]
    simp only [partitionWeight]
    omega
  -- Step 3: Use complement to get right side = 2W
  have hadd := Finset.sum_add_sum_compl S' (partitionWeight w T)
  rw [hTotalSum] at hadd
  omega

/-- Soundness of reduction from Subset Sum to Partition.

Note the hypothesis `(h : T ≤ ∑ a, w a)`. Because Lean's natural numbers `ℕ`
do not support negative numbers (subtraction truncates at 0), we must assert
that the target `T` is not strictly greater than the total weight of all
items. (If it were, the Subset Sum would be trivially false anyway).
-/
theorem SubsetSumToPartitionSoundness (w : U → ℕ) (T : ℕ) (h : T ≤ ∑ a, w a):
  Partition (partitionWeight w T) → SubsetSum w T := by
  classical
  rintro ⟨S', hS'⟩
  set S : Finset U := Finset.univ.filter (fun a => Sum.inl a ∈ S') with hSdef
  have hmemS : ∀ a : U, a ∈ S ↔ Sum.inl a ∈ S' := by
    intro a
    simp [hSdef]
  have keySplit : ∀ (t : Finset (U ⊕ Bool)) (Sf : Finset U),
      (∀ a, a ∈ Sf ↔ Sum.inl a ∈ t) →
      ∑ b ∈ t, partitionWeight w T b
        = (∑ a ∈ Sf, w a)
          + (if Sum.inr true ∈ t then partitionWeight w T (Sum.inr true) else 0)
          + (if Sum.inr false ∈ t then partitionWeight w T (Sum.inr false) else 0) := by
    intro t Sf hmem
    have hA : ∑ a : U, (if Sum.inl a ∈ t then partitionWeight w T (Sum.inl a) else 0)
        = ∑ a ∈ Sf, w a := by
      rw [← Fintype.sum_ite_mem Sf w]
      apply Finset.sum_congr rfl
      intro a _
      simp only [← hmem a, partitionWeight]
    rw [← Fintype.sum_ite_mem t (partitionWeight w T), Fintype.sum_sum_type, Fintype.sum_bool, hA]
    omega
  have hSplitS' := keySplit S' S hmemS
  have hSplitComp := keySplit S'ᶜ Sᶜ (fun a => by simp [Finset.mem_compl, hmemS a])
  have hSAcompl : (∑ a ∈ S, w a) + (∑ a ∈ Sᶜ, w a) = ∑ a, w a :=
    Finset.sum_add_sum_compl S w
  by_cases h1 : Sum.inr true ∈ S'
  · by_cases h2 : Sum.inr false ∈ S'
    · -- both dummies present: forces W = 0, so S works vacuously
      refine ⟨S, ?_⟩
      simp [h1, h2, Finset.mem_compl, partitionWeight] at hS' hSplitS' hSplitComp
      omega
    · -- only ⊤ present: S is the Subset Sum witness
      refine ⟨S, ?_⟩
      simp [h1, h2, Finset.mem_compl, partitionWeight] at hS' hSplitS' hSplitComp
      omega
  · by_cases h2 : Sum.inr false ∈ S'
    · -- only ⊥ present: the complement Sᶜ is the Subset Sum witness
      refine ⟨Sᶜ, ?_⟩
      simp [h1, h2, Finset.mem_compl, partitionWeight] at hS' hSplitS' hSplitComp
      omega
    · -- neither dummy present: forces W = 0, so S works vacuously
      refine ⟨S, ?_⟩
      simp [h1, h2, Finset.mem_compl, partitionWeight] at hS' hSplitS' hSplitComp
      omega

/-- Main theorem for reduction from Subset Sum to Partition.

Note the hypothesis `(h : T ≤ ∑ a, w a)`. Because Lean's natural numbers `ℕ`
do not support negative numbers (subtraction truncates at 0), we must assert
that the target `T` is not strictly greater than the total weight of all
items. (If it were, the Subset Sum would be trivially false anyway).
-/
theorem SubsetSumToPartitionReduction (w : U → ℕ) (T : ℕ)
    (h : T ≤ ∑ a, w a) :
    SubsetSum w T ↔ Partition (partitionWeight w T) :=
  Iff.intro
  (SubsetSumToPartitionCompleteness w T h)
  (SubsetSumToPartitionSoundness w T h)

end SubsetSumToPartition
