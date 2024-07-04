/-
Copyright (c) 2024 Shilun Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shilun Li
-/

import Mathlib.Logic.Equiv.Fin
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Finset.Basic
import Mathlib.Init.Set
import Mathlib.Tactic.Linarith

/-!
# Code Definitions

`Code n 𝔽`: a subset of 𝔽ⁿ.
`AsymptoticCodes 𝔽`: a map from ℕ to `Code n 𝔽`.

-/

open Set Filter Asymptotics Finset Linarith

namespace CodingTheory

-- variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
variable {α : Type*} [Fintype α] [DecidableEq α] -- the alphabet
variable {n k : ℕ}


/-- An element of 𝔽ⁿ. -/
abbrev Codeword (n : ℕ) (α : Type*) [Fintype α] [DecidableEq α] := (i : Fin n) → α


/-- Code `Code n 𝔽` is a subset of 𝔽ⁿ. -/
abbrev Code (n : ℕ) (α : Type*) [Fintype α] [DecidableEq α] := Finset (Codeword n α)


/-- AsymptoticCodes is a map from ℕ to `Code n 𝔽`. -/
-- def AsymptoticCodes (α : Type*) (S : Set ℕ) (hs : S.Infinite) [Fintype α] [DecidableEq α] :=  (n : S) → Code n α


def hamming_distance (c1 c2 : Codeword n α) : ℕ :=
  hammingDist c1 c2


/-- Perhaps add C.card >=2 --/
def distance (C : Code n α) (d : ℕ) : Prop :=
  (∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hamming_distance x y = d)∧ (∀ z ∈ C, ∀ w ∈ C, z ≠ w → hamming_distance z w ≥ d)

lemma dist_le_length (C : Code n α) (d : ℕ) (h : distance C d) : d <= n := by{
  rcases h with ⟨h1, _⟩
  rcases h1 with ⟨c₁, ⟨_, ⟨c₂, ⟨_, ⟨_, hdeq⟩⟩⟩⟩⟩
  have hle : hammingDist c₁ c₂ <= n
  · calc
      hammingDist c₁ c₂ <= Fintype.card (Fin n) := by exact hammingDist_le_card_fintype
      _                 = n                    := by rel[Fintype.card_fin n]
  dsimp [hamming_distance] at hdeq
  rw[hdeq] at hle
  exact hle
}

theorem singleton_bound (C : Code n α) (d : ℕ) (h : distance C d) (hα : Nontrivial α):
  C.card ≤ (Fintype.card α)^(n - d + 1) := by {
  by_cases h01: C.card = 0 ∨ C.card = 1
  · rcases h01 with h0|h1
    · rw[h0]
      exact Nat.zero_le (Fintype.card α ^ (n - d + 1))
    · rw[h1]
      have hcard : 0 < Fintype.card α
      · exact Fintype.card_pos
      have h' : n-d+1 >=1
      · linarith
      exact Nat.one_le_pow (n-d+1) (Fintype.card α) (hcard)


  by_contra h'
  push_neg at h' h01

  have h_two_le_card_C: 1 < C.card
  · exact (Nat.two_le_iff C.card).mpr h01

  have h_dist_le_length : d <= n
  · exact dist_le_length C d h

  have h_one_le_d : 1 <= d
  · by_contra h_d_le_one
    push_neg at h_d_le_one
    apply Nat.lt_one_iff.1 at h_d_le_one
    rcases h.1 with ⟨c₁, ⟨_, ⟨c₂, ⟨_, ⟨hneq, hdzero⟩⟩⟩⟩⟩
    rw[h_d_le_one] at hdzero
    dsimp [hamming_distance]at hdzero
    symm at hdzero
    apply hamming_zero_eq_dist.1 at hdzero
    tauto

  have h_n_gt_one : 1 <= n
  · calc
      n >= d := by exact dist_le_length C d h
      _ >= 1 := by exact h_one_le_d

  have hle : n - d + 1 <= n := by{
    calc
      n - d + 1 <= n - 1 + 1 := by rel[h_one_le_d]
              _  = n         := by exact Nat.sub_add_cancel h_n_gt_one
  }

  obtain ⟨_, h_hd_gt⟩ := h
  simp [Code, Codeword] at C

  let f : Codeword n α → Codeword (n-d+1) α := fun c ↦ (fun i ↦ c ((Fin.castLE hle) i))

  let K : (Finset (Codeword (n-d+1) α)) := Finset.univ
  have h_f_to_K : ∀ c ∈ C, f c ∈ K
  · intros c _
    simp

  have h_Kcard: K.card = Fintype.card α ^ (n- d + 1)
  · simp
    rw[Finset.card_univ]
    simp

  rw[← h_Kcard] at h'
  rcases Finset.exists_ne_map_eq_of_card_lt_of_maps_to h' h_f_to_K with ⟨c₁, ⟨hc₁_mem, ⟨c₂,⟨hc₂_mem, ⟨hc₁₂_neq, hc₁₂feq⟩⟩⟩⟩⟩
  simp [f] at hc₁₂feq
  specialize h_hd_gt c₁ hc₁_mem c₂ hc₂_mem hc₁₂_neq

  have h_card_complement : (filter (fun i => c₁ i = c₂ i) Finset.univ).card +
  (filter (fun i => ¬c₁ i = c₂ i) Finset.univ).card = n
  · dsimp[Finset.card]
    rw[← Multiset.card_add (Multiset.filter (fun i => c₁ i = c₂ i) Finset.univ.val) (Multiset.filter (fun i => ¬c₁ i = c₂ i) Finset.univ.val)]
    rw[Multiset.filter_add_not (fun i => c₁ i = c₂ i) Finset.univ.val]
    simp

  have h_card_eq_ge_d : (filter (fun i => c₁ i = c₂ i) Finset.univ).card >= n - d + 1
  · let S₁ : Finset (Fin n) := filter (fun i => i < n - d +1) Finset.univ
    have h_S_disj : Disjoint S₁ S₁ᶜ
    · exact disjoint_compl_right
    rw [← Finset.union_compl S₁]
    rw [Finset.filter_union]
    have h_filter_disj : Disjoint (filter (fun i => c₁ i = c₂ i) S₁) (filter (fun i => c₁ i = c₂ i) S₁ᶜ)
    · exact disjoint_filter_filter h_S_disj
    rw[Finset.card_union_eq h_filter_disj]

    have h_filter_eq_S₁ : filter (fun i => c₁ i = c₂ i) S₁ = S₁
    · ext i
      constructor
      · exact fun a => mem_of_mem_filter i a
      · simp
        intro hi
        constructor
        · exact hi
        · apply Function.funext_iff.1 at hc₁₂feq
          have h_cast_eq : i = Fin.castLE hle i
          · ext
            simp
            exact (Nat.mod_eq_of_lt hi).symm
          specialize hc₁₂feq i
          rw[h_cast_eq]
          exact hc₁₂feq

    have h_Scard : S₁.card = n - d + 1
    · apply Finset.card_eq_of_equiv_fin
      simp [Fin]
      apply Fintype.equivFinOfCardEq
      exact Fintype.card_fin_lt_of_le hle

    rw[h_filter_eq_S₁]
    rw[h_Scard]
    simp


  have h_hd_lt_d : hamming_distance c₁ c₂ < d
  · dsimp [hamming_distance, hammingDist]
    calc
      (filter (fun i => ¬c₁ i = c₂ i) Finset.univ).card = (filter (fun i => c₁ i = c₂ i) Finset.univ).card
                                                          + (filter (fun i => ¬c₁ i = c₂ i) Finset.univ).card
                                                          - (filter (fun i => c₁ i = c₂ i) Finset.univ).card  := by exact (Nat.add_sub_cancel_left (filter (fun i => c₁ i = c₂ i) Finset.univ).card (filter (fun i => ¬c₁ i = c₂ i) Finset.univ).card).symm
                                                      _ = n - (filter (fun i => c₁ i = c₂ i) Finset.univ).card:= by rw[h_card_complement]
                                                      _ <= n - (n - d + 1) := by rel[h_card_eq_ge_d]
                                                      _ = n - (n - d) - 1  := by rw[Nat.sub_sub]
                                                      _ = d - 1            := by rw[Nat.sub_sub_self h_dist_le_length]
                                                      _ < d                := by exact Nat.sub_lt h_one_le_d Nat.zero_lt_one

  apply Nat.lt_le_asymm at h_hd_lt_d
  tauto
}



theorem hamming_bound (C : Code n α) (d : ℕ) : C.card ≤ (Fintype.card α)^n / Finset.sum (Finset.range (d + 1)) (λ i=> Nat.choose n i * (q - 1)^i) :=
  sorry
All Messages (2)
