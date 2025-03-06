/-
Copyright (c) 2024 Shilun Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shilun Li
-/
import Mathlib.Logic.Equiv.Fin
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Init.Set
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finmap
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Rank
import Mathlib.Probability.ProbabilityMassFunction.Uniform
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Code Definitions

`Code n 𝔽`: a subset of 𝔽ⁿ.
`AsymptoticCodes 𝔽`: a map from ℕ to `Code n 𝔽`.

-/

open Set Filter Asymptotics Finset Linarith

namespace CodingTheory

-- variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
variable {α : Type*} [Fintype α] [DecidableEq α] [Field α]-- the alphabet
variable {n k : ℕ}


/-- An element of 𝔽ⁿ. -/
abbrev Codeword (n : ℕ) (α : Type*) [Fintype α] [DecidableEq α] := (i : Fin n) → α

namespace Codeword

@[simp]
def add (c₁ c₂ : Codeword n α) : Codeword n α := fun i ↦ (c₁ i + c₂ i)

@[simp]
def sub (c₁ c₂ : Codeword n α) : Codeword n α := fun i ↦ (c₁ i - c₂ i)

@[simp]
def zero : Codeword n α := fun (_ : Fin n) ↦ 0


/-- Code `Code n 𝔽` is a subset of 𝔽ⁿ. -/
abbrev Code (n : ℕ) (α : Type*) [Fintype α] [DecidableEq α] := Finset (Codeword n α)

/-- Linear Code as a `Code n 𝔽` with a Generator Matrix. -/
def Linear_Code (C : Code n α) (G : Matrix (Fin n) (Fin m) α) := (∀ c' : Codeword m α, Matrix.mulVec G c' ∈ C) ∧ (∀ c ∈ C, ∃ c' : Codeword m α, c = Matrix.mulVec G c')

def Linear_Code' (C : Code n α) (m : ℕ) := ∃ (G : Matrix (Fin n) (Fin m) α), (∀ c' : Codeword m α, Matrix.mulVec G c' ∈ C) ∧ (∀ c ∈ C, ∃ c' : Codeword m α, c = Matrix.mulVec G c')

noncomputable def qaryEntropy (q : ℕ) (p : ℝ) := p * (Real.logb q (q-1)) - p * (Real.logb q p) - (1-p)*(Real.logb q (1 -p))

/-- AsymptoticCodes is a map from ℕ to `Code n 𝔽`. -/
-- def AsymptoticCodes (α : Type*) (S : Set ℕ) (hs : S.Infinite) [Fintype α] [DecidableEq α] :=  (n : S) → Code n α


def hamming_distance (c1 c2 : Codeword n α) : ℕ :=
  hammingDist c1 c2


/-- Perhaps add C.card >=2 --/
def distance (C : Code n α) (d : ℕ) : Prop :=
  (∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hamming_distance x y = d)∧ (∀ z ∈ C, ∀ w ∈ C, z ≠ w → hamming_distance z w ≥ d)

def weight (c: Codeword n α) : ℕ := hamming_distance c 0


def max_size (n d A : ℕ) : Prop :=
  ∃ C : Code n α, (distance C d ∧ (C.card = A) ∧ (∀ c : Code n α, distance c d → c.card ≤ C.card))


lemma dist_le_length (C : Code n α) (d : ℕ) (h : distance C d) : d <= n := by {
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

theorem singleton_bound (C : Code n α) (d : ℕ) (h : distance C d) (hα : Nontrivial α) :
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

@[simp]
def hamming_ball (l : ℕ) (c : Codeword n α) : Finset (Codeword n α) := {c' : Codeword n α | hamming_distance c' c ≤ l}.toFinset
set_option maxHeartbeats 1000000





theorem hamming_ball_size (n l : ℕ ): ∀ c : Codeword n α, (hamming_ball l c).card = (Finset.sum (Finset.range (l + 1)) (λ i=> Nat.choose n i * (Fintype.card α - 1)^i)) := by {
  intro c
  simp
  rw[Set.toFinset_card]

  have h_card_x0 : ∀ d, {c' : Codeword n α | hamming_distance c' Codeword.zero = d}.toFinset.card = Nat.choose n d * (Fintype.card α - 1)^d
  · intro d
    dsimp [hamming_distance, zero]
    -- rw[toFinset_card]
    -- simp [hammingDist]

    let d_comb : Finset (Finset (Fin n)) := Finset.powersetCard d Finset.univ
    have h_card_d_comb : d_comb.card = Nat.choose n d
    · simp

    let α_nonzero := {x : α | x ≠ 0}.toFinset
    have h_card_α_nonzero : α_nonzero.card = Fintype.card α - 1
    · rw[toFinset_card]
      simp

    have h_card_fun : ∀ s ∈ d_comb, Fintype.card (s → α_nonzero) = (Fintype.card α - 1)^d
    · intro s hs
      rw[Fintype.card_fun]
      have : Fintype.card { x // x ∈ α_nonzero } = Fintype.card α - 1
      · simp
      rw[this]
      simp at *
      rw[hs]





    let f := fun (s : Finset (Fin n)) ↦ (Finset.univ : Finset (s → α_nonzero))

    have : ∀ s ∈ d_comb, (f s).card = (Fintype.card α - 1)^d
    · intro s hs
      simp
      exact h_card_fun s hs

    let S := d_comb.sigma f
    have h_card_S : S.card = Nat.choose n d * (Fintype.card α - 1) ^ d
    · simp
      rw[Finset.sum_eq_card_nsmul this, h_card_d_comb]
      rfl


    rw[←h_card_S]
    let f' : (s : ((k : Finset (Fin n)) × ({ x // x ∈ k } → { x // x ∈ α_nonzero }))) → s ∈ S → Codeword n α := fun s _ ↦ (fun i ↦ if h : i ∈ s.1 then s.2 ⟨i, h⟩ else 0)

    symm
    apply Finset.card_congr f'

    -- f' maps S to the hamming ball
    have h_f'_map_to_ball: ∀ (a : (k : Finset (Fin n)) × ({ x // x ∈ k } → { x // x ∈ α_nonzero })) (ha : a ∈ S), f' a ha ∈ toFinset {c' | hammingDist c' zero = d}
    · intros a ha
      apply Finset.mem_sigma.1 at ha
      rw[toFinset]
      simp [hammingDist]
      have : (filter (fun i => i ∈ a.fst) Finset.univ).card = d
      · simp at *
        exact ha

      rw[← this]
      rw[← Fintype.card_subtype]
      simp
      apply Fintype.card_of_subtype
      intros x
      constructor
      · intro hx
        use hx
        have : ↑(a.snd ⟨x, hx⟩) ∈  α_nonzero
        · exact coe_mem (Sigma.snd a { val := x, property := hx })
        simp at this
        exact this
      · intros hx
        rcases hx with ⟨h₁, h₂⟩
        exact h₁

    exact h_f'_map_to_ball

    -- f' is injective
    have h_f'_injective: ∀ (a b : (k : Finset (Fin n)) × ({ x // x ∈ k } → { x // x ∈ α_nonzero })) (ha : a ∈ S) (hb : b ∈ S), f' a ha = f' b hb → a = b
    · intros a b h_a h_b
      intro h_feq
      let f_a := (f' a h_a)
      let f_b := (f' b h_b)
      have fab_eq: f_a = f_b := by exact h_feq

      have first_eq: a.1 = b.1
      · ext x
        constructor
        · intro h1
          by_contra h_xb
          have h_fbzero: f_b x = 0 := by simp; intro h_inb; exact absurd h_inb h_xb
          have h_fazero: f_a x = 0 := by rw[fab_eq]; exact h_fbzero
          simp at h_fazero
          let a₀ := a.2 ⟨x, h1⟩
          apply h_fazero at h1
          have h_azero : ¬a₀.val ≠ 0 := by simp; exact h1
          have h_anonzero : a₀.val ∈ α_nonzero := by exact a₀.property
          rw [Set.mem_toFinset, Set.mem_setOf] at h_anonzero
          exact absurd h_anonzero h_azero
        · intro h2
          by_contra h_xa
          have h_fazero: f_a x = 0 := by simp; intro h_ina; exact absurd h_ina h_xa
          have h_fbzero: f_b x = 0 := by rw[←fab_eq]; exact h_fazero
          simp at h_fbzero
          let b₀ := b.2 ⟨x, h2⟩
          apply h_fbzero at h2
          have h_bzero : ¬b₀.val ≠ 0 := by simp; exact h2
          have h_bnonzero : b₀.val ∈ α_nonzero := by exact b₀.property
          rw [Set.mem_toFinset, Set.mem_setOf] at h_bnonzero
          exact absurd h_bnonzero h_bzero

      have h_2eq : ({ x // x ∈ b.fst } → { x // x ∈ α_nonzero }) = ({ x // x ∈ a.fst } → { x // x ∈ α_nonzero })
      · rw[first_eq]

      let b' := cast h_2eq b.2
      have h_bheq : HEq b' b.2 := by simp

      ext
      rw[first_eq]
      refine HEq.symm (heq_of_cast_eq h_2eq ?h_f'_injective.a.x)
      funext x
      suffices b' x = a.snd x by {
        exact this
      }

      have h₁' : f_a x = a.2 x
      · simp

      have h₂ : (f_a x) = (f_b x)
      ·  rw[fab_eq]

      have h₃ : (f_b x) = (b' x)
      ·
        have h₃' : ↑x ∈ b.1
        · have h₃'' : ↑x ∈ a.1 := by simp
          rw[← first_eq]
          exact h₃''

        simp[h₃']

        have : Sigma.snd b { val := ↑x, property := (h₃' : ↑x ∈ b.fst) } = b' x
        · simp
          apply congr_heq -- Life Saving Theorem
          exact h_bheq.symm
          refine (Subtype.heq_iff_coe_eq ?this.h₂.h).mpr rfl
          rw[first_eq]
          tauto

        exact congrArg Subtype.val this


      rw[h₃] at h₂
      rw[h₂] at h₁'
      exact SetCoe.ext h₁'

    exact h_f'_injective

    -- f' is surjective
    have h_f'_surjective: ∀ b ∈ toFinset {c' | hammingDist c' zero = d}, ∃ a, ∃ (ha : a ∈ S), f' a ha = b
    · intro b
      intro h_b
      let a₁ := toFinset { i | b i ≠ 0 }

      have h_y : ∀ y ∈ a₁, (b ↑y) ∈ α_nonzero := by simp

      let a₂ (y : { x // x ∈ a₁ }) : { x // x ∈ α_nonzero } := ⟨b y, by {
        apply h_y
        exact y.property
      }⟩

      use ⟨a₁, a₂⟩

      have h_a : ⟨a₁, a₂⟩ ∈ S
      · simp
        have h_d : hammingDist b zero = d
        · rw[Set.mem_toFinset, Set.mem_setOf] at h_b
          exact h_b
        unfold hammingDist at h_d
        have h_setEq : (toFinset {i | ¬b i = 0}) = (filter (fun i => b i ≠ zero i) Finset.univ)
        · simp
          apply Finset.ext
          intro t
          constructor
          · intro h₁
            have h₁' : ¬b t = 0
            · rw[Set.mem_toFinset, Set.mem_setOf] at h₁
              exact h₁
            simp
            exact h₁'
          · intro h₂
            contrapose h₂
            rw[Set.mem_toFinset, Set.mem_setOf] at h₂
            simp at h₂
            simp[h₂]

        rw[h_setEq]
        exact h_d

      use h_a
      simp
      funext x

      by_cases h_x : b x = 0
      · simp
        intro h'
        rw[h_x]
      · simp
        intro h'
        by_contra h_x
        have h_xb : x ∈ toFinset {i | ¬b i = 0}
        · apply Set.mem_toFinset.2
          simp
          contrapose h_x
          simp at h_x
          simp
          rw[h_x]
        exact absurd h_xb h'



    exact h_f'_surjective




  have h_card_dist_eq : ∀ d, {c' : Codeword n α | hamming_distance c' c = d}.toFinset.card = Nat.choose n d * (Fintype.card α - 1)^d
  · intro d
    rw[← h_card_x0]
    let f : Codeword n α → Codeword n α := fun x ↦ sub x c
    apply Finset.card_congr (fun a _ ↦ f a)
    simp [toFinset]
    dsimp [toFinset]
    simp
    · intros a ha
      dsimp [hamming_distance, sub] at *
      rw[hammingDist_eq_hammingNorm] at ha
      exact ha
    · intros a b ha hb hfab
      simp [toFinset] at *
      ext i
      apply Function.funext_iff.1 at hfab
      specialize hfab i
      simp at hfab
      exact hfab
    · intros b hb
      use add b c
      simp [toFinset, hamming_distance] at *
      dsimp [toFinset] at *
      simp at *
      constructor
      · rw[hammingDist_eq_hammingNorm]
        have : add b c - c = b
        · ext i
          simp
        rw[this]
        exact hb
      · ext i
        simp




  induction' l with d ih
  · simp [hamming_distance]
  · simp
    rw[Nat.succ_add]
    rw[Finset.sum_range_succ]
    rw[← ih]
    simp
    rw[Nat.succ_eq_add_one]
    have : Fintype.card { x // hamming_distance x c ≤ d + 1 } = Fintype.card { x // hamming_distance x c ≤ d } + Fintype.card { x // hamming_distance x c = d + 1}
    · have : fun x ↦ hamming_distance x c ≤ d + 1 = fun x ↦ hamming_distance x c ≤ d ∨ hamming_distance x c = d + 1
      · ext x
        constructor
        · intros h_d1
          apply Nat.eq_or_lt_of_le at h_d1
          rcases h_d1 with hl | hr
          right
          exact hl
          left
          linarith
        · intros h_or
          rcases h_or with hl | hr
          linarith
          linarith

      have : {x // hamming_distance x c ≤ d + 1} = {x // hamming_distance x c ≤ d ∨ hamming_distance x c = d + 1 }
      · exact congrArg Subtype this

      have : Fintype.card {x // hamming_distance x c ≤ d + 1} = Fintype.card {x // hamming_distance x c ≤ d ∨ hamming_distance x c = d + 1 }
      · exact Fintype.card_congr' this

      rw[this]

      have : Disjoint (fun x ↦ hamming_distance x c ≤ d)  (fun x ↦ hamming_distance x c = d + 1)
      · apply Pi.disjoint_iff.2
        intros c'
        simp
        intro hc'
        linarith


      apply Fintype.card_subtype_or_disjoint
      exact this


    rw[this]
    simp
    have : {c' : Codeword n α | hamming_distance c' c = d + 1}.toFinset.card = Nat.choose n (d+1) * (Fintype.card α - 1)^(d + 1)
    · exact h_card_dist_eq (d + 1)

    rw[Set.toFinset_card] at this
    simp at this
    linarith
}

lemma hamming_ball_size_asymptotic (q n : ℕ) (p : ℝ) (hq : q = Fintype.card α) (hα : Nontrivial α) (hnp : (Nat.floor (n*p)) = n*p) (hp : 0 < p ∧ p ≤ 1 - 1/q):
∀ c : Codeword n α, (hamming_ball (Nat.floor (n*p)) c).card ≤ Real.rpow q ((qaryEntropy q p) * n) := by {
  intro c
  rw[hamming_ball_size]
  rw[← hq]
  have : 0 < Real.rpow q ((qaryEntropy q p) * n)
  · apply Real.rpow_pos_of_pos
    rw[hq]
    simp
    exact Fintype.card_pos
  apply (div_le_one this).1
  simp
  dsimp[qaryEntropy]

  -- Using sub lemmas
  have hq₁ : (0 : ℝ) < ↑q
  · rw[hq]
    simp
    exact Fintype.card_pos

  have hq₂ : (0 : ℝ) ≤ ↑q - 1
  · simp
    rw[hq]
    exact Nat.one_le_of_lt Fintype.card_pos

  have hq₃ : (0 : ℝ) < ↑q - 1
  · simp
    rw[hq]
    exact Fintype.one_lt_card

  have h₁ : 0 < 1 - p
  · suffices p < 1 by exact sub_pos.mpr this
    calc
      p ≤ 1 - 1/↑q               := by exact hp.2
      _ = 1 - 1/(Fintype.card α) := by rw[hq]
      _ < 1                      := by exact sub_lt_self 1 (one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero Fintype.card_ne_zero)))
  have hp₂ : p < 1
  · linarith

  rw[div_eq_mul_inv, ← Real.rpow_neg]
  have : -((p * Real.logb (↑q) (↑q - 1) - p * Real.logb (↑q) p - (1 - p) * Real.logb (↑q) (1 - p)) * ↑n) =
          (Real.logb (↑q) (↑q - 1)) * (-p * ↑n) + (Real.logb (↑q) p) * (p * ↑n) + (Real.logb (↑q) (1 - p)) * ((1-p) * ↑n)
  · linarith
  rw[this]

  rw[Real.rpow_add, Real.rpow_add, Real.rpow_mul, Real.rpow_logb, Real.rpow_mul, Real.rpow_mul, Real.rpow_mul,Real.rpow_mul]
  rw[Real.rpow_logb, Real.rpow_logb]
  rw[← Real.rpow_mul, ← Real.rpow_mul]
  rw[Finset.sum_mul]


  simp

-- Doing all the algebra
  have h_alg1 : ∀ x, ↑(Nat.choose n x) * ↑(q - 1) ^ x * ((↑q - 1) ^ (-(p * ↑n)) * p ^ (p * ↑n) * (1 - p) ^ ((1 - p) * ↑n)) =
  ↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p/((q-1)*(1-p)))^(p*↑n)
  · intro x
    rw[one_sub_mul, sub_eq_add_neg ↑n (p * ↑n)]
    rw[Real.rpow_add h₁, ← mul_assoc, ← Real.rpow_nat_cast]
    calc
      ↑(Nat.choose n x) * ↑(q - 1) ^ (x :ℝ) * ((↑q - 1) ^ (-(p * ↑n)) * p ^ (p * ↑n)) * ((1 - p) ^ (n : ℝ) * (1 - p) ^ (-(p * ↑n))) =
      ↑(Nat.choose n x) * ↑(q - 1) ^ (x : ℝ) * (1 - p) ^ (n : ℝ) * ((((1 - p) ^(-(p * ↑n)) * (↑q - 1) ^ (-(p * ↑n)))) * p ^ (p * ↑n)) := by linarith
      _ = ↑(Nat.choose n x) * ↑(q - 1) ^ (x : ℝ) * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ (p * ↑n) := by {
        rw[← Real.mul_rpow]
        rw[Real.rpow_neg, ← Real.inv_rpow]
        rw[← Real.mul_rpow]
        rw[← div_eq_inv_mul]
        ring
        · apply inv_nonneg.2
          apply mul_nonneg
          exact le_of_lt h₁
          exact hq₂
        · linarith
        · exact (zero_le_mul_left h₁).mpr hq₂
        · exact (zero_le_mul_left h₁).mpr hq₂
        · exact le_of_lt h₁
        · exact hq₂
      }

  have h_alg_2 : ∀ x ∈ (Finset.range (⌊↑n * p⌋₊ + 1)), ↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ (p * ↑n) ≤ (↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ x)
  · intros x hx
    suffices (p / ((↑q - 1) * (1 - p))) ^ (p * ↑n) ≤ (p / ((↑q - 1) * (1 - p))) ^ x by {
      calc
        ↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ (p * ↑n) =
        (↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ)) * (p / ((↑q - 1) * (1 - p))) ^ (p * ↑n) := by linarith
        _ ≤ (↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ x) := by rel[this]
    }
    simp at hx
    have : 0 < (p / ((↑q - 1) * (1 - p))) ∧ (p / ((↑q - 1) * (1 - p))) ≤ 1
    · constructor
      · apply div_pos
        linarith[hp.1]
        apply mul_pos
        exact hq₃
        linarith[h₁]
      · suffices p / (q - 1) ≤ 1 - p by {
          rw[← div_div]
          apply (div_le_one h₁).2
          exact this
        }
        calc
          p / (↑q - 1) ≤ 1/q := by {
            apply (div_le_iff hq₃).2
            rw[mul_sub]
            simp
            simp at hp
            rw[inv_mul_cancel]
            exact hp.2
            exact ne_of_gt hq₁
          }
          _ ≤ 1 - p := by linarith

    have h_x_le_pn : x ≤ p * n
    · have : 0 ≤ n*p
      · apply mul_nonneg
        exact Nat.cast_nonneg n
        linarith[hp.1]
      rw[mul_comm]
      apply (Nat.le_floor_iff this).1
      exact Nat.lt_succ.mp hx

    rw[← Real.rpow_nat_cast]
    apply Real.rpow_le_rpow_of_exponent_ge this.1 this.2 h_x_le_pn



  calc
      (Finset.sum (Finset.range (⌊↑n * p⌋₊ + 1)) fun x =>
    ↑(Nat.choose n x) * ↑(q - 1) ^ x * ((↑q - 1) ^ (-(p * ↑n)) * p ^ (p * ↑n) * (1 - p) ^ ((1 - p) * ↑n))) =  (Finset.sum (Finset.range (⌊↑n * p⌋₊ + 1)) fun x =>
    ↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p/((q-1)*(1-p)))^(p*↑n)) := by {
      apply Finset.sum_congr
      rfl
      intro x hx
      exact h_alg1 x
    }
    _ ≤ (Finset.sum (Finset.range (⌊↑n * p⌋₊ + 1)) fun x => (↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ x)) := by {
      apply Finset.sum_le_sum
      intros i hi
      exact h_alg_2 i hi
    }
    _ ≤ (Finset.sum (Finset.range (n + 1)) fun x => (↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ (n : ℝ) * (p / ((↑q - 1) * (1 - p))) ^ x)) := by {
      apply Finset.sum_le_sum_of_subset_of_nonneg

      apply range_subset.2
      simp
      apply Nat.floor_le_of_le
      calc
        ↑n * p ≤ ↑n * 1 := by exact mul_le_mul_of_nonneg_left (le_of_lt hp₂) (Nat.cast_nonneg n)
        _      ≤ ↑n     := by simp
      intros i _ _
      apply mul_nonneg
      apply mul_nonneg
      apply mul_nonneg
      simp
      simp
      simp
      exact pow_nonneg (le_of_lt h₁) n
      apply pow_nonneg
      apply div_nonneg
      exact le_of_lt hp.1
      apply mul_nonneg
      exact hq₂
      exact le_of_lt h₁
    }
    _ = Finset.sum (Finset.range (n + 1)) fun x => (↑(Nat.choose n x) * p ^ x * (1 - p) ^ ((n : ℝ) - x)) := by{
      apply Finset.sum_congr
      rfl
      intros x hx
      simp at hx
      apply Nat.lt_succ.1 at hx
      field_simp
      rw[mul_pow, ←mul_assoc]
      symm
      calc
        ↑(Nat.choose n x) * p ^ x * (1 - p) ^ ((n:ℝ) - (x:ℝ)) * (↑q - 1) ^ x * (1 - p) ^ x =
        ↑(Nat.choose n x) * (↑q - 1) ^ x * ((1 - p) ^ ((n:ℝ) - (x:ℝ)) * (1 - p) ^ x) * p ^ x := by linarith
        _ = ↑(Nat.choose n x) * (↑q - 1) ^ x * ((1 - p) ^ (n - x) * (1 - p) ^ x) * p ^ x := by rw[←Nat.cast_sub hx, Real.rpow_nat_cast]
        _ = ↑(Nat.choose n x) * (↑q - 1) ^ x * (1 - p) ^ n * p ^ x := by rw[←pow_add, Nat.sub_add_cancel hx]
        _ = ↑(Nat.choose n x) * ↑(q - 1) ^ x * (1 - p) ^ n * p ^ x := by {
          simp
          left
          left
          left
          rw[Nat.cast_sub]
          simp
          rw[hq]
          exact Nat.one_le_of_lt Fintype.card_pos
        }




    }
    _ = Finset.sum (Finset.range (n + 1)) fun x => (p ^ x * (1 - p) ^ (n - x) * ↑(Nat.choose n x)) := by {
      apply Finset.sum_congr
      rfl
      intros x hx
      simp at hx
      apply Nat.lt_succ.1 at hx
      rw[←Nat.cast_sub hx, Real.rpow_nat_cast]
      linarith
    }
    _ = 1 := by {
      rw[← add_pow p (1-p) n]
      simp
    }

  -- More algebras on ineqaulities
  exact le_of_lt hp.1
  exact hq₂
  exact hq₁
  linarith[hq₃]
  exact h₁
  exact hq₁
  linarith[hq₃]
  exact hp.1
  exact le_of_lt hq₁
  rw[Real.rpow_logb]
  exact le_of_lt hp.1
  exact hq₁
  linarith[hq₃]
  exact hp.1
  linarith[hq₁]
  exact hq₂
  exact hq₁
  linarith[hq₃]
  exact hq₃
  linarith[hq₁]
  exact hq₁
  exact hq₁
  linarith[hq₁]
}

lemma hamming_ball_non_intersect (C : Code n α) (h : distance C d) (h' : 0 < d): ∀ c₁ c₂ : Codeword n α, (c₁ ∈ C ∧ c₂ ∈ C ∧ c₁ ≠ c₂) → ∀ c' : Codeword n α, c' ∈ (hamming_ball (Nat.floor (((d : ℝ)-1)/2)) c₁) → c' ∉  (hamming_ball (Nat.floor (((d : ℝ)-1)/2)) c₂) := by {
  intros c₁ c₂ hc₁₂ c' hc'

  dsimp [hamming_ball, hamming_distance] at *

  have h_dist_c₁₂ : hamming_distance c₁ c₂ ≥ d
  · exact h.2 c₁ hc₁₂.1 c₂ hc₁₂.2.1 hc₁₂.2.2

  have h_dist_c₁' : (hamming_distance c₁ c') ≤ (Nat.floor (((d : ℝ)-1)/2))
  · apply Set.mem_toFinset.1 at hc'
    simp at hc'
    rw[hammingDist_comm c' c₁] at hc'
    exact hc'

  by_contra h_dist_c'₂
  apply Set.mem_toFinset.1 at h_dist_c'₂
  simp at h_dist_c'₂

  have : (Nat.floor (((d : ℝ)-1)/2)) ≤ ((d : ℝ)-1)/2
  · apply Nat.floor_le
    apply div_nonneg
    simp
    exact h'
    linarith

  have : (Nat.floor (((d : ℝ)-1)/2)) + (Nat.floor (((d : ℝ)-1)/2)) ≤ ((d - (1 : ℕ) ) : ℝ)
  · simp
    linarith


  have : ((Nat.floor (((d : ℝ)-1)/2)) + (Nat.floor (((d : ℝ)-1)/2))) < d
  · suffices (Nat.floor (((d : ℝ)-1)/2)) + (Nat.floor (((d : ℝ)-1)/2)) ≤ d - 1 by {
      exact Nat.lt_of_le_pred h' this
    }
    rw[← Nat.cast_sub] at this
    rw[← Nat.cast_add] at this
    exact Nat.cast_le.1 this
    linarith





  have h_cont : hamming_distance c₁ c₂ < d
  · simp [hamming_distance] at *
    calc
      hammingDist c₁ c₂ ≤ hammingDist c₁ c' + hammingDist c' c₂ := by exact hammingDist_triangle c₁ c' c₂
      _                 ≤ (Nat.floor (((d : ℝ)-1)/2)) + (Nat.floor (((d : ℝ)-1)/2))    := by linarith [h_dist_c₁', h_dist_c'₂]
      _                 < d                                     := by linarith[this]


  linarith



}

lemma hamming_ball'_disjoint (C : Code n α) (h : distance C d) (h' : 0 < d) : ∀ c₁ c₂ : Codeword n α, (c₁ ∈ C ∧ c₂ ∈ C ∧ c₁ ≠ c₂) → Disjoint (hamming_ball (Nat.floor (((d : ℝ) - 1)/2)) c₁) (hamming_ball (Nat.floor (((d : ℝ)-1)/2)) c₂) := by {
  intros c₁ c₂ hc₁₂
  dsimp [hamming_ball]
  apply Set.disjoint_toFinset.2
  apply Set.disjoint_iff.2
  intros c' hc'
  simp at *
  rcases hc' with ⟨hc'₁, hc'₂⟩
  have : c' ∈ (hamming_ball (Nat.floor (((d : ℝ)-1)/2)) c₁)
  · dsimp [hamming_ball]
    apply Set.mem_toFinset.2
    simp
    exact hc'₁

  apply hamming_ball_non_intersect C h h' c₁ c₂ hc₁₂ c'
  exact this
  simp
  apply Set.mem_toFinset.2
  simp
  exact hc'₂
}


theorem hamming_bound (n d A : ℕ) (C : Code n α) (h : distance C d) (h' : Fintype.card α = q) (h'' : Fintype.card α >1)(hd : 0 < d):
C.card ≤ Fintype.card α ^ n / (Finset.sum (Finset.range ((Nat.floor (((d : ℝ)-1)/2)) + 1)) (λ i=> Nat.choose n i * (Fintype.card α - 1)^i)) := by {
  have h1 : 0 < Finset.sum (Finset.range ((Nat.floor (((d : ℝ)-1)/2)) + 1)) (λ i=> Nat.choose n i * (Fintype.card α - 1)^i)
  · apply Finset.sum_pos
    intros i hi
    apply mul_pos
    · apply Nat.choose_pos
      have : (Nat.floor (((d : ℝ)-1)/2)) + 1 ≤ d
      · suffices (Nat.floor (((d : ℝ)-1)/2)) ≤ d - 1 by exact Nat.add_le_of_le_sub hd this
        suffices (Nat.floor (((d : ℝ)-1)/2)) ≤ ((d - (1 : ℕ) ) : ℝ) by{
          rw[← Nat.cast_sub] at this
          exact Nat.cast_le.1 this
          exact hd
        }
        calc
          (Nat.floor (((d : ℝ)-1)/2)) ≤ ((d : ℝ)-1)/2        := by {
            apply Nat.floor_le
            apply div_nonneg
            simp
            exact hd
            linarith
          }
          _                           ≤ ((d - (1 : ℕ) ) : ℝ) := by {
            simp
            linarith
          }
      calc
        i ≤ ((Nat.floor (((d : ℝ)-1)/2)) + 1)  := by linarith [Finset.mem_range.1 hi]
        _ ≤ d  := by exact this
        _ ≤ n  := by exact dist_le_length C d h
    · apply Nat.pos_pow_of_pos
      simp
      exact h''
    simp


  suffices C.card * (Finset.sum (Finset.range ((Nat.floor (((d : ℝ)-1)/2)) + 1)) (λ i=> Nat.choose n i * (Fintype.card α - 1)^i)) ≤ Fintype.card α ^ n by exact (Nat.le_div_iff_mul_le h1).mpr this

  let S : Finset (Codeword n α) := Finset.univ
  have h_Scard: S.card = Fintype.card α ^ n
  · simp
    rw[Finset.card_univ]
    simp



  have h_disjoint : (C.toSet).PairwiseDisjoint (fun c ↦ (hamming_ball (Nat.floor (((d:ℝ)-1)/2)) c))
  · intros x hx y hy hxy
    simp at hx hy
    exact hamming_ball'_disjoint C h hd x y ⟨hx, hy, hxy⟩

  let SU : Finset (Codeword n α) := Finset.disjiUnion C (fun c ↦ (hamming_ball (Nat.floor (((d:ℝ)-1)/2)) c)) h_disjoint


  have h_SUcard : SU.card = C.card * (Finset.sum (Finset.range ((Nat.floor (((d : ℝ)-1)/2)) + 1)) (λ i=> Nat.choose n i * (Fintype.card α - 1)^i))
  · rw[Finset.card_disjiUnion]
    apply Finset.sum_eq_card_nsmul
    exact fun a a_1 => hamming_ball_size n (Nat.floor (((d : ℝ)-1)/2)) a

  calc
    (C.card * Finset.sum (Finset.range ((Nat.floor (((d : ℝ)-1)/2)) + 1)) fun i => Nat.choose n i * (Fintype.card α - 1) ^ i) = SU.card := by exact h_SUcard.symm
    _                                                                                                            ≤ S.card  := by exact Finset.card_le_univ SU
    _                                                                                                            = Fintype.card α ^ n   := by exact h_Scard


}

lemma Linear_Code_dist_eq_min_weight (C : Code n α) (h_linear : Linear_Code' C m) (h : distance C d) :
 (∀c ∈ C, c ≠ 0 → weight c ≥ d) ∧ (∃c ∈ C, weight c = d):= by {
  rcases h_linear with ⟨G, hG⟩
  constructor
  · intros c hc c_nzero
    simp [weight]
    apply h.2 c hc 0
    rcases hG with ⟨hG_image, hG_preimage⟩
    specialize hG_image 0
    simp at hG_image
    exact hG_image
    exact c_nzero
  · rcases h.1 with ⟨c₁, ⟨hc₁, c₂, ⟨hc₂, ⟨hc₁₂neq, hc₁₂dist_eq_d⟩⟩⟩⟩
    use c₁ - c₂
    rcases hG with ⟨hG_image, hG_preimage⟩
    apply hG_preimage at hc₁
    apply hG_preimage at hc₂
    rcases hc₁ with ⟨c₁', hc₁'⟩
    rcases hc₂ with ⟨c₂', hc₂'⟩
    constructor
    · rw[hc₁', hc₂']
      rw[sub_eq_add_neg, ← Matrix.mulVec_neg, ← Matrix.mulVec_add, ← sub_eq_add_neg]
      exact hG_image (c₁' - c₂')
    · rw[← hc₁₂dist_eq_d]
      simp [hamming_distance, weight]
      exact (hammingDist_eq_hammingNorm c₁ c₂).symm
}



-- Uniform distribution on length-n vectors. Function from vectors to probabilities
noncomputable def uniform_vector_dist (n : ℕ) (α : Type*) [Fintype α] [DecidableEq α]: (Codeword n α) → ℝ :=
  fun _ => 1 / ((Fintype.card α) ^ n)

-- Theorem saying that the set of matrices G satisfying Gx = v is finite
theorem finite_matrix_dist (n k : ℕ) (v : Codeword n α) (x : Codeword k α) :
Set.Finite { G : Matrix (Fin n) (Fin k) α | Matrix.mulVec G x = v } := by {

  have dist_subset : { G : Matrix (Fin n) (Fin k) α | Matrix.mulVec G x = v } ⊆ (Set.univ : Set (Matrix (Fin n) (Fin k) α))
  · simp

  have matrices_fintype : Finite ↑{G | Matrix.mulVec G x = v}
  · exact Finite.Set.subset (Set.univ : Set (Matrix (Fin n) (Fin k) α)) dist_subset

  exact (Set.finite_coe_iff.mp matrices_fintype)
}



-- Measure on length-n vectors v defined by the proportion of matrices G that satisfy Gx = v
noncomputable def matrix_dist (n k : ℕ) (x : Codeword k α) : (Codeword n α) → ℝ :=
fun v => (Set.Finite.toFinset (finite_matrix_dist n k v x)).card / ((Fintype.card α) ^ (n * k))



-- Utility function to get a matrix representation of a row of a matrix
def get_matrix_row (n k : ℕ) (M : Matrix (Fin n) (Fin k) α) (i : Fin n) : Matrix (Fin 1) (Fin k) α :=
Matrix.of (fun _ j => (M i) j)



-- Actual lemma stating that Gx is uniformly distributed
theorem uniformity_lemma (n k : ℕ) (x : Codeword k α) (h_x : x ≠ 0) (h_k : k ≥ 1) :
matrix_dist n k x = uniform_vector_dist n α := by {

  unfold matrix_dist uniform_vector_dist
  funext v
  simp
  field_simp

  have h : (filter (fun G => Matrix.mulVec G x = v) Finset.univ).card = (Fintype.card α)^(n * (k-1))
  · -- Says that the amount of matrices G such that Gx = v is equal to the amount of matrices G such that
    -- for each row G_i, G_ix = v_i
    have h2 : (fun G => Matrix.mulVec G x = v) = (fun G => ∀i, Matrix.mulVec (get_matrix_row n k G i) x = fun _ => v i)
    · funext G
      apply propext
      apply Iff.intro
      · intro h_G i
        funext x'
        unfold get_matrix_row Matrix.mulVec Matrix.dotProduct
        simp
        unfold Matrix.mulVec Matrix.dotProduct at h_G
        simp at h_G
        exact congrFun h_G i
      · intro h_g
        unfold Matrix.mulVec Matrix.dotProduct
        simp
        unfold get_matrix_row Matrix.mulVec Matrix.dotProduct at h_g
        simp at h_g
        funext x₀
        have h_g' : (fun x_1 => Finset.sum Finset.univ fun x_2 => G x₀ x_2 * x x_2) = fun x => v x₀
        · exact h_g x₀
        exact congrFun h_g' x₀

    -- Says that the number of matrices G such that for each row G_i, G_ix = v_i is equal to the product
    -- over i of the number of row vectors g such that gx = v_i
    have h3 : (filter (fun G => ∀ (i : Fin n), Matrix.mulVec (get_matrix_row n k G i) x = fun _ => v i) Finset.univ).card
    = Finset.prod Finset.univ (fun (i : Fin n) => (filter (fun g : Matrix (Fin 1) (Fin k) α => Matrix.mulVec g x = fun _ => v i) Finset.univ).card)
    · have h3₀ : (fun G => ∀ (i : Fin n), Matrix.mulVec (get_matrix_row n k G i) x = fun _ => v i)
      = (fun G => ∀ (i : Fin n), (Finset.sum Finset.univ fun j => G i j * x j) = v i)
      · unfold get_matrix_row Matrix.mulVec Matrix.dotProduct
        simp
        funext G₀
        simp
        apply Iff.intro
        · intro h_fun i₀
          specialize h_fun i₀
          have h_f : ∀x₀, (fun x_1 => Finset.sum Finset.univ fun x_2 => G₀ i₀ x_2 * x x_2) x₀ = v i₀ := by exact congr_fun h_fun
          let x₀ : Fin 1 := 1
          specialize h_f x₀
          exact h_f
        · intro h_all i₀
          funext x₀
          specialize h_all i₀
          exact h_all

      have h3₁ : Finset.prod Finset.univ (fun i => (filter (fun g : Matrix (Fin 1) (Fin k) α => Matrix.mulVec g x = fun x => v i) Finset.univ).card)
      = ((Finset.univ : Finset (Fin n)).pi (fun i => (filter (fun g : Matrix (Fin 1) (Fin k) α => (Matrix.mulVec g x = fun x => v i)) Finset.univ))).card
      · simp

      let S : Finset ((a : Fin n) → a ∈ Finset.univ → Matrix (Fin 1) (Fin k) α) :=
      ((Finset.univ : Finset (Fin n)).pi (fun i => (filter (fun g : Matrix (Fin 1) (Fin k) α => (Matrix.mulVec g x = fun _ => v i)) Finset.univ)))

      have h3₂ : S.card = (filter (fun G : Matrix (Fin n) (Fin k) α => ∀ (i : Fin n), (Finset.sum Finset.univ fun j => G i j * x j) = v i) Finset.univ).card
      · let f : (s : (a : Fin n) → a ∈ Finset.univ → Matrix (Fin 1) (Fin k) α) → s ∈ S → (Matrix (Fin n) (Fin k) α) := fun s _ ↦ Matrix.of (fun i j => (s i (Finset.mem_univ i)) 1 j)

        apply Finset.card_congr f

        have h_map_to_generator : ∀ (a : (a : Fin n) → a ∈ Finset.univ → Matrix (Fin 1) (Fin k) α) (ha : a ∈ S),
        f a ha ∈ filter (fun G => ∀ (i : Fin n), (Finset.sum Finset.univ fun j => G i j * x j) = v i) Finset.univ
        · intro a ha
          simp
          intro i

          have h_av : Matrix.mulVec (a i (Finset.mem_univ i)) x = fun _ => v i
          · apply Finset.mem_pi.mp at ha
            specialize ha i
            specialize ha (Finset.mem_univ i)
            apply Finset.mem_filter.mp at ha
            simp[ha]

          unfold Matrix.mulVec Matrix.dotProduct at h_av
          simp at h_av
          have h_av₂ : ∀x₀, (fun x_1 => Finset.sum Finset.univ fun x_2 => a i (_ : i ∈ Finset.univ) x_1 x_2 * x x_2) x₀ = v i
          · apply congr_fun h_av
          let x₀ : Fin 1 := 1
          specialize h_av₂ x₀
          simp[h_av₂]

        exact h_map_to_generator

        have h_f_injective : ∀ (a b : (a : Fin n) → a ∈ Finset.univ → Matrix (Fin 1) (Fin k) α) (ha : a ∈ S) (hb : b ∈ S), f a ha = f b hb → a = b
        · intro a b ha hb
          intro h_fab_eq
          funext y h_y
          apply congr_fun at h_fab_eq
          specialize h_fab_eq y
          simp at h_fab_eq
          apply congr_fun at h_fab_eq
          funext 1 x_k
          specialize h_fab_eq x_k
          simp at h_fab_eq
          simp[h_fab_eq]

        exact h_f_injective

        have h_f_surjective : ∀ b ∈ filter (fun G => ∀ (i : Fin n), (Finset.sum Finset.univ fun j => G i j * x j) = v i) Finset.univ, ∃ a, ∃ (ha : a ∈ S), f a ha = b
        · simp
          intro b h_eq
          let a₀ : ((a : Fin n) → a ∈ Finset.univ → Matrix (Fin 1) (Fin k) α) := fun a h_a => Matrix.of (fun i j => b a j)
          use a₀
          simp
          constructor
          · unfold Matrix.mulVec Matrix.dotProduct
            simp[h_eq]
          · funext i j
            simp

        exact h_f_surjective


      simp_rw[h3₀, h3₁, h3₂]

    -- Says that the number of row vectors g such that gx = v_i is equal to |α|^(k-1)
    have h4 : ∀i, (filter (fun g : Matrix (Fin 1) (Fin k) α => Matrix.mulVec g x = fun _ => v i) Finset.univ).card = (Fintype.card α)^(k-1)
    · intro i

      unfold Matrix.mulVec Matrix.dotProduct
      simp

      have h4₀ : (filter (fun g : Matrix (Fin 1) (Fin k) α => (fun x_1 => Finset.sum Finset.univ fun x_2 => g x_1 x_2 * x x_2) = fun x => v i) Finset.univ) =
      Set.toFinset {g : Matrix (Fin 1) (Fin k) α | (Finset.sum (Finset.univ : Finset (Fin k)) fun a => (g 1 a) * (x a)) = v i}
      · sorry -- Definitely doable, just simplifying the mess

      let S := (toFinset {g : Matrix (Fin 1) (Fin k) α | (Finset.sum Finset.univ fun a => g 1 a * x a) = v i})

      have h4₁ : S.card = (Finset.univ : Finset (Codeword (k-1) α)).card
      · let f : (g : Matrix (Fin 1) (Fin k) α) → g ∈ S → Codeword (k-1) α := fun g _ => zero -- This is a placeholder, obviously not the correct bijection
        sorry -- This is the sticking point. It is true but seems very difficult to prove

      have h4₂ : (Finset.univ : Finset (Codeword (k-1) α)).card = (Fintype.card α)^(k-1)
      · sorry -- This is obvious but could be nontrivial to prove

      rw[h4₀, h4₁, h4₂]

    simp_rw[h2, h3, h4]
    simp[←pow_mul, mul_comm]



  norm_cast
  rw[h, ←pow_add]
  congr
  calc
    n * (k - 1) + n = n * (k - 1) + n * 1 := by rw [Nat.mul_one]
    _               = n * ((k - 1) + 1)   := by rw [←Nat.mul_add]
    _               = n * k               := by rw[Nat.sub_add_cancel h_k]
}

theorem prob_leq_ball_size (x : Codeword k α) (d : ℕ) (h_k : k ≥ 1) (h_x : x ≠ 0) (h_d : d > 0) :
(Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}).card / (Fintype.card α)^(n*k) ≤
(hamming_ball (d-1) (zero : Codeword n α)).card / (Fintype.card α)^n := by {

  let S := Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}
  let S' := Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | (Matrix.mulVec G x) ∈ hamming_ball (d-1) zero}

  have h_card_eq : S.card = S'.card
  · let f : (G : Matrix (Fin n) (Fin k) α) → G ∈ S → (Matrix (Fin n) (Fin k) α) := fun G _ ↦ G
    apply Finset.card_congr f

    have h_map : ∀ (G : Matrix (Fin n) (Fin k) α) (hG : G ∈ S), f G hG ∈ S'
    · simp
      unfold weight
      intro G h_dist_le_d
      have h_dist_leq_dminus1 : hamming_distance (Matrix.mulVec G x) 0 ≤ d - 1
      · have h₁ : (hamming_distance (Matrix.mulVec G x) 0) + 1 ≤ d := by exact Nat.succ_le_of_lt h_dist_le_d
        have h₂ : (hamming_distance (Matrix.mulVec G x) 0) + 1 - 1 ≤ d - 1 := by exact Nat.sub_le_sub_right h₁ 1
        rw[Nat.add_sub_cancel] at h₂
        exact h₂
      rw [mem_toFinset]
      simp[h_dist_leq_dminus1]
      exact h_dist_leq_dminus1

    exact h_map

    have h_inj : ∀ (G G' : Matrix (Fin n) (Fin k) α) (hG : G ∈ S) (hG' : G' ∈ S), f G hG = f G' hG' → G = G'
    · intro G G' hG hG' h_fG_eq
      simp[h_fG_eq]

    exact h_inj

    have h_surj : ∀ G' ∈ S', ∃ G, ∃ (hG : G ∈ S), f G hG = G'
    · intro G' h_G'inS'
      use G'
      simp
      simp_rw[mem_toFinset] at h_G'inS'
      simp[Set.mem_setOf] at h_G'inS'
      rw[mem_toFinset] at h_G'inS'
      simp[Set.mem_setOf] at h_G'inS'
      unfold weight
      sorry -- This is easily doable
    exact h_surj

  simp_rw[h_card_eq]

  let matrix_uniformity := uniformity_lemma n k x h_x h_k

  unfold matrix_dist uniform_vector_dist at matrix_uniformity
  simp at matrix_uniformity

  have h_unif (v: Codeword n α) : (toFinset {G | Matrix.mulVec G x = v}).card / Fintype.card α ^ (n * k) = 1 / (Fintype.card α)^n -- TODO: Should this be ≤?
  · apply congr_fun at matrix_uniformity
    specialize matrix_uniformity v
    have h_filter : ↑(filter (fun x_1 => Matrix.mulVec x_1 x = v) Finset.univ) = (toFinset {G | Matrix.mulVec G x = v})
    · sorry -- Just wrestling with types
    rw[←h_filter]

    sorry -- Casting mess

  have h_sum : (toFinset {G | Matrix.mulVec G x ∈ hamming_ball (d - 1) zero}).card / Fintype.card α ^ (n * k) = Finset.sum (Set.toFinset {v : Codeword n α | (hamming_distance v zero) ≤ d-1}) fun v => 1 / (Fintype.card α)^n
  · sorry -- Use h_unif

  have h_ball_size : Finset.sum (Set.toFinset {v : Codeword n α | (hamming_distance v zero) ≤ d-1}) (fun v => 1 / (Fintype.card α)^n) = (hamming_ball (d-1) (zero : Codeword n α)).card / (Fintype.card α)^n
  · have h_sum_mult : Finset.sum (Set.toFinset {v : Codeword n α | (hamming_distance v zero) ≤ d-1}) (fun v => 1 / (Fintype.card α)^n) = (Set.toFinset {v : Codeword n α | (hamming_distance v zero) ≤ d-1}).card * (1 / (Fintype.card α)^n)
    · sorry -- Not sure how to do this but should be basic arithmetic manipulation
    rw[h_sum_mult]
    field_simp
    let a := (toFinset {v : Codeword n α | hamming_distance v zero ≤ d - 1}).card
    let b := (Fintype.card α)^n
    change a * (1/b) = a / b
    sorry -- More arithmetic, might need hypothesis that b ≠ 0

  rw[h_sum, h_ball_size]
}

theorem existence_bound (d: ℕ) :
(Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | ∃ (x : Codeword k α), weight (Matrix.mulVec G x) < d}).card ≤
(Fintype.card α)^k * ((hamming_ball (d-1) (zero : Codeword n α)).card) := by {

  let S := Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | ∃ (x : Codeword k α), weight (Matrix.mulVec G x) < d}
  let S_u := Set.toFinset (⋃ (x : Codeword k α), {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d})

  have h_union_eq : S = S_u
  · ext G
    apply Iff.intro
    · intro h_S
      rw[Set.mem_toFinset, Set.mem_setOf] at h_S
      simp[h_S]
    · intro h_Su
      sorry

  let card_sum := (Finset.sum Finset.univ fun (x : Codeword k α) => (Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}).card)

  have h_union_bound : S_u.card ≤ card_sum
  · sorry -- Apply Finset.card_union_le. Might need induction.

  have h_sum_leq : card_sum ≤ (Fintype.card α)^k * ((hamming_ball (d-1) (zero : Codeword n α)).card)
  · sorry -- Use previous lemma prob_leq_ball_size

  change S.card ≤ (Fintype.card α)^k * ((hamming_ball (d-1) (zero : Codeword n α)).card)
  rw[h_union_eq]

  trans card_sum
  · exact h_union_bound
  · exact h_sum_leq
}

theorem gv_bound (n k q d : ℕ) (h_q : q = (Fintype.card α)) (h_k : k ≤ n - ((Nat.clog q) (hamming_ball (d-1) (zero : Codeword n α)).card) - 1):
(Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | ∀ (x : Codeword k α), x ≠ 0 → weight (Matrix.mulVec G x) ≥ d}).card ≥ 1 := by {
  sorry -- The final result - should follow closely from the previous lemmas but may be worth reframing
}
