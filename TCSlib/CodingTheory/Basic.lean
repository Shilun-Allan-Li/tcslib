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
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.Archimedean
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Disjoint

/-!
# Code Definitions

`Code n 𝔽`: a subset of 𝔽ⁿ.
`AsymptoticCodes 𝔽`: a map from ℕ to `Code n 𝔽`.

-/

open Set Filter Asymptotics Finset Linarith

namespace CodingTheory

-- variable {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α]-- the alphabet
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

def weight (c: Codeword n α) : ℕ := hamming_distance c zero


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

theorem hamming_ball_size_asymptotic_upper_bound (q n : ℕ) (p : ℝ) (hq : q = Fintype.card α) (hα : Nontrivial α) (hp : 0 < p ∧ p ≤ 1 - 1/q):
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
lemma q_pow_qary_entropy_simp {q : ℕ} {p : ℝ} (hq : 2 ≤ q) (hp : 0 < p ∧ p < 1): Real.rpow q (qaryEntropy q p) = (q - 1)^p * p ^ (-p) * (1 - p)^(-(1 - p)) := by{
  simp
  dsimp[qaryEntropy]
  have : (p * Real.logb (↑q) (↑q - 1) - p * Real.logb (↑q) p - (1 - p) * Real.logb (↑q) (1 - p)) =
          (Real.logb (↑q) (↑q - 1)) * (p) + (Real.logb (↑q) p) * -(p) + (Real.logb (↑q) (1 - p)) * -(1-p)
  · linarith
  rw[this]

  have hq₂ : 0 < (q : ℝ)
  · simp
    linarith

  have hq₃ : (q : ℝ) ≠ 1
  · have :  1 < (q : ℝ)
    · simp
      linarith
    linarith

  have hq₄ : (0 : ℝ) < ↑q - 1
  · simp
    linarith

  have hq₅ : q ≠ 0
  · simp
    linarith

  have hp₂ : 0 < 1 - p
  · suffices p < 1 by exact sub_pos.mpr this
    exact hp.2


  rw[Real.rpow_add hq₂, Real.rpow_add hq₂]
  rw[Real.rpow_mul (le_of_lt hq₂), Real.rpow_mul (le_of_lt hq₂), Real.rpow_mul (le_of_lt hq₂)]
  rw[Real.rpow_logb hq₂ hq₃ hq₄, Real.rpow_logb hq₂ hq₃ hp.1, Real.rpow_logb hq₂ hq₃ hp₂]

  simp
}

lemma q_pow_qary_entropy_simp' {q : ℕ} {p : ℝ} (hq : 2 ≤ q) (hp : 0 < p ∧ p < 1): q ^ (qaryEntropy q p) = (q - 1)^p * p ^ (-p) * (1 - p)^(-(1 - p)) := by{
  simp
  dsimp[qaryEntropy]
  have : (p * Real.logb (↑q) (↑q - 1) - p * Real.logb (↑q) p - (1 - p) * Real.logb (↑q) (1 - p)) =
          (Real.logb (↑q) (↑q - 1)) * (p) + (Real.logb (↑q) p) * -(p) + (Real.logb (↑q) (1 - p)) * -(1-p)
  · linarith
  rw[this]

  have hq₂ : 0 < (q : ℝ)
  · simp
    linarith

  have hq₃ : (q : ℝ) ≠ 1
  · have :  1 < (q : ℝ)
    · simp
      linarith
    linarith

  have hq₄ : (0 : ℝ) < ↑q - 1
  · simp
    linarith

  have hq₅ : q ≠ 0
  · simp
    linarith

  have hp₂ : 0 < 1 - p
  · suffices p < 1 by exact sub_pos.mpr this
    exact hp.2


  rw[Real.rpow_add hq₂, Real.rpow_add hq₂]
  rw[Real.rpow_mul (le_of_lt hq₂), Real.rpow_mul (le_of_lt hq₂), Real.rpow_mul (le_of_lt hq₂)]
  rw[Real.rpow_logb hq₂ hq₃ hq₄, Real.rpow_logb hq₂ hq₃ hp.1, Real.rpow_logb hq₂ hq₃ hp₂]

  simp
}

lemma sqrt_sub_sqrt_floor_le_one (hx : 0 ≤ x) : Real.sqrt x - Real.sqrt (Nat.floor x) ≤ 1 := by{
  suffices ‖Real.sqrt x - Real.sqrt (Nat.floor x)‖ ≤ ‖(1 : ℝ)‖ by{
    simp at this
    rw[abs_of_nonneg] at this
    exact this
    simp
    apply Real.sqrt_le_sqrt
    exact Nat.floor_le hx
  }
  apply sq_le_sq.1
  rw[sub_sq]
  simp
  rw[Real.sq_sqrt hx]
  calc
    x - 2 * Real.sqrt x * Real.sqrt ↑⌊x⌋₊ + ↑⌊x⌋₊ ≤ x - 2 * (Real.sqrt ↑⌊x⌋₊ * Real.sqrt ↑⌊x⌋₊) +  ↑⌊x⌋₊:= by {
      suffices 2 * (Real.sqrt ↑⌊x⌋₊ * Real.sqrt ↑⌊x⌋₊) ≤ 2 * (Real.sqrt x * Real.sqrt ↑⌊x⌋₊)  by linarith
      suffices Real.sqrt ↑⌊x⌋₊ ≤ Real.sqrt x by {
        apply (mul_le_mul_left two_pos).2
        by_cases h: ↑⌊x⌋₊ = 0
        rw[h]
        simp
        have hx_pos : 0 < Real.sqrt ↑⌊x⌋₊ := by simp; exact Nat.pos_of_ne_zero h
        apply (mul_le_mul_right hx_pos).2
        exact this
      }
      exact Real.sqrt_le_sqrt (Nat.floor_le hx)
    }
    _ = x - 2 * ↑⌊x⌋₊ +  ↑⌊x⌋₊ := by simp
    _ = x - ↑⌊x⌋₊             := by ring
    _ ≤ 1                     := by linarith[Nat.sub_one_lt_floor x]

}
lemma hamming_volume_asymptotic_lower_bound (q n: ℕ) (p : ℝ) (hp : 0 < p ∧ p < 1) (hn : 0 < n) (hq : 2 ≤ q):
∃ (ε : ℕ → ℝ), IsLittleO atTop ε (fun n ↦ (n: ℝ)) ∧ Nat.choose n (Nat.floor (n*p)) * (q - 1) ^ (p*n) ≥  Real.rpow q ((qaryEntropy q p) * n - ε n):= by{
  -- Some trivial claims

  -- Using the leftover coefficient and prove the asymptotic behavior
  let ε : ℕ → ℝ := fun n ↦ Real.logb q (n ^ ((1 : ℝ)/2))
  let ε' : ℕ → ℝ := fun n ↦  Real.logb q ((2 * Real.pi * (p * (1 - p))) ^ (1 / 2)) + (ε n)

  -- Proving the Asymptotic Tightness of the Error term
  use ε'
  constructor
  · apply Asymptotics.IsLittleO.add
    · simp
      right
      have h1 : (norm ∘ (fun (n:ℕ) => (n:ℝ))) = (fun (n : ℕ) ↦ ‖(n: ℝ)‖)
      · exact rfl
      rw[h1]
      simp
      apply tendsto_nat_cast_atTop_iff.2
      have h2 : (fun (n:ℕ) ↦ n) = id
      · exact rfl
      rw[h2]
      exact Filter.tendsto_id
    · dsimp
      have h₁ : (fun (x:ℕ) => Real.logb (↑q) (↑x ^ ((1:ℝ) / 2))) = (fun (x:ℕ) => 1/2 * 1 / Real.log (↑q) * Real.log (↑x))
      · ext x
        by_cases hx : x = 0
        rw[hx]
        simp
        apply Nat.pos_of_ne_zero at hx
        rw [← Real.log_div_log, Real.log_rpow]
        field_simp
        exact Nat.cast_pos.mpr hx
      rw[h₁]
      apply Asymptotics.IsLittleO.const_mul_left
      -- This composition theorem is really useful when dealing with f : ℕ → ℝ
      exact IsLittleO.comp_tendsto Real.isLittleO_log_id_atTop tendsto_nat_cast_atTop_atTop

  -- Using Stirling's Formula to "Derive" the Error term
  · rw[Nat.choose_eq_factorial_div_factorial]
    have h_stirling := Stirling.factorial_isEquivalent_stirling
    -- have h_stirling_Big := Asymptotics.IsEquivalent.isBigO h_stirling
    -- have h_stirling_Big' := Asymptotics.IsEquivalent.isBigO_symm h_stirling
    have h_stirling₁ : (fun (n : ℕ) => ↑(Nat.factorial (Nat.floor (n*p)))) ~[atTop] fun n => Real.sqrt (2 * (Nat.floor (n*p)) * Real.pi) * ((Nat.floor (n*p)) / Real.exp 1) ^ (Nat.floor (n*p))
    · sorry
    have h_stirling₂ : (fun (n : ℕ) => ↑(Nat.factorial (n - (Nat.floor (n*p))))) ~[atTop] fun n => Real.sqrt (2 * (n - (Nat.floor (n*p))) * Real.pi) * ((n - (Nat.floor (n*p))) / Real.exp 1) ^ (n - (Nat.floor (n*p)))
    · sorry
    have h_stirling_choose := Asymptotics.IsEquivalent.mul h_stirling (Asymptotics.IsEquivalent.inv (Asymptotics.IsEquivalent.mul h_stirling₁ h_stirling₂))
    rw[Pi.mul_def, Pi.mul_def, Pi.mul_def, Pi.mul_def] at h_stirling_choose
    simp at h_stirling_choose
    apply Asymptotics.IsEquivalent.isBigO_symm at h_stirling_choose
    rw[Asymptotics.IsBigO_def] at h_stirling_choose
    rcases h_stirling_choose with ⟨c, hc⟩
    rw[Asymptotics.IsBigOWith_def] at hc
    simp at hc
    sorry
    sorry
    -- lift
  -- · simp
  --   have h₁ : (2 * Real.pi * (p * (1 - p)))^(1/2) ≠ 0
  --   · simp
  --     push_neg
  --     exact ⟨(by linarith [Real.pi_pos]), ⟨(by linarith), (by linarith)⟩⟩
  --   have h₂ : Real.sqrt n ≠ 0
  --   · sorry
  --   have : Real.logb (↑q) ((2 * Real.pi * (p * (1 - p))) ^ (1 / 2) * ↑n ^ (1 / 2))  =
  --   Real.logb (↑q) ((2 * Real.pi * (p * (1 - p))) ^ (1 / 2)) + Real.logb (↑q) (↑n ^ (1 / 2))
  --   · exact Real.logb_mul h₁ h₁

  --   rw[this]

}

lemma binomial_coef_asymptotic_lower_bound (n: ℕ) (p : ℝ) (hp : 0 < p ∧ p < 1) (hn : 0 < n) :
∃ (ε : ℕ → ℝ), IsLittleO atTop ε (fun n ↦ (n: ℝ)) ∧ Nat.choose n (Nat.floor (n*p)) ≥  Real.rpow 2 ((qaryEntropy 2 p) * n - ε n):= by{

  have : ∃ (f : ℕ → ℝ), IsLittleO atTop f (fun n ↦ (n: ℝ)) ∧
    ↑(Nat.choose n ⌊↑n * p⌋₊) * (↑2 - 1) ^ (p * ↑n) ≥ Real.rpow (↑2) (qaryEntropy 2 p * ↑n - f n)
  · exact hamming_volume_asymptotic_lower_bound 2 n p hp hn (by norm_num)

  norm_num at this
  simp
  exact this
  -- -- Some trivial claims

  -- -- Using the leftover coefficient and prove the asymptotic behavior
  -- let f : ℕ → ℝ := fun n ↦ Real.sqrt n
  -- let f' : ℕ → ℝ := fun n ↦  Real.logb 2 (Real.sqrt (2 * Real.pi * (p * (1 - p))) * f n)

  -- use f'
  -- constructor
  -- -- · -- Showing Positivity
  -- --   simp
  -- --   apply Real.logb_pos
  -- --   norm_num
  -- --   apply one_lt_mul

  -- -- · constructor
  -- · -- Asymptotic
  --   apply Asymptotics.IsLittleO.const_mul_left
  --   simp
  --   apply Asymptotics.isLittleO_pow_pow_atTop_of_lt
  -- · -- Show Equality using Stirling's Formula
  --   sorry
}

theorem hamming_ball_size_asymptotic_lower_bound (q n: ℕ) (p : ℝ) (hq : q = Fintype.card α) (hα : Nontrivial α) (hnp : (Nat.floor (n*p)) = n*p) (hp : 0 < p ∧ p ≤ 1 - 1/q) (hn : 0 < n):
∀ c : Codeword n α, ∃ (ε : ℕ → ℝ), IsLittleO atTop ε (fun n ↦ (n: ℝ)) ∧ (hamming_ball (Nat.floor (n*p)) c).card ≥ Real.rpow q ((qaryEntropy q p) * n - ε n) := by {
  intro C

  have hα₂ : 2 ≤ q
  · rw[hq]
    linarith[Fintype.one_lt_card_iff_nontrivial.2 hα]

  have hα₂' : 2 ≤ (q: ℝ)
  · rw[hq]
    apply Nat.cast_le.2
    linarith[Fintype.one_lt_card_iff_nontrivial.2 hα]

  have hp₂ : p < 1
  · calc
      p ≤ 1 - 1/↑q               := by exact hp.2
      _ = 1 - 1/(Fintype.card α) := by rw[hq]
      _ < 1                      := by exact sub_lt_self 1 (one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero Fintype.card_ne_zero)))

  rw[hamming_ball_size n]

  rcases hamming_volume_asymptotic_lower_bound q n p ⟨hp.1, hp₂⟩ hn hα₂ with ⟨f, ⟨hf_asymp, hf⟩⟩
  use f
  constructor
  · exact hf_asymp
  · simp at hf ⊢
    apply le_trans hf
    rw[← hq]
    have : ∀ i ∈ (Finset.range (⌊↑n * p⌋₊ + 1)), 0 ≤ (Nat.choose n i * (Fintype.card α - 1) ^ i : ℝ)
    · intros i hi
      simp at hi
      rw[← hq]
      apply mul_nonneg
      · simp
      · apply pow_nonneg
        linarith
    have hnp_mem: ⌊↑n * p⌋₊ ∈ (Finset.range (⌊↑n * p⌋₊ + 1))
    · simp
    simp only [hq] at this ⊢

    have h₁ : (((Fintype.card α) : ℝ) - 1) = ((Fintype.card α - 1) : ℕ)
    · rw[← hq]
      have : 1 ≤ q
      · linarith
      rw[Nat.cast_sub]
      simp
      exact this
    rw[← h₁]
    rw[mul_comm p ↑n]
    rw[← hnp]
    simp
    exact Finset.single_le_sum this hnp_mem



  -- -- Some trivial claims
  -- have hα₂ : 2 ≤ (q: ℝ)
  -- · rw[hq]
  --   apply Nat.cast_le.2
  --   linarith[Fintype.one_lt_card_iff_nontrivial.2 hα]

  -- have hα₂' : 2 ≤ q
  -- · rw[hq]
  --   linarith[Fintype.one_lt_card_iff_nontrivial.2 hα]

  -- have hα_pos : 0 < (q: ℝ)
  -- · linarith

  -- have hp₂ : p < 1
  -- · calc
  --     p ≤ 1 - 1/↑q               := by exact hp.2
  --     _ = 1 - 1/(Fintype.card α) := by rw[hq]
  --     _ < 1                      := by exact sub_lt_self 1 (one_div_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero Fintype.card_ne_zero)))

  -- -- Calling Binomial Coef Lemma
  -- intro C
  -- rcases binomial_coef_asymptotic_lower_bound n p ⟨hp.1, hp₂⟩ hn with ⟨f, ⟨hf_asymp, hf⟩⟩

  -- have hfn : 0 ≤ f n
  -- · by_contra hfn_neg
  --   push_neg at hfn_neg
  --   let c' : Codeword n (Fin 2) := 0
  --   have h₁ : (hamming_ball (Nat.floor (n*p)) c').card = (Nat.choose n ⌊↑n * p⌋₊)
  --   · sorry
  --   rw[← h₁] at hf
  --   have h₂: (hamming_ball ⌊↑n * p⌋₊ c').card > Real.rpow 2 (qaryEntropy 2 p * ↑n)
  --   · calc
  --      Real.rpow 2 (qaryEntropy 2 p * ↑n) < Real.rpow 2 (qaryEntropy 2 p * ↑n - f n) := by {
  --       apply (Real.rpow_lt_rpow_left_iff _).2
  --       linarith
  --       norm_num
  --     }
  --     _ ≤ (hamming_ball ⌊↑n * p⌋₊ c').card := by exact hf
  --   have h₃ : (hamming_ball ⌊↑n * p⌋₊ c').card ≤ Real.rpow 2 (qaryEntropy 2 p * ↑n)
  --   · apply hamming_ball_size_asymptotic_upper_bound


  -- -- Simlify binary entropy
  -- rw[sub_eq_add_neg] at hf
  -- simp at hf
  -- rw[Real.rpow_add two_pos, Real.rpow_mul (le_of_lt two_pos)] at hf
  -- have : Real.rpow (2 : ℕ) (qaryEntropy 2 p) = 2 ^ qaryEntropy 2 p
  -- · simp
  -- rw[← this] at hf
  -- rw[q_pow_qary_entropy_simp 2 p] at hf



  -- -- Doing All the Algebra
  -- use f
  -- constructor
  -- · exact hf_asymp
  -- · rw[hamming_ball_size n]
  --   simp

  --   calc
  --     Real.rpow (↑q) (qaryEntropy q p * ↑n - f n) ≤ (Nat.choose n ⌊↑n * p⌋₊) * (q - 1)^⌊↑n * p⌋₊ := by{
  --       simp at hf ⊢
  --       rw[sub_eq_add_neg]
  --       rw[Real.rpow_add hα_pos, Real.rpow_mul (le_of_lt hα_pos)]
  --       rw[q_pow_qary_entropy_simp' q p hα₂' ⟨hp.1, hp₂⟩]
  --       norm_num at hf
  --       simp
  --       have : 0 < ((q :ℝ) - 1)^(p*n)
  --       · apply Real.rpow_pos_of_pos
  --         linarith

  --       apply (mul_le_mul_left this).2 at hf
  --       calc
  --        ((↑q - 1) ^ p * p ^ (-p) * (1 - p) ^ (p - 1)) ^ n * ↑q ^ (-f n) ≤
  --         (↑q - 1) ^ (p * ↑n) * (p ^ (-p) * (1 - p) ^ (p - 1)) ^ n * 2 ^ (-f n) := by {
  --           rw[Real.rpow_mul (by linarith)]
  --           rw[← Real.rpow_nat_cast]
  --           rw[← Real.rpow_nat_cast]
  --           have h₁ : 0 ≤ ((q:ℝ) - 1) ^ p
  --           · apply Real.rpow_nonneg
  --             linarith
  --           have h₂ : 0 ≤ p ^ (-p) * (1 - p) ^ (p - 1)
  --           · apply mul_nonneg
  --             apply Real.rpow_nonneg
  --             linarith
  --             apply Real.rpow_nonneg
  --             linarith
  --           rw[← Real.mul_rpow h₁ h₂]
  --           rw[← mul_assoc]
  --           apply (mul_le_mul_left _).2
  --           apply Real.rpow_le_rpow_of_nonpos _ _ _
  --           linarith
  --           linarith
  --           simp
  --           · linarith
  --           · apply Real.rpow_pos_of_pos
  --             apply mul_pos
  --             apply mul_pos
  --             apply Real.rpow_pos_of_pos
  --             linarith
  --             apply Real.rpow_pos_of_pos
  --             linarith
  --             apply Real.rpow_pos_of_pos
  --             linarith
  --         }
  --       _ ≤ (↑q - 1) ^ (p * ↑n) * ↑(Nat.choose n ⌊↑n * p⌋₊) := by {
  --         linarith
  --       }
  --       _ ≤ ↑(Nat.choose n ⌊↑n * p⌋₊) * (↑q - 1) ^ ⌊↑n * p⌋₊ := by {
  --         rw[mul_comm p ↑n]
  --         rw[← hnp]
  --         simp
  --         linarith
  --       }
  --     }
  --     _ ≤ ((Finset.sum (Finset.range (⌊↑n * p⌋₊ + 1)) fun i => Nat.choose n i * (Fintype.card α - 1) ^ i) : ℝ) := by{
  --       have : ∀ i ∈ (Finset.range (⌊↑n * p⌋₊ + 1)), 0 ≤ (Nat.choose n i * (Fintype.card α - 1) ^ i : ℝ)
  --       · intros i hi
  --         simp at hi
  --         rw[← hq]
  --         apply mul_nonneg
  --         · simp
  --         · apply pow_nonneg
  --           linarith
  --       have hnp_mem: ⌊↑n * p⌋₊ ∈ (Finset.range (⌊↑n * p⌋₊ + 1))
  --       · simp
  --       simp only [hq] at this ⊢
  --       exact Finset.single_le_sum this hnp_mem
  --     }
  --     _ ≤ Finset.sum (Finset.range (⌊↑n * p⌋₊ + 1)) fun x => ↑(Nat.choose n x) * ↑(Fintype.card α - 1) ^ x := by{
  --       apply Finset.sum_le_sum
  --       intros i hi
  --       apply mul_le_mul
  --       · linarith
  --       · have h₁ : (((Fintype.card α) : ℝ) - 1) = ((Fintype.card α - 1) : ℕ)
  --         · rw[← hq]
  --           have : 1 ≤ q
  --           · linarith
  --           rw[Nat.cast_sub]
  --           simp
  --           exact this

  --         rw[h₁]
  --       rw[← Real.rpow_nat_cast]
  --       apply Real.rpow_nonneg
  --       rw[←hq]
  --       linarith
  --       simp
  --     }

  -- simp
  -- exact ⟨hp.1, by linarith⟩
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


theorem hamming_bound (n d : ℕ) (C : Code n α) (h : distance C d) (h'' : Fintype.card α >1)(hd : 0 < d):
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
    exact fun a _ => hamming_ball_size n (Nat.floor (((d : ℝ)-1)/2)) a

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
    rcases hG with ⟨hG_image, _⟩
    specialize hG_image 0
    simp at hG_image
    exact hG_image
    exact c_nzero
  · rcases h.1 with ⟨c₁, ⟨hc₁, c₂, ⟨hc₂, ⟨_, hc₁₂dist_eq_d⟩⟩⟩⟩
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
theorem uniformity_lemma (n k : ℕ) (x : Codeword k α) (h_x : x ≠ zero) (h_k : k ≥ 1) :
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
      Set.toFinset {g : Matrix (Fin 1) (Fin k) α | (Finset.sum (Finset.univ : Finset (Fin k)) fun a => (g 0 a) * (x a)) = v i}
      · ext x
        simp
        constructor
        · intro h_filter
          apply congr_fun at h_filter
          specialize h_filter 1
          rw[Set.mem_toFinset, Set.mem_setOf]
          exact h_filter
        · intro h_univ
          rw[Set.mem_toFinset, Set.mem_setOf] at h_univ
          funext 1
          exact h_univ

      let c := v i
      let S := (toFinset {g : Matrix (Fin 1) (Fin k) α | (Finset.sum Finset.univ fun a => g 0 a * x a) = c})

      have h4₁ : S.card = (Fintype.card α)^(k-1)
      · have h_nonzero_element : ∃ (j : Fin k), x j ≠ 0
        · by_contra h_zero
          push_neg at h_zero
          have h_x_eq_zero : x = zero := by ext l; exact h_zero l
          exact h_x h_x_eq_zero

        rcases h_nonzero_element with ⟨j, h_j⟩

        have h_rearrange : S = (toFinset {g : Matrix (Fin 1) (Fin k) α | (g 0 j) = (c - Finset.sum (Finset.univ.erase j) fun a => (g 0 a)*(x a)) / (x j)})
        · ext y
          simp
          constructor
          · intro h_sum
            field_simp[h_sum]
          · intro h_formula
            field_simp at h_formula
            rw[eq_sub_iff_add_eq] at h_formula
            simp_all[Finset.sum_sub_distrib, mul_sub]

        simp_rw[h_rearrange]
        let S₂ := (toFinset {g : Matrix (Fin 1) (Fin k) α | g 0 j = (v i - Finset.sum (erase Finset.univ j) fun a => g 0 a * x a) / x j})

        have h_g_bijection : S₂.card = (Finset.univ : Finset (Codeword (k-1) α)).card
        · have h_k1 (l : Fin (k-1)) : ↑l < k
          · have h_l2 : ↑l < k - 1 := l.2
            omega

          have h_k2 (l : Fin (k-1)) : ↑l + 1 < k
          · have h_l2 : ↑l < k - 1 := l.2
            omega

          let f : (g : Matrix (Fin 1) (Fin k) α) → g ∈ S₂ → (Codeword (k-1) α) := fun g h_g => (fun (l : Fin (k-1)) => if h_llt : l.val < j then (g 0 ⟨l.val, by exact h_k1 l⟩) else (g 0 ⟨l.val + 1, by exact h_k2 l⟩))
          apply Finset.card_congr f

          simp_all

          have h_f_inj : ∀ (a b : Matrix (Fin 1) (Fin k) α) (ha : a ∈ S₂) (hb : b ∈ S₂), f a ha = f b hb → a = b
          · simp
            intro a b h_a h_b h_l

            let φa := (fun (l : Fin (k-1)) => if (l : ℕ) < (j : ℕ) then a 0 { val := ↑l, isLt := h_k1 l } else a 0 { val := ↑l + 1, isLt := h_k2 l })
            let φb := (fun (l : Fin (k-1)) => if (l : ℕ) < (j : ℕ) then b 0 { val := ↑l, isLt := h_k1 l } else b 0 { val := ↑l + 1, isLt := h_k2 l })
            have hφ : φa = φb := by simp[h_l]

            ext i₁ iκ
            have h_i1 : i₁ = 0 := by fin_cases i₁; simp
            rw[h_i1]
            have h_cases : iκ.val < j.val ∨ iκ.val = j.val ∨ iκ.val > j.val
            · exact Nat.lt_trichotomy iκ.val j.val

            have h_eq_if_lt (i₀ : Fin k) (h_lt : ↑i₀ < ↑j) : a 0 i₀ = b 0 i₀
            · have h_i₀val : i₀ < k-1
              · have h_j_le : ↑j ≤ k-1 := Nat.le_pred_of_lt j.2
                exact lt_of_lt_of_le h_lt h_j_le
              have h_φeq : φa ⟨↑i₀, by exact h_i₀val⟩ = φb ⟨↑i₀, by exact h_i₀val⟩ := by exact congrFun hφ ⟨↑i₀, by exact h_i₀val⟩
              have h_φa : φa ⟨↑i₀, by exact h_i₀val⟩ = a 0 ↑i₀
              · simp[φa]
                intro h_jleq
                have h_notjleq : ¬(j ≤ i₀) := Nat.not_le_of_gt h_lt
                contradiction
              have h_φb : φb ⟨↑i₀, by exact h_i₀val⟩ = b 0 ↑i₀
              · simp[φb]
                intro h_jleq
                have h_notjleq : ¬(j ≤ i₀) := Nat.not_le_of_gt h_lt
                contradiction
              rw[h_φa, h_φb] at h_φeq
              exact h_φeq

            have h_eq_if_gt (i₀ : Fin k) (h_gt : (i₀ : ℕ) > (j : ℕ)) : a 0 i₀ = b 0 i₀
            · have h_i₀val : i₀ - 1 < k - 1
              · have h_i₀_lt_k : ↑i₀ < k := i₀.2
                have h_i₀_gt_j : ↑i₀ > ↑j := h_gt
                omega

              have h_φeq : φa ⟨↑i₀ - 1, by exact h_i₀val⟩ = φb ⟨↑i₀ - 1, by exact h_i₀val⟩ := by exact congrFun hφ ⟨↑i₀ - 1, by exact h_i₀val⟩
              have h_φa : φa ⟨↑i₀ - 1, by exact h_i₀val⟩ = a 0 ↑i₀
              · simp[φa]
                rw[if_neg]
                have h_i₀_pos : (i₀ : ℕ) > 0 := by exact Nat.lt_of_le_of_lt (Nat.zero_le j) h_gt
                have h_i₀_ge_one : 1 ≤ (i₀ : ℕ)
                · rw [Nat.one_le_iff_ne_zero]
                  intro h_zero
                  exact Nat.ne_of_gt h_i₀_pos h_zero
                have h_simplify : (i₀ : ℕ) - 1 + 1 = ↑i₀ := by exact Nat.sub_add_cancel h_i₀_ge_one
                simp_rw[h_simplify]
                omega
              have h_φb : φb ⟨↑i₀ - 1, by exact h_i₀val⟩ = b 0 ↑i₀
              · simp[φb]
                rw[if_neg]
                have h_i₀_pos : (i₀ : ℕ) > 0 := by exact Nat.lt_of_le_of_lt (Nat.zero_le j) h_gt
                have h_i₀_ge_one : 1 ≤ (i₀ : ℕ)
                · rw [Nat.one_le_iff_ne_zero]
                  intro h_zero
                  exact Nat.ne_of_gt h_i₀_pos h_zero
                have h_simplify : (i₀ : ℕ) - 1 + 1 = ↑i₀ := by exact Nat.sub_add_cancel h_i₀_ge_one
                simp_rw[h_simplify]
                omega
              rw[h_φa, h_φb] at h_φeq
              exact h_φeq


            rcases h_cases with (h_lt | h_eq | h_gt)
            · exact h_eq_if_lt iκ h_lt
            · have h_fineq : iκ = j := by exact Fin.eq_of_val_eq h_eq
              rw[h_fineq, h_a, h_b]
              field_simp

              have h_a_sum_split : (Finset.sum (Finset.univ : Finset (Fin k)) fun a_1 => a 0 a_1 * x a_1) =
              (Finset.sum (Finset.filter (fun i => i < j) Finset.univ) fun a_1 => a 0 a_1 * x a_1) + (Finset.sum (Finset.filter (fun i => i > j) Finset.univ) fun a_1 => a 0 a_1 * x a_1) + a 0 j * x j
              · simp_rw[←Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin k)) (fun i => i = j) (fun a_1 => a 0 a_1 * x a_1)]

                have h_eq_j : Finset.filter (fun i => i = j) (Finset.univ : Finset (Fin k)) = {j} := by ext i; simp

                have h_neq_split : Finset.filter (fun i => i ≠ j) (Finset.univ : Finset (Fin k)) = Finset.filter (fun i => i < j) (Finset.univ : Finset (Fin k)) ∪ Finset.filter (fun i => i > j) (Finset.univ : Finset (Fin k))
                · ext i
                  simp

                have h_disjoint : Disjoint (Finset.filter (fun i => i < j) (Finset.univ : Finset (Fin k))) (Finset.filter (fun i => i > j) (Finset.univ : Finset (Fin k)))
                · apply Finset.disjoint_filter.mpr
                  intro i h1 h2
                  exact lt_asymm h2

                rw[h_eq_j, Finset.sum_singleton, h_neq_split, Finset.sum_union h_disjoint]
                ring

              have h_b_sum_split : (Finset.sum Finset.univ fun a_1 => b 0 a_1 * x a_1) =
              (Finset.sum (Finset.filter (fun i => i < j) Finset.univ) fun a_1 => b 0 a_1 * x a_1) + (Finset.sum (Finset.filter (fun i => i > j) Finset.univ) fun a_1 => b 0 a_1 * x a_1) + b 0 j * x j
              · simp_rw[←Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin k)) (fun i => i = j) (fun a_1 => b 0 a_1 * x a_1)]

                have h_eq_j : Finset.filter (fun i => i = j) (Finset.univ : Finset (Fin k)) = {j} := by ext i; simp

                have h_neq_split : Finset.filter (fun i => i ≠ j) (Finset.univ : Finset (Fin k)) = Finset.filter (fun i => i < j) (Finset.univ : Finset (Fin k)) ∪ Finset.filter (fun i => i > j) (Finset.univ : Finset (Fin k))
                · ext i
                  simp

                have h_disjoint : Disjoint (Finset.filter (fun i => i < j) (Finset.univ : Finset (Fin k))) (Finset.filter (fun i => i > j) (Finset.univ : Finset (Fin k)))
                · apply Finset.disjoint_filter.mpr
                  intro i h1 h2
                  exact lt_asymm h2

                rw[h_eq_j, Finset.sum_singleton, h_neq_split, Finset.sum_union h_disjoint]
                ring

              rw[h_a_sum_split, h_b_sum_split]

              have h_lt_sum_eq : (Finset.sum (filter (fun i => i < j) Finset.univ) fun a_1 => a 0 a_1 * x a_1) = (Finset.sum (filter (fun i => i < j) Finset.univ) fun a_1 => b 0 a_1 * x a_1)
              · apply Finset.sum_congr rfl
                intro i hi
                simp at hi
                have h_eq : a 0 i = b 0 i := by exact h_eq_if_lt i hi
                rw[h_eq]

              have h_gt_sum_eq : (Finset.sum (filter (fun i => i > j) Finset.univ) fun a_1 => a 0 a_1 * x a_1) = (Finset.sum (filter (fun i => i > j) Finset.univ) fun a_1 => b 0 a_1 * x a_1)
              · apply Finset.sum_congr rfl
                intro i hi
                simp at hi
                have h_eq : a 0 i = b 0 i := by exact h_eq_if_gt i hi
                rw[h_eq]

              simp_rw[h_lt_sum_eq, h_gt_sum_eq]
              ring

            · exact h_eq_if_gt iκ h_gt

          exact h_f_inj

          have h_f_surj : ∀ b ∈ Finset.univ, ∃ a, ∃ (ha : a ∈ S₂), f a ha = b
          · intro b h_b

            have h_l1 (l : Fin k) (h_lj : ↑l < j) : ↑l < k - 1
            · have h_jk : ↑j < k := j.is_lt
              exact Nat.lt_of_lt_of_le h_lj (Nat.le_pred_of_lt h_jk)

            have h_l2 (l : Fin k) (h_lj : ¬(↑l < j)) (h_lj' : ¬(↑l = j)) : ↑l - 1 < k - 1
            · have h_lk : l < k := l.is_lt

              have h_cases : k < 1 ∨ k = 1 ∨ k > 1
              · exact Nat.lt_trichotomy k 1

              rcases h_cases with (h_klt | h_keq | h_kgt)
              · omega
              · have h_l0 : l = ⟨0, by exact Nat.lt_of_succ_le h_k⟩
                · apply Fin.ext
                  have h_l_lt_1 : l.val < 1
                  · simp
                    subst h_keq
                    interval_cases (l : ℕ)
                    rfl
                  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h_l_lt_1)
                have h_j0 : j = ⟨0, by exact Nat.lt_of_succ_le h_k⟩
                · apply Fin.ext
                  have h_j_lt_1 : j.val < 1 := by subst h_keq; exact j.isLt
                  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ h_j_lt_1)
                push_neg at h_lj'
                rw[h_l0, h_j0] at h_lj'
                contradiction
              · have h_l_geq_1 : 1 ≤ (l : ℕ)
                · have h_j_geq_0 : (j : Nat) ≥ 0 := Nat.zero_le _
                  have h_l_gt_j : (j : ℕ) < (l : ℕ)
                  · contrapose! h_lj'
                    have h_j_leq_l : (j : ℕ) ≤ (l : ℕ) := Nat.le_of_not_lt h_lj
                    exact Fin.ext (Nat.le_antisymm h_lj' h_j_leq_l)
                  have h_l_gt_0 : (0 : Nat) < (l : Nat) := Nat.lt_of_le_of_lt h_j_geq_0 h_l_gt_j
                  exact Nat.succ_le_of_lt h_l_gt_0
                omega


            let p₀ : (Matrix (Fin 1) (Fin k) α) := fun _ l => if h_lj : l < j then b ⟨l.val, by exact h_l1 l h_lj⟩ else (if h_lj' : l = j then 0 else b ⟨l.val - 1, by exact h_l2 l h_lj h_lj'⟩)
            let p : (Matrix (Fin 1) (Fin k) α) := fun _ l => if l ≠ j then (p₀ 0 l) else ((v i - Finset.sum (Finset.erase Finset.univ j) fun c => (p₀ 0 c) * x c) / x j)
            use p

            have h_p : p ∈ S₂
            · let inS₂ (g : Matrix (Fin 1) (Fin k) α) : Prop := g 0 j = (v i - Finset.sum (erase Finset.univ j) fun c => g 0 c * x c) / x j
              have hS₂_mem : S₂ = toFinset {g | inS₂ g} := by simp
              rw[hS₂_mem, ←Finset.mem_coe]
              have h_finseteq : ↑(toFinset {g | inS₂ g}) = {g | inS₂ g} := by simp
              rw[h_finseteq, Set.mem_setOf_eq]
              simp only[inS₂, p]
              simp [Finset.sum_congr]
              congr
              field_simp[h_j]
              let v_term := (v i - Finset.sum Finset.univ fun x_2 => (if h_lj : x_2 < j then b { val := ↑x_2, isLt := h_l1 x_2 h_lj } else if h_lj' : x_2 = j then 0 else b { val := ↑x_2 - 1, isLt := h_l2 x_2 h_lj h_lj' }) * x x_2)
              have h_v_term : v_term = (v i - Finset.sum Finset.univ fun x_2 => (if h_lj : x_2 < j then b { val := ↑x_2, isLt := h_l1 x_2 h_lj } else if h_lj' : x_2 = j then 0 else b { val := ↑x_2 - 1, isLt := h_l2 x_2 h_lj h_lj' }) * x x_2) := by rfl
              simp only [Finset.sum_ite, Finset.sum_sub_distrib, Finset.mem_univ, if_true]
              rw[←h_v_term]

              have h_j_sum : (Finset.sum (filter (fun x => x = j) Finset.univ) fun x_1 => v_term * x x_1 / x j) = v_term
              · have h_filter_eq_singleton : (Finset.filter (fun x => x = j) (Finset.univ : Finset (Fin k))) = {j}
                · ext x_1
                  simp [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton]
                rw[h_filter_eq_singleton]
                simp[Finset.sum_singleton]
                field_simp[h_j]

              rw[h_j_sum]
              ring_nf

              let sum_fun := fun x_1 => (if h_lj : x_1 < j then b { val := ↑x_1, isLt := h_l1 x_1 h_lj } else if h_lj' : x_1 = j then 0 else b { val := ↑x_1 - 1, isLt := h_l2 x_1 h_lj h_lj' }) * x x_1

              have h_sum_fun_zero : sum_fun j = 0 := by simp

              rw[←Finset.sum_erase (Finset.univ : Finset (Fin k)) h_sum_fun_zero]
              change (Finset.sum (erase Finset.univ j) fun x => sum_fun x) = (Finset.sum (filter (fun x => ¬x=j) Finset.univ) fun x => sum_fun x)

              have h_erase_eq_filter_not : (erase Finset.univ j) = (filter (fun x => ¬x=j) Finset.univ)
              · ext l
                simp [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ]

              rw[h_erase_eq_filter_not]


            use h_p
            funext l
            change (fun g h_g => (fun (l : Fin (k-1)) => if h_llt : l.val < j then (g 0 ⟨l.val, by exact h_k1 l⟩) else (g 0 ⟨l.val + 1, by exact h_k2 l⟩))) p h_p l = b l
            change (if h_llt : (l : ℕ) < (j : ℕ) then p 0 ⟨l.val, by exact h_k1 l⟩ else p 0 ⟨l.val + 1, by exact h_k2 l⟩) = b l

            split_ifs with h_if
            · let l_cast : (Fin k) := { val := ↑l, isLt := h_k1 l }
              change (fun _ l => if l ≠ j then (p₀ 0 l) else ((v i - Finset.sum (Finset.erase Finset.univ j) fun c => (p₀ 0 c) * x c) / x j)) 0 l_cast = b l
              change (if l_cast ≠ j then (p₀ 0 l_cast) else ((v i - Finset.sum (Finset.erase Finset.univ j) fun c => (p₀ 0 c) * x c) / x j)) = b l
              have h_l_neq_j : l_cast ≠ j
              · have h_l_cast_lt : (l_cast : ℕ) < (j : ℕ) := by simp[h_if]
                have h_l_cast_ne : (l_cast : ℕ) ≠ (j : ℕ) := by exact ne_of_lt h_l_cast_lt
                rw [Fin.val_ne_iff] at h_l_cast_ne
                exact h_l_cast_ne
              rw [if_pos h_l_neq_j]
              simp
              intro h_j_leq
              have h_jl_nat : (j : ℕ) ≤ (l : ℕ)
              · rw[Fin.le_iff_val_le_val] at h_j_leq
                have h_l_val : (l : ℕ) = (({ val := ↑l, isLt := h_k1 l } : (Fin k)) : ℕ) := by simp
                rw[h_l_val]
                exact h_j_leq
              omega
            · simp
              split_ifs with h_if₂ h_if₃
              · simp[Fin.ext_iff] at h_if₂
                omega
              · push_neg at h_if
                have h_lj : (↑l + 1 : ℕ) < (↑j : ℕ) := h_if₃
                omega
              · rfl


          exact h_f_surj

        rw[h_g_bijection]

        have h_codeword_card : (Finset.univ : Finset (Codeword (k-1) α)).card = (Fintype.card α)^(k-1)
        · rw[Finset.card_univ]
          unfold Codeword
          rw[Fintype.card_fun]
          simp

        rw[h_codeword_card]



      rw[h4₀, h4₁]

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
((Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}).card : ℝ) / (Fintype.card α : ℝ)^(n*k) ≤
((hamming_ball (d-1) (zero : Codeword n α)).card : ℝ) / (Fintype.card α : ℝ)^n := by {

  let S := Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}
  let S' := Set.toFinset {G : (Matrix (Fin n) (Fin k) α) | (Matrix.mulVec G x) ∈ hamming_ball (d-1) zero}

  have h_card_eq : S.card = S'.card
  · let f : (G : Matrix (Fin n) (Fin k) α) → G ∈ S → (Matrix (Fin n) (Fin k) α) := fun G _ ↦ G
    apply Finset.card_congr f

    have h_map : ∀ (G : Matrix (Fin n) (Fin k) α) (hG : G ∈ S), f G hG ∈ S'
    · simp
      unfold weight
      intro G h_dist_le_d
      have h_dist_leq_dminus1 : hamming_distance (Matrix.mulVec G x) zero ≤ d - 1
      · have h₁ : (hamming_distance (Matrix.mulVec G x) zero) + 1 ≤ d := by exact Nat.succ_le_of_lt h_dist_le_d
        have h₂ : (hamming_distance (Matrix.mulVec G x) zero) + 1 - 1 ≤ d - 1 := by exact Nat.sub_le_sub_right h₁ 1
        rw[Nat.add_sub_cancel] at h₂
        exact h₂
      rw [mem_toFinset]
      simp[h_dist_leq_dminus1]

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
      apply Nat.lt_of_le_pred
      simp[h_d]
      exact h_G'inS'
    exact h_surj

  simp_rw[h_card_eq]

  let matrix_uniformity := uniformity_lemma n k x h_x h_k

  unfold matrix_dist uniform_vector_dist at matrix_uniformity
  simp at matrix_uniformity

  have h_unif (v: Codeword n α) : (toFinset {G | Matrix.mulVec G x = v}).card / Fintype.card α ^ (n * k) = 1 / ((Fintype.card α : ℝ))^n -- TODO: Should this be ≤?
  · apply congr_fun at matrix_uniformity
    specialize matrix_uniformity v
    have h_filter_eq : ↑(filter (fun x_1 => Matrix.mulVec x_1 x = v) Finset.univ) = (toFinset {G | Matrix.mulVec G x = v})
    · ext y
      constructor
      · intro h_filter
        rw[Finset.mem_filter] at h_filter
        simp_rw[Set.mem_toFinset, Set.mem_setOf, h_filter]
      · intro h_finset
        rw[Set.mem_toFinset, Set.mem_setOf] at h_finset
        rw[Finset.mem_filter]
        simp[h_finset]

    rw[←h_filter_eq]
    have h_inv : ((Fintype.card α : ℝ) ^ n)⁻¹ = 1 / (Fintype.card α : ℕ) ^ n := by simp
    rw_mod_cast[←h_inv]
    exact matrix_uniformity

  have h_sum : ((toFinset {G | Matrix.mulVec G x ∈ hamming_ball (d - 1) zero}).card : ℝ) / (Fintype.card α : ℝ) ^ (n * k) = Finset.sum (Set.toFinset {v : Codeword n α | (hamming_distance v zero) ≤ d-1}) fun v => 1 / (Fintype.card α : ℝ)^n
  · simp[Finset.sum_const]
    have h_ball_eq_sum : (toFinset {G | Matrix.mulVec G x ∈ hamming_ball (d-1) zero}) = (Set.toFinset (⋃ (v : Fin n → α) (h_v : weight v ≤ d-1), {G : (Matrix (Fin n) (Fin k) α) | (Matrix.mulVec G x) = v}))
    · simp
      ext y
      constructor
      · intro h_ball
        simp
        apply Set.mem_toFinset.mp at h_ball
        apply Set.mem_toFinset.mp at h_ball
        simp at h_ball
        unfold weight
        simp[h_ball]
      · intro h_union
        apply Set.mem_toFinset.mp at h_union
        obtain ⟨v, hv⟩ := Set.mem_iUnion.mp h_union
        obtain ⟨hwt, hG⟩ := Set.mem_iUnion.mp hv
        have h_yxv : Matrix.mulVec y x = v := hG
        have h_yx_hd : hamming_distance (Matrix.mulVec y x) 0 ≤ d - 1 := by rw[h_yxv]; exact hwt
        have h_yx_set : Matrix.mulVec y x ∈ toFinset {c' | hamming_distance c' 0 ≤ d - 1} := Set.mem_toFinset.mpr h_yx_hd
        exact Set.mem_toFinset.mpr h_yx_set

    unfold hamming_ball at h_ball_eq_sum
    rw[h_ball_eq_sum]

    have h_card_eq_sum : (toFinset (⋃ (v : Codeword n α), ⋃ (_ : weight v ≤ d - 1), {G | Matrix.mulVec G x = v})).card = Finset.sum (Set.toFinset {v : Codeword n α | (hamming_distance v zero) ≤ d-1}) fun v => (toFinset {G | Matrix.mulVec G x = v}).card
    · let hamming_set : Finset (Codeword n α) := toFinset {v | hamming_distance v zero ≤ d - 1}
      let f : Codeword n α → Finset (Matrix (Fin n) (Fin k) α) := fun v => toFinset {G | Matrix.mulVec G x = v}
      let G_union : Finset (Matrix (Fin n) (Fin k) α) := hamming_set.biUnion f

      have h_G_union : G_union = toFinset (⋃ (v : Codeword n α), ⋃ (_ : weight v ≤ d - 1), {G | Matrix.mulVec G x = v})
      · ext G
        simp[Finset.mem_biUnion, Set.mem_toFinset, Set.mem_setOf_eq]
        constructor
        · intro h_a
          let ⟨a, h_adist, h_Ga⟩ := h_a
          rw[Set.mem_toFinset, Set.mem_setOf] at h_Ga
          rw[←h_Ga] at h_adist
          unfold weight
          exact h_adist
        · intro h_weight
          let a := Matrix.mulVec G x
          use a
          apply And.intro
          · exact h_weight
          · rw[Set.mem_toFinset, Set.mem_setOf]

      have h_disjoint : ∀ x ∈ hamming_set, ∀ y ∈ hamming_set, x ≠ y → Disjoint (f x) (f y)
      · intro a h_a b h_b h_ab
        simp
        rw[Finset.disjoint_iff_ne]
        intro G h_Ga H h_Ha
        rw[Set.mem_toFinset, Set.mem_setOf] at h_Ga h_Ha
        rw [←h_Ga, ←h_Ha] at h_ab
        by_contra h_GHeq
        have h_mul_eq : Matrix.mulVec G x = Matrix.mulVec H x := by simp[h_GHeq]
        contradiction

      rw[←h_G_union]
      apply Finset.card_biUnion h_disjoint

    rw[h_card_eq_sum]
    field_simp[matrix_uniformity]
    have h_preimage_card : ∀ (v : Codeword n α), ((toFinset {G | Matrix.mulVec G x = v}).card : ℝ) = ↑(Fintype.card α) ^ (n * k - n)
    · intro v₀
      specialize h_unif v₀
      field_simp at h_unif
      have h_card_exp : ↑(toFinset {G | Matrix.mulVec G x = v₀}).card  = ((Fintype.card α : ℝ) ^ (n * k)) / ((Fintype.card α : ℝ) ^ n) := by field_simp[h_unif]
      field_simp[h_card_exp]
      norm_cast
      simp_rw[←pow_add]
      have h_pow_eq : (n * k) - n + n = n * k
      · rw[Nat.sub_add_cancel]
        have h_k' : k > 0 := Nat.pos_of_ne_zero (ne_of_gt h_k)
        have h_symm : n * k = k * n := by simp[Nat.mul_comm]
        rw[h_symm]
        exact Nat.le_mul_of_pos_left n h_k' -- Proves n ≤ n*k using k > 0
      rw[h_pow_eq]
    simp_rw[h_preimage_card, Finset.sum_const, nsmul_eq_mul]

    have h_exp : (Fintype.card α : ℝ)^(n * k - n) * (Fintype.card α : ℝ)^n = (Fintype.card α : ℝ)^(n * k)
    · simp_rw[←pow_add]
      have h_pow_eq : (n * k) - n + n = n * k
      · rw[Nat.sub_add_cancel]
        have h_k' : k > 0 := Nat.pos_of_ne_zero (ne_of_gt h_k)
        have h_symm : n * k = k * n := by simp[Nat.mul_comm]
        rw[h_symm]
        exact Nat.le_mul_of_pos_left n h_k' -- Proves n ≤ n*k using k > 0
      rw[h_pow_eq]

    rw[←h_exp]
    simp[mul_assoc]


  have h_ball_size : Finset.sum (Set.toFinset {v : Codeword n α | (hamming_distance v zero) ≤ d-1}) (fun v => 1 / (Fintype.card α : ℝ)^n) = ((hamming_ball (d-1) (zero : Codeword n α)).card : ℝ) / (Fintype.card α : ℝ)^n
  · have h_sum_mult : Finset.sum (Set.toFinset {v : Codeword n α | (hamming_distance v zero) ≤ d-1}) (fun v => 1 / (Fintype.card α : ℝ)^n) = (Set.toFinset {v : Codeword n α | (hamming_distance v zero) ≤ d-1}).card * (1 / (Fintype.card α : ℝ)^n)
    · simp[Finset.sum_const]
    rw[h_sum_mult]
    field_simp

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
      have h_inone : ∃x, G ∈ {G : (Matrix (Fin n) (Fin k) α) | weight (Matrix.mulVec G x) < d}
      · simp[mem_iUnion] at h_Su
        exact h_Su
      simp[h_inone]
      rcases h_inone with ⟨x, h_xset⟩
      rw[Set.mem_setOf] at h_xset
      use x

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

def list_decodable (ρ : ℝ) (hρ₁: 0 ≤ ρ) (hρ₂: ρ ≤ 1) (n L : ℕ) (hL : L ≥ 1) (C : Code n α) : Prop :=
  (∀ y : Codeword n α, (hamming_ball (Nat.floor (ρ*n)) y ∩ C).card ≤ L)

theorem qary_entropy_pos (q : ℕ) (p : ℝ) (hq : q = (Fintype.card α)) (hp : 0 < p ∧ p ≤ 1 - 1 / (q : ℝ)) :
  0 < p * Real.logb (q : ℝ) ((q : ℝ) - 1) - p * Real.logb (q : ℝ) p - (1 - p) * Real.logb (q : ℝ) (1 - p):= by
  have hq_1 : (1 : ℝ) < (q : ℝ) := by
    rw [hq]
    exact_mod_cast Fintype.one_lt_card
  have : 0 < 1 - (1 : ℝ) / q := lt_of_lt_of_le hp.1 hp.2
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have : (1 : ℝ) / (q : ℝ) < 1 := by
      have := this; linarith
    exact lt_trans (by norm_num) hq_1

  have hp_1 : p < 1 := by
    have : p ≤ 1 - 1 / (q : ℝ) := hp.2
    exact lt_of_le_of_lt this (by
      have : (0 : ℝ) < 1 / (q : ℝ) := by
        have : 0 < (q : ℝ) := hqpos; exact one_div_pos.mpr this
      linarith)
  have h1p_0 : 0 < 1 - p := by linarith
  have h1p_1 : 1 - p < 1 := by linarith

  have hlogq_pos : 0 < Real.log (q : ℝ) := by
    apply (Real.log_pos_iff hqpos).2 hq_1

  have := show
      0 <
        p * (Real.log ((q : ℝ) - 1) / Real.log (q : ℝ))
        - p * (Real.log p / Real.log (q : ℝ))
        - (1 - p) * (Real.log (1 - p) / Real.log (q : ℝ)) by
    simpa [Real.logb] using
      (show
        0 <
          p * Real.logb (q : ℝ) ((q : ℝ) - 1)
          - p * Real.logb (q : ℝ) p
          - (1 - p) * Real.logb (q : ℝ) (1 - p) from ?_)
  suffices 0 < p * Real.log ((q : ℝ) - 1) - p * Real.log p - (1 - p) * Real.log (1 - p) by
    have := (div_pos_iff.mpr (Or.inl ⟨this, hlogq_pos⟩))
    simp only [Real.logb, div_eq_mul_inv]
    simp only [div_eq_mul_inv] at this
    have hdistrib : (p * Real.log (↑q - 1) - p * Real.log p - (1 - p) * Real.log (1 - p)) * (Real.log ↑q)⁻¹ = p * (Real.log (↑q - 1) * (Real.log ↑q)⁻¹) - p * (Real.log p * (Real.log ↑q)⁻¹) - (1 - p) * (Real.log (1 - p) * (Real.log ↑q)⁻¹) := by
      simp [sub_eq_add_neg]
      rw [distrib_three_right]
      simp [mul_assoc]
    rw [hdistrib] at this
    exact this

  have h_logp_neg : Real.log p < 0 :=
    Real.log_neg hp.1 hp_1
  have h_log1p_neg : Real.log (1 - p) < 0 :=
    Real.log_neg h1p_0 h1p_1
  have h_ent_pos :
      0 < - p * Real.log p - (1 - p) * Real.log (1 - p) := by
    have hp_neg: 0 < -p * Real.log p := by
      have : Real.log p < 0 := h_logp_neg
      have := (mul_neg_of_pos_of_neg hp.1 this)
      simpa [neg_mul, neg_neg] using this
    have h1p_neg: 0 < -(1 - p) * Real.log (1 - p) := by
      have : Real.log (1 - p) < 0 := h_log1p_neg
      have := (mul_neg_of_pos_of_neg h1p_0 this)
      linarith
    have := add_pos hp_neg h1p_neg
    ring_nf
    linarith [this]

  have : 0 ≤ Real.log ((q : ℝ) - 1) := by
    have : (q : ℝ) ≥ 2 := by
      have : 1 < q := by
        rw [hq]
        exact_mod_cast Fintype.one_lt_card
      exact_mod_cast (by linarith [this])
    have : (q : ℝ) - 1 ≥ 1 := by linarith
    exact Real.log_nonneg this
  have : 0 ≤ p * Real.log ((q : ℝ) - 1) :=
    mul_nonneg (le_of_lt hp.1) this
  have : 0 < p * Real.log ((q : ℝ) - 1)
                + (- p * Real.log p - (1 - p) * Real.log (1 - p)) := by
    exact add_pos_of_nonneg_of_pos this h_ent_pos
  ring_nf at this
  ring_nf
  exact this
  simp [Real.logb]
  linarith [this]

theorem list_decoding_capacity
  (q : ℕ) (p : ℝ) (hq : q = (Fintype.card α)) (hp : 0 < p ∧ p ≤ 1 - 1/q) (L : ℕ) (hL : 1 ≤ L):
  let r := 1 - (qaryEntropy q p) - 1 / (L : ℝ);
  let M := Nat.floor ((q : ℝ) ^ (r * n));
  ∃ C : Code n α,
    (M ≤ C.card) ∧ (list_decodable p (by linarith [hp]) (by linarith [hp, one_div_nonneg.2 (show (0 : ℝ) ≤ (q : ℝ) from by exact_mod_cast (Nat.zero_le q))]) n L hL C)
:= by
  classical
  intro r M
  have hq_pos : (1 : ℝ) < (q : ℝ) := by
    rw [hq]
    exact_mod_cast Fintype.one_lt_card
  have hr : r ≤ 1 := by
    have hH : 0 < qaryEntropy q p := qary_entropy_pos q p hq hp
    have hL0 : 0 ≤ 1 / (L : ℝ) := by
      have : (0 : ℝ) < (L : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (Nat.succ_pos 0) hL)
      exact one_div_nonneg.mpr (le_of_lt this)
    dsimp [r]
    linarith

  let y := Classical.arbitrary (Codeword n α)

  let radius : ℕ := Nat.floor (p * n)
  let N : ℕ := q ^ n

  let Ω : Finset (Code n α) := {C : Code n α | C.card = M}.toFinset
  have hΩcard : Ω.card = Nat.choose N M := by
    have h : (Finset.univ : Finset (Codeword n α)).card = q ^ n := by
      simp [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hq]
    simp [h]
  have hΩcardpos : (0 : ℝ) < (Ω.card : ℝ) := by
    rw [hΩcard]
    have m_le_n : M ≤ N := by
      show Nat.floor ((q : ℝ) ^ (r * n)) ≤ q ^ n
      have hr : r * n ≤ n := by
        exact mul_le_of_le_one_left (Nat.cast_nonneg n) hr
      have : (q : ℝ) ^ (r * n) ≤ (q : ℝ) ^ (n : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [hq_pos]) hr
      have : Nat.floor ((q : ℝ) ^ (r * n)) ≤ (q : ℝ) ^ (n : ℝ) := by
        -- exact Nat.floor_le (Real.rpow_nonneg_of_nonneg (by linarith [hq_pos]) (r * n))
        sorry
      norm_cast at this
    apply Nat.choose_pos at m_le_n
    exact_mod_cast m_le_n

  let bad_code_at (C : Code n α) (y : Codeword n α) := ((hamming_ball radius y) ∩ C).card ≥ L + 1
  let bad_codes_at (y : Codeword n α) := {C : (Code n α) | bad_code_at C y}
  let bad_codes := {C: (Code n α) | ∃ y : Codeword n α, bad_code_at C y}
  let bad_in_Ω : Finset (Code n α) := Ω.filter (fun C => C ∈ bad_codes)

  -- 1) one center
  have one_center_bound :
    ((Ω.filter (fun C => C ∈ bad_codes_at y)).card : ℝ) / (Ω.card : ℝ)
    ≤ (Nat.choose ((hamming_ball radius y).card) (L+1) : ℝ)
      * (Nat.choose M (L+1) : ℝ) / (Nat.choose N (L+1) : ℝ)
  := by
    sorry

  -- 2) union bound over all centers
  have union_bound :
    (bad_in_Ω.card : ℝ) / (Ω.card : ℝ)
    ≤ N * (Nat.choose ((hamming_ball radius y).card) (L+1) : ℝ)
      * (Nat.choose M (L+1) : ℝ) / (Nat.choose N (L+1) : ℝ)
  := by
    sorry

  -- 3) |B| ≤ 2^{H(p) n}
  have hamming_ball_vol_bound :
    (hamming_ball radius y).card ≤ Real.rpow q (qaryEntropy q p * n)
  := by
    have hα : Nontrivial α := inferInstance
    have hr : radius = ⌊↑n * p⌋₊ := by rw [mul_comm]
    rw [hr]
    refine (hamming_ball_size_asymptotic_upper_bound q n p hq hα hp) y

  -- 4) choose ≤ power/(L+1)!
  have choose_bound :
    (Nat.choose M (L+1) : ℝ) ≤ (M : ℝ)^(L+1) / (Nat.factorial (L+1))
  := by
    sorry

  -- 5) substitute M=⌊2^{r n}⌋, r = 1 - H(p) - 1/L and simplify to < 1
  have bad_frac_lt_one :
    (bad_in_Ω.card : ℝ) / (Ω.card : ℝ) < 1
  := by
    -- combine union_bound, hamming_ball_vol_bound, choose_bound and r-definition
    sorry

  -- finish proof via contradiction
  by_contra hcontra
  have all_bad : bad_in_Ω.card = Ω.card := by
    simp at hcontra
    have hΩeq : bad_in_Ω = Ω := by
      simp
      ext C
      constructor
      · intro hC
        simp at hC
        specialize hcontra C
        rw [hC.1] at hcontra
        simp at hcontra
        have hsub : C ⊆ (Finset.univ : Finset _) := by
          intro x hx
          simp
        exact (mem_powersetCard.mpr ⟨hsub, by simp [hC.1]⟩)
      · intro hC
        have hbad : ∃ y, L + 1 ≤ (toFinset {c' | hamming_distance c' y ≤ ⌊p * ↑n⌋₊} ∩ C).card := by
          classical
          obtain ⟨-, hcard⟩ := Finset.mem_powersetCard.1 hC
          have hM : M ≤ C.card := by simp [hcard]
          simp [M, r] at hM
          have : p ≤ (1 : ℝ) := le_trans hp.2 (by norm_num)
          have : ¬ list_decodable p (by linarith [hp.1]) this n L hL C := hcontra C hM
          have : ∃ y, ¬ (hamming_ball radius y ∩ C).card ≤ L := by
            unfold list_decodable at this
            exact not_forall.1 this
          rcases this with ⟨y', hy'⟩
          have : L + 1 ≤ (hamming_ball radius y' ∩ C).card :=
            Nat.succ_le_of_lt (Nat.lt_of_not_ge hy')
          simpa [radius, hamming_ball] using ⟨y', this⟩
        refine Finset.mem_filter.mpr ?_
        exact ⟨hC, hbad⟩
    rw [hΩeq]

  have hΩnonzero :
    (Ω.card : ℝ) ≠ 0
  := by
    rw [hΩcard]
    rw [ne_iff_lt_or_gt]
    right
    rw [← hΩcard]
    exact hΩcardpos

  have frac_eq_one :
    (bad_in_Ω.card : ℝ) / (Ω.card : ℝ) = 1
  := by
    rw [all_bad]
    exact div_self hΩnonzero

  exact (not_lt.mpr le_rfl) (frac_eq_one ▸ bad_frac_lt_one)
