import TCSlib.CodingTheory.Basic

set_option linter.unusedSectionVars false

/-!
# Hamming Bound

This file establishes the **Hamming bound** (also called the sphere-packing bound): for a code
`C` of block-length `n` and minimum distance `d` over a `q`-ary alphabet `α`,

  |C| · Vol(n, ⌊(d-1)/2⌋) ≤ |α|^n,

where `Vol(n, t) = Σ_{i=0}^{t} C(n,i) · (|α|-1)^i` is the volume of a Hamming ball of
radius `t`.

## Main Results

* `hamming_ball_size` : the exact volume formula for Hamming balls.
* `hamming_ball_non_intersect` : balls of radius `⌊(d-1)/2⌋` around distinct codewords
  of a code with minimum distance `d` are disjoint.
* `hamming_bound` : the Hamming (sphere-packing) bound.

-/

open Set Filter Asymptotics Finset

namespace CodingTheory
namespace Codeword

variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α]
variable {n k : ℕ}

/-- **Volume formula**: the Hamming ball of radius `l` centred at any codeword has exactly
    `Σ_{i=0}^{l} C(n,i) · (|α|-1)^i` elements. -/
theorem hamming_ball_size (n l : ℕ) :
    ∀ c : Codeword n α,
      (hamming_ball l c).card =
        Finset.sum (Finset.range (l + 1)) (λ i => Nat.choose n i * (Fintype.card α - 1)^i) := by {
  intro c
  simp

  have h_card_x0 : ∀ d, {c' : Codeword n α | hamming_distance c' Codeword.zero = d}.toFinset.card = Nat.choose n d * (Fintype.card α - 1)^d := by
    intro d
    dsimp [hamming_distance, zero]

    let d_comb : Finset (Finset (Fin n)) := Finset.powersetCard d Finset.univ
    have h_card_d_comb : d_comb.card = Nat.choose n d := by
      simp [d_comb]

    let α_nonzero := {x : α | x ≠ 0}.toFinset
    have h_card_α_nonzero : α_nonzero.card = Fintype.card α - 1 := by
      rw [toFinset_card]
      simp

    have h_card_fun : ∀ s ∈ d_comb, Fintype.card (s → α_nonzero) = (Fintype.card α - 1)^d := by
      intro s hs
      rw [Fintype.card_fun]
      rw [show Fintype.card { x // x ∈ α_nonzero } = Fintype.card α - 1 by
        simpa using h_card_α_nonzero]
      dsimp[d_comb] at hs
      simp! at *
      rw[hs]

    let f := fun (s : Finset (Fin n)) ↦ (Finset.univ : Finset (s → α_nonzero))

    have : ∀ s ∈ d_comb, (f s).card = (Fintype.card α - 1)^d := by intro s hs; exact h_card_fun s hs

    let S := d_comb.sigma f
    have h_card_S : S.card = Nat.choose n d * (Fintype.card α - 1) ^ d := by
      simp [S]
      rw [Finset.sum_eq_card_nsmul this, h_card_d_comb]
      rfl

    rw[←h_card_S]
    let f' : (s : ((k : Finset (Fin n)) × ({ x // x ∈ k } → { x // x ∈ α_nonzero }))) → s ∈ S → Codeword n α := fun s _ ↦ (fun i ↦ if h : i ∈ s.1 then s.2 ⟨i, h⟩ else 0)

    symm
    apply Finset.card_bij f'

    -- f' maps S to the hamming ball
    have h_f'_map_to_ball: ∀ (a : (k : Finset (Fin n)) × ({ x // x ∈ k } → { x // x ∈ α_nonzero })) (ha : a ∈ S), f' a ha ∈ toFinset {c' | hammingDist c' zero = d} := by
      intros a ha
      dsimp[S] at ha
      apply Finset.mem_sigma.1 at ha
      rw[toFinset]
      simp [hammingDist]
      have : (filter (fun i => i ∈ a.fst) Finset.univ).card = d := by
        simpa [d_comb] using ha.1
      rw[← this]
      rw[← Fintype.card_subtype]
      apply Fintype.card_of_subtype
      simp
      intros x
      constructor
      · intro hx
        push_neg
        refine dite_ne_right_iff.mpr ?_
        use hx
        have : ↑(a.snd ⟨x, hx⟩) ∈  α_nonzero := by
          exact coe_mem (Sigma.snd a { val := x, property := hx })
        simp[α_nonzero] at this
        exact this
      · intros hx
        simp[f'] at hx
        rcases hx with ⟨h₁, h₂⟩
        exact h₁

    exact h_f'_map_to_ball

    -- f' is injective
    have h_f'_injective: ∀ (a : (k : Finset (Fin n)) × ({ x // x ∈ k } → { x // x ∈ α_nonzero })) (ha : a ∈ S),
     ∀ (b : (k : Finset (Fin n)) × ({ x // x ∈ k } → { x // x ∈ α_nonzero })) (hb : b ∈ S), f' a ha = f' b hb → a = b := by
      intros a h_a b h_b
      intro h_feq
      let f_a := (f' a h_a)
      let f_b := (f' b h_b)
      have fab_eq: f_a = f_b := by exact h_feq

      have first_eq: a.1 = b.1 := by
        ext x
        constructor
        · intro h1
          by_contra h_xb
          have h_fbzero: f_b x = 0 := by simp[f_b, f']; intro h_inb; exact absurd h_inb h_xb
          have h_fazero: f_a x = 0 := by rw[fab_eq]; exact h_fbzero
          dsimp[f_a, f'] at h_fazero; simp at h_fazero
          let a₀ := a.2 ⟨x, h1⟩
          apply h_fazero at h1
          have h_azero : ¬a₀.val ≠ 0 := by simp; exact h1
          have h_anonzero : a₀.val ∈ α_nonzero := by exact a₀.property
          rw [Set.mem_toFinset, Set.mem_setOf] at h_anonzero
          exact absurd h_anonzero h_azero
        · intro h2
          by_contra h_xa
          have h_fazero: f_a x = 0 := by simp[f_a, f']; intro h_ina; exact absurd h_ina h_xa
          have h_fbzero: f_b x = 0 := by rw[←fab_eq]; exact h_fazero
          dsimp[f_b, f'] at h_fbzero; simp at h_fbzero
          let b₀ := b.2 ⟨x, h2⟩
          apply h_fbzero at h2
          have h_bzero : ¬b₀.val ≠ 0 := by simp; exact h2
          have h_bnonzero : b₀.val ∈ α_nonzero := by exact b₀.property
          rw [Set.mem_toFinset, Set.mem_setOf] at h_bnonzero
          exact absurd h_bnonzero h_bzero

      have h_2eq : ({ x // x ∈ b.fst } → { x // x ∈ α_nonzero }) = ({ x // x ∈ a.fst } → { x // x ∈ α_nonzero }) := by rw[first_eq]

      let b' := cast h_2eq b.2
      have h_bheq : HEq b' b.2 := by simp[b']

      ext
      rw[first_eq]
      refine HEq.symm (heq_of_cast_eq h_2eq ?h_f'_injective.a.x)
      funext x
      suffices b' x = a.snd x by {
        exact this
      }

      have h₁' : f_a x = a.2 x := by
        simp [f_a, f']
      have h₂ : (f_a x) = (f_b x) := by rw[fab_eq]
      have h₃ : (f_b x) = (b' x) := by
        dsimp[f_b, f']
        have h₃' : ↑x ∈ b.1 := by
          have h₃'' : ↑x ∈ a.1 := by simp
          rw[← first_eq]
          exact h₃''
        simp[h₃']

        have : Sigma.snd b { val := ↑x, property := (h₃' : ↑x ∈ b.fst) } = b' x := by
          dsimp[f_b, f']
          apply congr_heq -- Life Saving Theorem
          exact h_bheq.symm
          refine (Subtype.heq_iff_coe_eq ?this.h₂.h).mpr rfl
          rw[first_eq]
          tauto
        exact this


      rw[h₃] at h₂
      rw[h₂] at h₁'
      exact SetCoe.ext h₁'

    exact h_f'_injective

    -- f' is surjective
    have h_f'_surjective: ∀ b ∈ toFinset {c' | hammingDist c' zero = d}, ∃ a, ∃ (ha : a ∈ S), f' a ha = b := by
      intro b
      intro h_b
      let a₁ := toFinset { i | b i ≠ 0 }

      have h_y : ∀ y ∈ a₁, (b ↑y) ∈ α_nonzero := by
        intro y hy
        simp [α_nonzero, a₁] at hy ⊢
        exact hy

      let a₂ (y : { x // x ∈ a₁ }) : { x // x ∈ α_nonzero } := ⟨b y, by {
        apply h_y
        exact y.property
      }⟩

      use ⟨a₁, a₂⟩

      have h_a : ⟨a₁, a₂⟩ ∈ S := by
        simp[a₁, a₂, S, d_comb]
        have h_d : hammingDist b zero = d := by rw[Set.mem_toFinset, Set.mem_setOf] at h_b; exact h_b
        unfold hammingDist at h_d
        have h_setEq : (toFinset {i | ¬b i = 0}) = (filter (fun i => b i ≠ zero i) Finset.univ) := by
          simp
        constructor
        · exact h_d
        · simp[f]

      use h_a
      simp[a₁, a₂, f, f', S, d_comb]
      funext x

      by_cases h_x : b x = 0
      · simp
        intro h'
        rw[h_x]
      · simp
        intro h'
        by_contra h_x
        have h_xb : x ∈ toFinset {i | ¬b i = 0} := by
          apply Set.mem_toFinset.2
          simp
          contrapose h_x
          simp at h_x
          simp
          rw[h_x]
        (expose_names; exact h_x_1 h')

    exact h_f'_surjective




  have h_card_dist_eq : ∀ d, {c' : Codeword n α | hamming_distance c' c = d}.toFinset.card = Nat.choose n d * (Fintype.card α - 1)^d := by
    intro d
    rw[← h_card_x0]
    let f : Codeword n α → Codeword n α := fun x ↦ sub x c
    apply Finset.card_bij (fun a _ ↦ f a)
    simp [toFinset]
    · intros a ha
      dsimp [hamming_distance, sub] at *
      rw[hammingDist_eq_hammingNorm] at ha
      exact ha
    · intros a b ha hb hfab
      simp [toFinset] at *
      ext i
      apply funext_iff.1 at hfab
      specialize hfab i
      simp[f] at hfab
      exact hfab
    · intros b hb
      use add b c
      simp [toFinset, hamming_distance] at *
      constructor
      · rw[hammingDist_eq_hammingNorm]
        have : add b c - c = b := by ext i; simp
        rw[this]
        exact hb
      · ext i
        simp[f]




  induction l
  · simp [hamming_distance]
    refine (Fintype.existsUnique_iff_card_one fun x => x = c).mp ?_
    simp
  · expose_names

    rw[Nat.succ_add]
    rw[Finset.sum_range_succ]
    rw[← h]

    have : Fintype.card { x // hamming_distance x c ≤n_1+ 1 } = Fintype.card { x // hamming_distance x c ≤n_1} + Fintype.card { x // hamming_distance x c = n_1 + 1} := by
      have : fun x ↦ hamming_distance x c ≤ n_1 + 1 = fun x ↦ hamming_distance x c ≤ n_1 ∨ hamming_distance x c = n_1 + 1 := by
        ext x
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

      have : {x // hamming_distance x c ≤ n_1 + 1} = {x // hamming_distance x c ≤ n_1 ∨ hamming_distance x c = n_1 + 1 } := by exact congrArg Subtype this

      have : Fintype.card {x // hamming_distance x c ≤ n_1 + 1} = Fintype.card {x // hamming_distance x c ≤ n_1 ∨ hamming_distance x c = n_1 + 1 } := by exact Fintype.card_congr' this

      rw[this]

      have : Disjoint (fun x ↦ hamming_distance x c ≤ n_1)  (fun x ↦ hamming_distance x c = n_1 + 1) := by
        apply Pi.disjoint_iff.2
        intros c'
        simp
        intro hc'
        linarith

      apply Fintype.card_subtype_or_disjoint
      exact this

    rw[Fintype.card_subtype, Fintype.card_subtype, Fintype.card_subtype] at this
    rw[this]
    simp
    have : {c' : Codeword n α | hamming_distance c' c = n_1 + 1}.toFinset.card = Nat.choose n (n_1 + 1) * (Fintype.card α - 1)^(n_1 + 1) := by exact h_card_dist_eq (n_1 + 1)
    simp at this
    linarith
}

/-- Hamming balls of radius `⌊(d-1)/2⌋` around distinct codewords of a code with minimum
    distance `d` are disjoint: no point can lie within that radius of two distinct codewords. -/
lemma hamming_ball_non_intersect {d} (C : Code n α) (h : distance C d) (h' : 0 < d) :
    ∀ c₁ c₂ : Codeword n α, (c₁ ∈ C ∧ c₂ ∈ C ∧ c₁ ≠ c₂) →
      ∀ c' : Codeword n α,
        c' ∈ (hamming_ball (Nat.floor (((d : ℝ)-1)/2)) c₁) →
        c' ∉  (hamming_ball (Nat.floor (((d : ℝ)-1)/2)) c₂) := by {
  intros c₁ c₂ hc₁₂ c' hc'

  dsimp [hamming_ball, hamming_distance] at *

  have h_dist_c₁₂ : hamming_distance c₁ c₂ ≥ d := by exact h.2 c₁ hc₁₂.1 c₂ hc₁₂.2.1 hc₁₂.2.2

  have h_dist_c₁' : (hamming_distance c₁ c') ≤ (Nat.floor (((d : ℝ)-1)/2)) := by
    apply Set.mem_toFinset.1 at hc'
    simp at hc'
    rw[hammingDist_comm c' c₁] at hc'
    exact hc'

  by_contra h_dist_c'₂
  apply Set.mem_toFinset.1 at h_dist_c'₂
  simp at h_dist_c'₂

  have : (Nat.floor (((d : ℝ)-1)/2)) ≤ ((d : ℝ)-1)/2 := by
    apply Nat.floor_le
    apply div_nonneg
    simp
    exact h'
    linarith

  have : (Nat.floor (((d : ℝ)-1)/2)) + (Nat.floor (((d : ℝ)-1)/2)) ≤ ((d - (1 : ℕ) ) : ℝ) := by simp; linarith

  have : ((Nat.floor (((d : ℝ)-1)/2)) + (Nat.floor (((d : ℝ)-1)/2))) < d := by
    suffices (Nat.floor (((d : ℝ)-1)/2)) + (Nat.floor (((d : ℝ)-1)/2)) ≤ d - 1 by {
      exact Nat.lt_of_le_pred h' this
    }
    rw[← Nat.cast_sub] at this
    rw[← Nat.cast_add] at this
    exact Nat.cast_le.1 this
    linarith

  have h_cont : hamming_distance c₁ c₂ < d := by
    simp [hamming_distance] at *
    calc
      hammingDist c₁ c₂ ≤ hammingDist c₁ c' + hammingDist c' c₂ := by exact hammingDist_triangle c₁ c' c₂
      _                 ≤ (Nat.floor (((d : ℝ)-1)/2)) + (Nat.floor (((d : ℝ)-1)/2))    := by linarith [h_dist_c₁', h_dist_c'₂]
      _                 < d                                     := by linarith[this]

  linarith
}

/-- Helper: Hamming balls of radius `⌊(d-1)/2⌋` around distinct codewords are pairwise
    disjoint as `Finset`s. -/
lemma hamming_ball'_disjoint {d} (C : Code n α) (h : distance C d) (h' : 0 < d) :
    ∀ c₁ c₂ : Codeword n α, (c₁ ∈ C ∧ c₂ ∈ C ∧ c₁ ≠ c₂) →
      Disjoint (hamming_ball (Nat.floor (((d : ℝ) - 1)/2)) c₁)
               (hamming_ball (Nat.floor (((d : ℝ)-1)/2)) c₂) := by {
  intros c₁ c₂ hc₁₂
  dsimp [hamming_ball]
  apply Set.disjoint_toFinset.2
  apply Set.disjoint_iff.2
  intros c' hc'
  simp at *
  rcases hc' with ⟨hc'₁, hc'₂⟩
  have : c' ∈ (hamming_ball (Nat.floor (((d : ℝ)-1)/2)) c₁) := by
    dsimp [hamming_ball]
    apply Set.mem_toFinset.2
    simp
    exact hc'₁

  apply hamming_ball_non_intersect C h h' c₁ c₂ hc₁₂ c'
  exact this
  simp
  exact hc'₂
}

/-- **Hamming bound** (sphere-packing bound): a code `C` of block-length `n` and minimum
    distance `d` over an alphabet `α` with `|α| > 1` satisfies
    `|C| ≤ |α|^n / Vol(n, ⌊(d-1)/2⌋)`. -/
theorem hamming_bound (n d : ℕ) (C : Code n α) (h : distance C d) (h'' : Fintype.card α > 1)
    (hd : 0 < d) :
    C.card ≤ Fintype.card α ^ n /
      (Finset.sum (Finset.range ((Nat.floor (((d : ℝ)-1)/2)) + 1))
        (λ i => Nat.choose n i * (Fintype.card α - 1)^i)) := by {
  have h1 : 0 < Finset.sum (Finset.range ((Nat.floor (((d : ℝ)-1)/2)) + 1)) (λ i=> Nat.choose n i * (Fintype.card α - 1)^i) := by
    apply Finset.sum_pos
    intros i hi
    apply mul_pos
    · apply Nat.choose_pos
      have : (Nat.floor (((d : ℝ)-1)/2)) + 1 ≤ d := by
        suffices (Nat.floor (((d : ℝ)-1)/2)) ≤ d - 1 by exact Nat.add_le_of_le_sub hd this
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
    · apply Nat.pow_pos
      simp
      exact h''
    simp


  suffices C.card * (Finset.sum (Finset.range ((Nat.floor (((d : ℝ)-1)/2)) + 1)) (λ i=> Nat.choose n i * (Fintype.card α - 1)^i)) ≤ Fintype.card α ^ n by exact (Nat.le_div_iff_mul_le h1).mpr this

  let S : Finset (Codeword n α) := Finset.univ
  have h_Scard: S.card = Fintype.card α ^ n := by simp[S]

  have h_disjoint : (C : Set (Codeword n α)).PairwiseDisjoint (fun c ↦ (hamming_ball (Nat.floor (((d:ℝ)-1)/2)) c)) := by
    intros x hx y hy hxy
    simp at hx hy
    exact hamming_ball'_disjoint C h hd x y ⟨hx, hy, hxy⟩

  let SU : Finset (Codeword n α) := Finset.disjiUnion C (fun c ↦ (hamming_ball (Nat.floor (((d:ℝ)-1)/2)) c)) h_disjoint


  have h_SUcard : SU.card = C.card * (Finset.sum (Finset.range ((Nat.floor (((d : ℝ)-1)/2)) + 1)) (λ i=> Nat.choose n i * (Fintype.card α - 1)^i)) := by
    rw[Finset.card_disjiUnion]
    apply Finset.sum_eq_card_nsmul
    exact fun a _ => hamming_ball_size n (Nat.floor (((d : ℝ)-1)/2)) a

  calc
    (C.card * Finset.sum (Finset.range ((Nat.floor (((d : ℝ)-1)/2)) + 1)) fun i => Nat.choose n i * (Fintype.card α - 1) ^ i) = SU.card := by exact h_SUcard.symm
    _                                                                                                            ≤ S.card  := by exact Finset.card_le_univ SU
    _                                                                                                            = Fintype.card α ^ n   := by exact h_Scard


}

end Codeword
end CodingTheory
