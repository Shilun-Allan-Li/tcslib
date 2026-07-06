/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hamming Balls and Spheres

## Main results

- `CommunicationComplexity.hammingBall`: Finset of codewords within Hamming distance `r` of a center word
- `CommunicationComplexity.hammingSphere`: Finset of codewords at exactly Hamming distance `r` from a center word
- `CommunicationComplexity.hammingBall_card`: cardinality of a Hamming ball equals `ballVol n r q`
- `CommunicationComplexity.hammingSphere_card`: cardinality of a Hamming sphere equals `C(n, k) · (q-1)^k`

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

/-- A codeword of length `n` over alphabet `α`. -/
abbrev Word (n : ℕ) (α : Type*) := Fin n → α

/-- The Hamming ball of radius `r` centered at `u`: all words within distance `r`. -/
def hammingBall (u : Word n α) (r : ℕ) : Finset (Word n α) :=
  Finset.univ.filter (fun v => hammingDist u v ≤ r)

/-- The Hamming sphere of radius `r` centered at `u`: all words at exactly distance `r`. -/
def hammingSphere (u : Word n α) (r : ℕ) : Finset (Word n α) :=
  Finset.univ.filter (fun v => hammingDist u v = r)

/-- The volume of a Hamming ball: `Σ_{i=0}^{t} C(n, i) · (q-1)^i`. -/
def ballVol (n t q : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (t + 1), Nat.choose n i * (q - 1) ^ i

/-! ### Sphere and ball decomposition -/

lemma hammingSpheres_disjoint (u : Word n α) (r t : ℕ) (hrt : r ≠ t) :
    Disjoint (hammingSphere u r) (hammingSphere u t) := by
  simp only [hammingSphere, Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
  intro x h1 h2; omega

lemma hammingSpheres_pairwise_disjoint (u : Word n α) (r : ℕ) :
    Set.PairwiseDisjoint (Finset.range r) (fun t => hammingSphere u t) :=
  fun _ _ _ _ hst => hammingSpheres_disjoint u _ _ hst

lemma hammingBall_eq_hammingSpheres (u : Word n α) (r : ℕ) :
    hammingBall u r = Finset.disjiUnion (Finset.range (r + 1))
      (fun k => hammingSphere u k) (hammingSpheres_pairwise_disjoint u (r + 1)) := by
  ext v
  simp only [hammingBall, hammingSphere, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_disjiUnion, Finset.mem_range]
  constructor
  · intro hv
    exact ⟨hammingDist u v, by omega, rfl⟩
  · rintro ⟨k, hk, hkv⟩
    omega

/-! ### Support fibers and sphere cardinality -/

/-- The support of `v` relative to `u`: positions where they differ. -/
private def support (u v : Word n α) : Finset (Fin n) :=
  Finset.univ.filter (fun i => u i ≠ v i)

omit [Fintype α] in
private lemma support_dist (u v : Word n α) : hammingDist u v = (support u v).card := rfl

/-- The fiber over a given support set `S`: words differing from `u` exactly on `S`. -/
private def supportFiber (u : Word n α) (S : Finset (Fin n)) : Finset (Word n α) :=
  Finset.univ.filter (fun v => support u v = S)

private lemma supportFiber_disjoint (u : Word n α) (S T : Finset (Fin n)) (hST : S ≠ T) :
    Disjoint (supportFiber u S) (supportFiber u T) := by
  simp only [supportFiber, support, ne_eq, Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ,
    true_and]
  intro X hXS hXT; simp_all

private lemma hammingSphere_eq_biUnion (u : Word n α) (r : ℕ) :
    hammingSphere u r = (Finset.powersetCard r Finset.univ).biUnion (supportFiber u) := by
  ext v
  constructor <;> simp [hammingSphere, hammingDist, supportFiber, support]

/-- The set of alternative symbols at position `i`. -/
private def choices (u : Word n α) (i : Fin n) : Finset α :=
  Finset.univ.filter (fun a => a ≠ u i)

private lemma choices_card (u : Word n α) (i : Fin n) :
    (choices u i).card = Fintype.card α - 1 := by
  simp [choices]
  have h : Finset.univ.filter (fun a => a ≠ u i) = Finset.univ.erase (u i) := by ext a; simp
  simp_all

private lemma choices_partition_supportFiber (u : Word n α) (S : Finset (Fin n)) (i : Fin n) :
    supportFiber u (insert i S) =
      (choices u i).biUnion (fun a => (supportFiber u (insert i S)).filter (fun v => v i = a)) := by
  ext w
  simp only [supportFiber, support, ne_eq, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_biUnion, exists_eq_right_right', iff_and_self]
  intro hw
  unfold choices
  simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and] at *
  intro h
  have hi : i ∈ insert i S := Finset.mem_insert_self i S
  rw [← hw] at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  exact hi (id (Eq.symm h))

private lemma piece_card (u : Word n α) (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    ∀ a ∈ choices u i,
      ((supportFiber u (insert i S)).filter (fun v => v i = a)).card =
        (supportFiber u S).card := by
  intro a ha
  apply Finset.card_bij (fun v _ => Function.update v i (u i))
  · intro v hv
    simp only [supportFiber, support, ne_eq, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    ext j
    simp only [Function.update, eq_rec_constant, dite_eq_ite, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro hite
      by_cases h : j = i
      · simp_all
      · simp_all only [↓reduceIte]
        obtain ⟨hv1, hv2⟩ := hv
        have hj' : j ∈ insert i S := by
          rw [← hv1]; exact (Finset.mem_filter_univ j).mpr hite
        exact Finset.mem_of_mem_insert_of_ne hj' h
    · intro hj
      obtain ⟨hv1, hv2⟩ := hv
      by_cases h : j = i
      · simp [choices] at ha; simp only [h, ↓reduceIte, not_true_eq_false]; exact hi (h ▸ hj)
      · simp only [h, ↓reduceIte]
        intro huv
        have hjS : j ∈ insert i S := Finset.mem_insert_of_mem hj
        rw [← hv1] at hjS; simp at hjS; contradiction
  · intro a1 ha1 a2 ha2 hup
    simp_all only [Finset.mem_filter]
    obtain ⟨ha1, ha1'⟩ := ha1
    obtain ⟨ha2, ha2'⟩ := ha2
    simp [supportFiber, support] at ha1
    simp [supportFiber, support] at ha2
    ext j
    by_cases hij : j = i
    · rw [hij, ha1', ha2']
    · have := congr_fun hup j
      simp only [Function.update, hij, ↓reduceDIte] at this
      exact this
  · intro b hb
    simp_all only [Finset.mem_filter, exists_prop]
    refine ⟨Function.update b i a, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · simp only [supportFiber, support, ne_eq, Finset.mem_filter, Finset.mem_univ, Function.update,
      eq_rec_constant, dite_eq_ite, true_and]
      ext j
      constructor
      · intro hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        by_cases hij : j = i
        · rw [hij]; exact Finset.mem_insert_self i S
        · simp only [hij, ↓reduceIte] at hj
          simp only [supportFiber, support, ne_eq, Finset.mem_filter, Finset.mem_univ,
            true_and] at hb
          have hj' : j ∈ S := by rw [← hb]; exact (Finset.mem_filter_univ j).mpr hj
          exact Finset.mem_insert_of_mem hj'
      · intro hjins
        simp_all only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
        cases hjins with
        | inl hl =>
          simp only [hl, ↓reduceIte]; simp only [choices, ne_eq, Finset.mem_filter,
            Finset.mem_univ, true_and] at ha; exact fun a_1 => ha (id (Eq.symm a_1))
        | inr hr =>
          by_cases hij : i = j
          · simp [hij]; simp_all
          · have hij' : ¬ j = i := fun a => hij (id (Eq.symm a))
            simp [hij']
            simp [supportFiber, support] at hb
            aesop
    · aesop
    · simp_all only [Function.update_idem, Function.update_eq_self_iff]
      simp only [supportFiber, support, ne_eq, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      by_contra h
      have hi' : i ∈ S := by rw [← hb]; exact (Finset.mem_filter_univ i).mpr h
      contradiction

private lemma card_supportFiber (u : Word n α) (S : Finset (Fin n)) :
    (supportFiber u S).card = (Fintype.card α - 1) ^ S.card := by
  induction S using Finset.induction with
  | empty =>
    simp only [supportFiber, support, ne_eq, Finset.filter_eq_empty_iff, Finset.mem_univ,
      Decidable.not_not, forall_const, Finset.card_empty, pow_zero]
    convert Finset.card_singleton u
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; funext i; exact (@h i).symm
    · intro h i; exact congrFun (id (Eq.symm h)) i
  | insert i S hi ih =>
    rw [choices_partition_supportFiber]
    rw [Finset.card_biUnion]
    · have pc := piece_card u S i hi
      rw [Finset.sum_congr rfl pc, Finset.sum_const, ih, Finset.card_insert_of_notMem hi,
          choices_card]
      rw [smul_eq_mul, pow_succ]; ring
    · intro a _ b _ hab
      exact Finset.disjoint_filter.mpr (fun _ _ ha hb => hab (ha ▸ hb))

lemma hammingSphere_card (u : Word n α) (k : ℕ) :
    (hammingSphere u k).card = Nat.choose n k * (Fintype.card α - 1) ^ k := by
  rw [hammingSphere_eq_biUnion,
      Finset.card_biUnion (fun S _ T _ hST => supportFiber_disjoint u S T hST)]
  rw [Finset.sum_const_nat (fun S hS => by
    rw [card_supportFiber, (Finset.mem_powersetCard.mp hS).2])]
  simp [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

lemma hammingBall_card (u : Word n α) (r : ℕ) :
    (hammingBall u r).card = ballVol n r (Fintype.card α) := by
  induction r with
  | zero =>
    simp only [hammingBall, nonpos_iff_eq_zero, hammingDist_eq_zero, ballVol, zero_add,
      Finset.range_one, Finset.sum_singleton, Nat.choose_zero_right, pow_zero, mul_one]
    exact (Fintype.existsUnique_iff_card_one (Eq u)).mp existsUnique_eq'
  | succ k ih =>
    have hdisj : Disjoint (hammingBall u k) (hammingSphere u (k + 1)) := by
      simp only [Finset.disjoint_left, hammingBall, hammingSphere]
      intro x h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rw [h2] at h1
      linarith
    have hbs : hammingBall u (k + 1) = hammingBall u k ∪ hammingSphere u (k + 1) := by
      ext v
      simp only [Finset.mem_union, hammingBall, hammingSphere, Finset.mem_filter,
                 Finset.mem_univ, true_and]
      omega
    rw [hbs, Finset.card_union_of_disjoint hdisj, ih, hammingSphere_card]
    unfold ballVol
    conv_rhs => rw [Finset.sum_range_succ]

/-- Binary Hamming ball volume: `Σ_{i=0}^{t} C(n, i)`. -/
lemma ballVol_binary (n t : ℕ) :
    ballVol n t 2 = ∑ i ∈ Finset.range (t + 1), Nat.choose n i := by
  simp [ballVol]

end CommunicationComplexity
