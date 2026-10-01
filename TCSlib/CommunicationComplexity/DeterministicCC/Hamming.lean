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

Counting words of a fixed length over a finite alphabet by their Hamming distance from a
centre word: the Hamming sphere of radius `k` has `C(n, k) · (q − 1)^k` elements and the
Hamming ball of radius `r` has `Vol_q(r, n) = Σ_{i ≤ r} C(n, i) (q − 1)^i` elements.

This is general coding-theory material ([GRS25, §1.3, §1.6, §3.3]) rather than
communication complexity proper; it lives here because its only consumer in the library is
the Index lower bound (`DeterministicCC/FuncIndexing.lean`), which counts inputs close to a
given one. Everything is stated for `Word n α = Fin n → α` with `hammingDist` from Mathlib.

## Main definitions

- `CommunicationComplexity.Word`: words of length `n` over the alphabet `α`
- `CommunicationComplexity.hammingBall`: the words within Hamming distance `r` of a centre
- `CommunicationComplexity.hammingSphere`: the words at Hamming distance exactly `r` from a
  centre
- `CommunicationComplexity.ballVol`: the volume `Vol_q(r, n)` of a `q`-ary Hamming ball

## Main results

- `CommunicationComplexity.hammingBall_eq_hammingSpheres`: a ball of radius `r` is the
  disjoint union of the spheres of radius `0, …, r`
- `CommunicationComplexity.hammingSphere_card`: a sphere of radius `k` has
  `C(n, k) · (q − 1)^k` elements
- `CommunicationComplexity.hammingBall_card`: a ball of radius `r` has `ballVol n r q`
  elements
- `CommunicationComplexity.ballVol_binary`: over a binary alphabet the volume is
  `Σ_{i ≤ r} C(n, i)`

## References

* [GRS25] V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*,
  draft textbook, 2025/26.

Original formalization by Lucy Horowitz, Timothe Kasriel, and Mihir Singhal.
-/

namespace CommunicationComplexity

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

/-- A codeword of length `n` over alphabet `α`. -/
abbrev Word (n : ℕ) (α : Type*) := Fin n → α

/-- The Hamming ball of radius `r` centred at `u`: the finite set of words `v` with
`hammingDist u v ≤ r`. [GRS25, Def 1.6.1]. -/
def hammingBall (u : Word n α) (r : ℕ) : Finset (Word n α) :=
  Finset.univ.filter (fun v => hammingDist u v ≤ r)

/-- The Hamming sphere of radius `r` centred at `u`: the finite set of words `v` with
`hammingDist u v = r`. Not defined in [GRS25]; it is the outermost layer
`B(u, r) \ B(u, r − 1)` of the Hamming ball of [GRS25, Def 1.6.1]. -/
def hammingSphere (u : Word n α) (r : ℕ) : Finset (Word n α) :=
  Finset.univ.filter (fun v => hammingDist u v = r)

/-- The volume of a `q`-ary Hamming ball of radius `t` in dimension `n`:
`Vol_q(t, n) = Σ_{i=0}^{t} C(n, i) · (q − 1)^i`. [GRS25, Def 3.3.2]. Deviation: defined for
all naturals `n`, `t`, `q` (with truncated subtraction `q − 1`), whereas GRS25 assume
`q ≥ 2` and `1 ≤ t ≤ n`; `hammingBall_card` shows it counts the ball in all cases. -/
def ballVol (n t q : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (t + 1), Nat.choose n i * (q - 1) ^ i

/-! ### Sphere and ball decomposition -/

/-- Two Hamming spheres about the same centre with different radii are disjoint. -/
lemma hammingSpheres_disjoint (u : Word n α) (r t : ℕ) (hrt : r ≠ t) :
    Disjoint (hammingSphere u r) (hammingSphere u t) := by
  simp only [hammingSphere, Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
  intro x h1 h2; omega

/-- The Hamming spheres about `u` of radii `0, …, r − 1` are pairwise disjoint. -/
lemma hammingSpheres_pairwise_disjoint (u : Word n α) (r : ℕ) :
    Set.PairwiseDisjoint (Finset.range r) (fun t => hammingSphere u t) :=
  fun _ _ _ _ hst => hammingSpheres_disjoint u _ _ hst

/-- The Hamming ball of radius `r` about `u` is the disjoint union of the Hamming spheres
about `u` of radii `0, …, r`. -/
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

/-- The support of `v` relative to `u`: the set of positions where `u` and `v` differ, so
that its size is the Hamming distance [GRS25, Def 1.3.3]. -/
private def support (u v : Word n α) : Finset (Fin n) :=
  Finset.univ.filter (fun i => u i ≠ v i)

omit [Fintype α] in
/-- The Hamming distance between `u` and `v` is the number of positions where they differ,
i.e. the size of `support u v`. [GRS25, Def 1.3.3]. -/
private lemma support_dist (u v : Word n α) : hammingDist u v = (support u v).card := rfl

/-- The fiber over a given support set `S`: words differing from `u` exactly on `S`. -/
private def supportFiber (u : Word n α) (S : Finset (Fin n)) : Finset (Word n α) :=
  Finset.univ.filter (fun v => support u v = S)

/-- Fibers over different support sets are disjoint. -/
private lemma supportFiber_disjoint (u : Word n α) (S T : Finset (Fin n)) (hST : S ≠ T) :
    Disjoint (supportFiber u S) (supportFiber u T) := by
  simp only [supportFiber, support, ne_eq, Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ,
    true_and]
  intro X hXS hXT; simp_all

/-- The Hamming sphere of radius `r` about `u` is the union, over all `r`-element sets `S`
of positions, of the fibers of words differing from `u` exactly on `S`. -/
private lemma hammingSphere_eq_biUnion (u : Word n α) (r : ℕ) :
    hammingSphere u r = (Finset.powersetCard r Finset.univ).biUnion (supportFiber u) := by
  ext v
  constructor <;> simp [hammingSphere, hammingDist, supportFiber, support]

/-- The set of alternative symbols at position `i`: every symbol other than `u i`. -/
private def choices (u : Word n α) (i : Fin n) : Finset α :=
  Finset.univ.filter (fun a => a ≠ u i)

/-- There are `q − 1` alternative symbols at any position, where `q = |α|`. -/
private lemma choices_card (u : Word n α) (i : Fin n) :
    (choices u i).card = Fintype.card α - 1 := by
  have h : choices u i = Finset.univ.erase (u i) := by
    ext a
    simp [choices]
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

/-- The fiber over `insert i S` is the union, over the alternative symbols `a ≠ u i`, of the
words in that fiber whose `i`-th symbol is `a`. -/
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

/-- For `i ∉ S` and any alternative symbol `a ≠ u i`, the words differing from `u` exactly
on `insert i S` and carrying the symbol `a` at position `i` are in bijection with the words
differing from `u` exactly on `S`; in particular the two sets have the same size.

**Proof sketch.** The bijection resets position `i` to the centre's symbol,
`v ↦ update v i (u i)`, and is verified through the three obligations of `Finset.card_bij`.

1. Well-defined: if `v` differs from `u` exactly on `insert i S`, then after resetting
   position `i` it differs from `u` exactly on `S` (position `i` now agrees; every other
   position is unchanged and, being in `insert i S` but not `i`, lies in `S`).
2. Injective: two such words agree at position `i` (both carry `a`) and, having the same
   reset, agree at every other position.
3. Surjective: a word `w` differing from `u` exactly on `S` is the reset of `update w i a`,
   which differs from `u` exactly on `insert i S` (at `i` because `a ≠ u i`; elsewhere as
   `w` does, using `i ∉ S`) and carries `a` at position `i`. -/
private lemma piece_card (u : Word n α) (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    ∀ a ∈ choices u i,
      ((supportFiber u (insert i S)).filter (fun v => v i = a)).card =
        (supportFiber u S).card := by
  intro a ha
  apply Finset.card_bij (fun v _ => Function.update v i (u i))
  · -- Step 1: resetting position `i` lands in the fiber over `S`
    intro v hv
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
  · -- Step 2: the reset map is injective on words carrying `a` at position `i`
    intro a1 ha1 a2 ha2 hup
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
  · -- Step 3: every word in the fiber over `S` is the reset of `update b i a`
    intro b hb
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

/-- The number of words differing from `u` exactly on a set `S` of positions is
`(q − 1)^|S|`, where `q = |α|`.

**Proof sketch.** Induction on `S`. For `S = ∅` the fiber is the singleton `{u}`. For
`insert i S` with `i ∉ S`, partition the fiber by the symbol at position `i`
(`choices_partition_supportFiber`); each of the `q − 1` pieces (`choices_card`) has the
size of the fiber over `S` (`piece_card`), which is `(q − 1)^|S|` by induction. -/
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

/-- The Hamming sphere of radius `k` about a word of length `n` over an alphabet of size
`q` has exactly `C(n, k) · (q − 1)^k` elements. [GRS25, Def 3.3.2] (the `k`-th summand of
the ball volume). The proof splits the sphere into the fibers over the `C(n, k)` possible
`k`-element supports (`hammingSphere_eq_biUnion`), each of size `(q − 1)^k`
(`card_supportFiber`). -/
lemma hammingSphere_card (u : Word n α) (k : ℕ) :
    (hammingSphere u k).card = Nat.choose n k * (Fintype.card α - 1) ^ k := by
  rw [hammingSphere_eq_biUnion,
      Finset.card_biUnion (fun S _ T _ hST => supportFiber_disjoint u S T hST)]
  rw [Finset.sum_const_nat (fun S hS => by
    rw [card_supportFiber, (Finset.mem_powersetCard.mp hS).2])]
  simp [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- The Hamming ball of radius `r` about a word of length `n` over an alphabet of size `q`
has exactly `ballVol n r q = Σ_{i ≤ r} C(n, i) (q − 1)^i` elements. [GRS25, Def 3.3.2].
Deviation: no restriction `q ≥ 2`, `1 ≤ r ≤ n` is needed (see `ballVol`). -/
lemma hammingBall_card (u : Word n α) (r : ℕ) :
    (hammingBall u r).card = ballVol n r (Fintype.card α) := by
  -- Step 1: the ball is the disjoint union of the spheres of radius `0, …, r`
  rw [hammingBall_eq_hammingSpheres, Finset.card_disjiUnion]
  -- Step 2: sum the sphere cardinalities `C(n, k) (q - 1)^k`
  unfold ballVol
  exact Finset.sum_congr rfl fun k _ => hammingSphere_card u k

/-- Over a binary alphabet the Hamming ball volume is `Σ_{i=0}^{t} C(n, i)`.
[GRS25, Def 3.3.2] with `q = 2`. -/
lemma ballVol_binary (n t : ℕ) :
    ballVol n t 2 = ∑ i ∈ Finset.range (t + 1), Nat.choose n i := by
  simp [ballVol]

end CommunicationComplexity
