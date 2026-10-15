/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.PathWalk
import Mathlib.Data.Nat.Size

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The combinatorics of inductive counting

The predicates evaluated by the inductive-counting machine
`Complexity.LogProg.ISGen.igA` [AB09, §4.3.2, proof of Theorem 4.20], over a relation `R`
on vertices `< K` and a set `Init` of start vertices.

* `Complexity.LogProg.ISCount.Mem K R Init L t` — `t` is reachable from a start vertex by at
  most `L` steps; `Complexity.LogProg.ISCount.ball` — the set `C_L` of such `t < K`.
* `Complexity.LogProg.ISCount.GS A B Kont r t c` — the acceptance condition of a guessed
  enumeration of the vertices `t, …, t + r - 1` with count `c`: each vertex is guessed in
  (and then must satisfy `A`, counting one) or out (and then must satisfy `B`), and the
  continuation `Kont` receives the final count. Its closed form is `gs_iff`.

The counting argument [AB09, §4.3.2]: when the count `cp` of the previous ball is right, the
inner enumeration accepts exactly when no member of `C_i` is or steps to `v`
(`gs_inner`), which is `v ∉ C_{i+1}` (`not_mem_succ_iff`); then the outer enumeration must
guess exactly `C_{i+1}`, and passes on its size (`gs_outer`). So each stage started with the
right count ends with the right count (`Complexity.LogProg.ISGen.gstage`).

Infrastructure for [AB09, §4.3.2]; not itself a result of the book.

## Main definitions

* `Complexity.LogProg.ISCount.Mem`, `Complexity.LogProg.ISCount.ball`,
  `Complexity.LogProg.ISCount.GS`.

## Main results

* `Complexity.LogProg.ISCount.gs_iff` — the closed form of a guessed enumeration.
* `Complexity.LogProg.ISCount.mem_succ_iff` — the balls grow by one step.
* `Complexity.LogProg.ISCount.gs_inner`, `Complexity.LogProg.ISCount.gs_outer` — the two
  enumerations with the right count. [AB09, §4.3.2]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3.2, Theorem 4.20.)
-/

namespace Complexity.LogProg

namespace ISCount

/-! ## Halving counts -/

/-- Halving a positive number shortens its binary expansion by one digit. -/
lemma size_half {m : ℕ} (h : m ≠ 0) : Nat.size m = Nat.size (m / 2) + 1 := by
  rw [← Nat.size_eq_bits_len, ← Nat.size_eq_bits_len, ← Nat.div2_val, Nat.div2_bits_eq_tail,
    List.length_tail]
  have : 0 < m.bits.length := by rw [Nat.size_eq_bits_len]; exact Nat.size_pos.mpr (by omega)
  omega

/-- The logarithmic width is at most one more than the binary length. -/
lemma logSpace_le_size_succ (n : ℕ) : logSpace n ≤ Nat.size n + 1 := by
  unfold logSpace
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
    have h2 : n < 2 ^ Nat.size n := Nat.lt_size_self n
    have : Nat.log 2 n < Nat.size n :=
      (Nat.pow_lt_pow_iff_right (show 1 < 2 by norm_num)).mp (lt_of_le_of_lt h1 h2)
    omega

/-- A number is below two to its binary length plus one. -/
lemma lt_two_pow_size_succ (n : ℕ) : n < 2 ^ (Nat.size n + 1) :=
  (Nat.lt_size_self n).trans (Nat.pow_lt_pow_right (by norm_num) (by omega))

/-! ## Balls -/

variable (K : ℕ) (R : ℕ → ℕ → Prop) (Init Acc : ℕ → Prop)

/-- **Reachability within `L` steps**: some start vertex `u < K` reaches `t` by at most `L`
steps of `R` through vertices `< K`. -/
def Mem (L t : ℕ) : Prop := ∃ u < K, Init u ∧ WalkLe R K L u t

open Classical in
/-- **The ball `C_L`**: the vertices `t < K` reachable within `L` steps. -/
noncomputable def ball (L : ℕ) : Finset ℕ := (Finset.range K).filter (Mem K R Init L)

variable {K R Init Acc}

/-- A walk from a vertex below `K` ends below `K`. -/
lemma walkLe_lt {j c t : ℕ} (hc : c < K) (h : WalkLe R K j c t) : t < K := by
  induction j generalizing c with
  | zero => cases h; exact hc
  | succ j ih =>
    rcases h with rfl | ⟨v, hv, -, hw⟩
    · exact hc
    · exact ih hv hw

/-- A reachable vertex is below `K`. -/
lemma Mem.lt {L t : ℕ} (h : Mem K R Init L t) : t < K := by
  obtain ⟨u, hu, -, hw⟩ := h
  exact walkLe_lt hu hw

/-- Membership in a ball. -/
lemma mem_ball {L t : ℕ} : t ∈ ball K R Init L ↔ Mem K R Init L t := by
  classical
  simp only [ball, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨h.lt, h⟩⟩

/-- The balls grow with the radius. -/
lemma ball_mono {L L' : ℕ} (h : L ≤ L') : ball K R Init L ⊆ ball K R Init L' := by
  intro t ht
  rw [mem_ball] at ht ⊢
  obtain ⟨u, hu, hi, hw⟩ := ht
  exact ⟨u, hu, hi, walkLe_mono h hw⟩

/-- **Walks extend at the end**: a walk of at most `j + 1` steps is a walk of at most `j`
steps, or one followed by a step into a vertex below `K`.

**Proof sketch.** `WalkLe` unfolds at the front (a walk is empty or a first step followed by
a shorter walk), so induct on `j` generalizing the start `c`. For `j = 0` both sides are the
empty walk or a single step. For `j + 1`, a walk that begins with a step `c → v` has its tail
split by the induction hypothesis at `v`; conversely, a last step appended to a walk is
pushed into the tail of that walk by the induction hypothesis (or, when the walk is empty, is
itself a one-step walk). -/
lemma walkLe_succ_iff (j c t : ℕ) : WalkLe R K (j + 1) c t ↔
    WalkLe R K j c t ∨ ∃ w, WalkLe R K j c w ∧ R w t ∧ t < K := by
  induction j generalizing c with
  | zero =>
    simp only [WalkLe]
    constructor
    · rintro (h | ⟨v, hv, he, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨c, rfl, he, hv⟩
    · rintro (h | ⟨w, rfl, he, ht⟩)
      · exact Or.inl h
      · exact Or.inr ⟨t, ht, he, rfl⟩
  | succ j ih =>
    constructor
    · rintro (h | ⟨v, hv, he, hw⟩)
      · exact Or.inl (Or.inl h)
      · rcases (ih v).mp hw with h | ⟨w, hw', hwt, ht⟩
        · exact Or.inl (Or.inr ⟨v, hv, he, h⟩)
        · exact Or.inr ⟨w, Or.inr ⟨v, hv, he, hw'⟩, hwt, ht⟩
    · rintro ((h | ⟨v, hv, he, hw⟩) | ⟨w, hw | ⟨v, hv, he, hw⟩, hwt, ht⟩)
      · exact Or.inl h
      · exact Or.inr ⟨v, hv, he, walkLe_succ hw⟩
      · subst hw
        exact Or.inr ⟨t, ht, hwt, walkLe_refl _ t⟩
      · exact Or.inr ⟨v, hv, he, (ih v).mpr (Or.inr ⟨w, hw, hwt, ht⟩)⟩

/-- **The balls grow by one step**: `C_{L+1}` is `C_L` together with the successors below `K`
of its members. -/
lemma mem_succ_iff (L t : ℕ) : Mem K R Init (L + 1) t ↔
    Mem K R Init L t ∨ ∃ w, Mem K R Init L w ∧ R w t ∧ t < K := by
  constructor
  · rintro ⟨u, hu, hi, hw⟩
    rcases (walkLe_succ_iff L u t).mp hw with h | ⟨w, hw', hwt, ht⟩
    · exact Or.inl ⟨u, hu, hi, h⟩
    · exact Or.inr ⟨w, ⟨u, hu, hi, hw'⟩, hwt, ht⟩
  · rintro (⟨u, hu, hi, hw⟩ | ⟨w, ⟨u, hu, hi, hw'⟩, hwt, ht⟩)
    · exact ⟨u, hu, hi, walkLe_succ hw⟩
    · exact ⟨u, hu, hi, (walkLe_succ_iff L u t).mpr (Or.inr ⟨w, hw', hwt, ht⟩)⟩

/-- **Non-membership in the next ball** (for `v < K`): no member of `C_L` is or steps to `v`. -/
lemma not_mem_succ_iff {L v : ℕ} (hv : v < K) : ¬ Mem K R Init (L + 1) v ↔
    ∀ u ∈ ball K R Init L, u ≠ v ∧ ¬ R u v := by
  rw [mem_succ_iff]
  constructor
  · intro h u hu
    rw [mem_ball] at hu
    refine ⟨fun e => h (Or.inl (e ▸ hu)), fun he => h (Or.inr ⟨u, hu, he, hv⟩)⟩
  · rintro h (hm | ⟨w, hw, hwv, -⟩)
    · exact (h v (mem_ball.mpr hm)).1 rfl
    · exact (h w (mem_ball.mpr hw)).2 hwv

/-- With a unique start vertex below `K`, the ball `C_0` has one element. -/
lemma card_ball_zero {u₀ : ℕ} (hu₀ : u₀ < K) (hI : ∀ u, Init u ↔ u = u₀) :
    (ball K R Init 0).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨u₀, Finset.ext fun t => ?_⟩
  rw [mem_ball, Finset.mem_singleton]
  constructor
  · rintro ⟨u, -, hi, hw⟩
    have e : u = t := hw
    rw [← e]
    exact (hI u).mp hi
  · intro h
    rw [h]
    exact ⟨u₀, hu₀, (hI u₀).mpr rfl, rfl⟩

/-! ## Guessed enumerations -/

/-- **A guessed enumeration** of the vertices `t, …, t + r - 1` with count `c`: each vertex
is guessed in (it must satisfy `A`, and the count grows) or out (it must satisfy `B`); at the
end the continuation `Kont` receives the count. -/
def GS (A B Kont : ℕ → Prop) : ℕ → ℕ → ℕ → Prop
  | 0, _, c => Kont c
  | r + 1, t, c => (A t ∧ GS A B Kont r (t + 1) (c + 1)) ∨ (B t ∧ GS A B Kont r (t + 1) c)

/-- A continuation conjunct independent of the count factors out of an enumeration. -/
lemma gs_and (A B Kont : ℕ → Prop) (Q : Prop) (r t c : ℕ) :
    GS A B (fun c => Kont c ∧ Q) r t c ↔ GS A B Kont r t c ∧ Q := by
  induction r generalizing t c with
  | zero => rfl
  | succ r ih =>
    simp only [GS, ih]
    tauto

/-- **The closed form of a guessed enumeration**: some set `T` of the enumerated vertices has
`A` on its members and `B` on the other enumerated vertices, and the continuation accepts
the count `c + |T|`.

**Proof sketch.** Induction on `r`: the first vertex `t` is in `T` (then `T` is
`insert t T'`) or not. -/
lemma gs_iff (A B Kont : ℕ → Prop) (r t c : ℕ) :
    GS A B Kont r t c ↔ ∃ T : Finset ℕ, T ⊆ Finset.Ico t (t + r) ∧ (∀ y ∈ T, A y) ∧
      (∀ y ∈ Finset.Ico t (t + r), y ∉ T → B y) ∧ Kont (c + T.card) := by
  induction r generalizing t c with
  | zero =>
    simp only [GS, Nat.add_zero, Finset.Ico_self, Finset.subset_empty]
    constructor
    · intro h; exact ⟨∅, rfl, by simp, by simp, by simpa using h⟩
    · rintro ⟨T, rfl, -, -, h⟩; simpa using h
  | succ r ih =>
    simp only [GS, ih]
    constructor
    · rintro (⟨hA, T, hT, hTA, hTB, hK⟩ | ⟨hB, T, hT, hTA, hTB, hK⟩)
      · have htT : t ∉ T := fun h => by have := Finset.mem_Ico.mp (hT h); omega
        refine ⟨insert t T, fun y hy => ?_, fun y hy => ?_, fun y hy hyT => ?_, ?_⟩
        · rcases Finset.mem_insert.mp hy with rfl | hy
          · exact Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
          · have := Finset.mem_Ico.mp (hT hy); exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
        · rcases Finset.mem_insert.mp hy with rfl | hy
          · exact hA
          · exact hTA y hy
        · have hne : y ≠ t := fun e => hyT (e ▸ Finset.mem_insert_self _ _)
          have := Finset.mem_Ico.mp hy
          exact hTB y (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
            (fun h => hyT (Finset.mem_insert_of_mem h))
        · rw [Finset.card_insert_of_notMem htT]
          rwa [show c + (T.card + 1) = c + 1 + T.card by omega]
      · refine ⟨T, fun y hy => ?_, hTA, fun y hy hyT => ?_, hK⟩
        · have := Finset.mem_Ico.mp (hT hy); exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
        · rcases Nat.eq_or_lt_of_le (Finset.mem_Ico.mp hy).1 with h | h
          · subst h; exact hB
          · exact hTB y
              (Finset.mem_Ico.mpr ⟨by omega, by have := (Finset.mem_Ico.mp hy).2; omega⟩) hyT
    · rintro ⟨T, hT, hTA, hTB, hK⟩
      by_cases htT : t ∈ T
      · refine Or.inl ⟨hTA t htT, T.erase t, fun y hy => ?_, fun y hy => hTA y
          (Finset.mem_of_mem_erase hy), fun y hy hyT => ?_, ?_⟩
        · have hne := Finset.ne_of_mem_erase hy
          have := Finset.mem_Ico.mp (hT (Finset.mem_of_mem_erase hy))
          exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
        · have := Finset.mem_Ico.mp hy
          refine hTB y (Finset.mem_Ico.mpr ⟨by omega, by omega⟩) fun h => hyT ?_
          exact Finset.mem_erase.mpr ⟨by omega, h⟩
        · have := Finset.card_erase_of_mem htT
          have hpos : 0 < T.card := Finset.card_pos.mpr ⟨t, htT⟩
          rwa [this, show c + 1 + (T.card - 1) = c + T.card by omega]
      · refine Or.inr ⟨hTB t (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩) htT, T, fun y hy => ?_,
          hTA, fun y hy hyT => ?_, hK⟩
        · have := Finset.mem_Ico.mp (hT hy)
          have hne : y ≠ t := fun e => htT (e ▸ hy)
          exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
        · have := Finset.mem_Ico.mp hy
          exact hTB y (Finset.mem_Ico.mpr ⟨by omega, by omega⟩) hyT

/-- **The inner enumeration with the right count** [AB09, §4.3.2]: guessing members of `C_L`
none of which is or steps to `v`, and finding exactly `|C_L|` of them, is possible iff every
member of `C_L` is neither `v` nor steps to `v`.

**Proof sketch.** A guessed set of members of `C_L` of size `|C_L|` is `C_L` itself. -/
lemma gs_inner (L v : ℕ) :
    GS (fun u => Mem K R Init L u ∧ u ≠ v ∧ ¬ R u v) (fun _ => True)
        (fun c => c = (ball K R Init L).card) K 0 0 ↔
      ∀ u ∈ ball K R Init L, u ≠ v ∧ ¬ R u v := by
  rw [gs_iff]
  simp only [Nat.zero_add]
  constructor
  · rintro ⟨T, -, hTA, -, hcard⟩
    have hsub : T ⊆ ball K R Init L := fun y hy => mem_ball.mpr (hTA y hy).1
    have heq : T = ball K R Init L := Finset.eq_of_subset_of_card_le hsub (by omega)
    intro u hu
    rw [← heq] at hu
    exact (hTA u hu).2
  · intro h
    refine ⟨ball K R Init L, fun y hy => ?_, fun y hy => ⟨mem_ball.mp hy, h y hy⟩,
      fun _ _ _ => trivial, rfl⟩
    exact Finset.mem_Ico.mpr ⟨Nat.zero_le _, (mem_ball.mp hy).lt⟩

/-- **The outer enumeration** [AB09, §4.3.2]: if the out-guesses certify exactly
non-membership in `C_L` (below `K`), then the enumeration guessing members of `C_L` that are
not accepting accepts iff no member of `C_L` is accepting and the continuation accepts
`|C_L|`.

**Proof sketch.** The guessed set must be `C_L`: its members are in `C_L`, and the other
vertices below `K` are not. -/
lemma gs_outer (L : ℕ) (B Kont : ℕ → Prop) (hB : ∀ t < K, B t ↔ ¬ Mem K R Init L t) :
    GS (fun t => Mem K R Init L t ∧ ¬ Acc t) B Kont K 0 0 ↔
      (∀ t ∈ ball K R Init L, ¬ Acc t) ∧ Kont (ball K R Init L).card := by
  rw [gs_iff]
  simp only [Nat.zero_add]
  constructor
  · rintro ⟨T, hT, hTA, hTB, hK⟩
    have heq : T = ball K R Init L := by
      ext y
      rw [mem_ball]
      constructor
      · intro hy; exact (hTA y hy).1
      · intro hy
        by_contra hyT
        have hyK := Finset.mem_Ico.mpr ⟨Nat.zero_le y, hy.lt⟩
        exact (hB y hy.lt).mp (hTB y hyK hyT) hy
    subst heq
    exact ⟨fun t ht => (hTA t ht).2, hK⟩
  · rintro ⟨hA, hK⟩
    refine ⟨ball K R Init L, fun y hy => ?_, fun y hy => ⟨mem_ball.mp hy, hA y hy⟩,
      fun y hy hyT => ?_, hK⟩
    · exact Finset.mem_Ico.mpr ⟨Nat.zero_le _, (mem_ball.mp hy).lt⟩
    · exact (hB y (Finset.mem_Ico.mp hy).2).mpr fun h => hyT (mem_ball.mpr h)

end ISCount

end Complexity.LogProg
