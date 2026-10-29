/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import TCSlib.Complexity.Randomized.Classes
import TCSlib.Complexity.SpaceComplexity.Machines.Bin

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Random strings: conditioning, union bounds, and numbers from random bits

Shared infrastructure for randomized algorithms stated with `Randomized.randProb`:
constant events, conditioning on the first coin or on a prefix of the coins, the union bound,
reading numbers off blocks of fair coins, and the uniformity and independence of those
numbers. No textbook counterpart; used throughout the chapter-7 files ([AB09, Ch. 7]).

## Main definitions

* `Randomized.blockVal` — the number in the `i`-th length-`b` block of a bit string
  (little-endian, via `Complexity.LogProg.bitsVal`).
* `Randomized.bitsEquiv`, `Randomized.blocksEquiv` — bits as numbers, as bijections.

## Main results

* `Randomized.randProb_succ`, `Randomized.randProb_append` — conditioning on the first coin,
  on the first `b` coins; `Randomized.randProb_drop`, `Randomized.randProb_drop_take` —
  events of a slice of the coins.
* `Randomized.randProb_append_ge`, `Randomized.randProb_append_le` — conditioning on a
  prefix (lower and upper bounds).
* `Randomized.exists_ofFn_of_randProb_pos`, `Randomized.exists_forall_not_of_randProb_le` —
  positive probability and the union bound.
* `Randomized.blockCount_add_not` — passing and failing blocks are all the blocks.
* `Randomized.randProb_bitsVal` — `L` coins give a uniform number in `[0, 2^L)`.
* `Randomized.randProb_blocks`, `Randomized.randProb_blocks_piFinset` — `n` blocks give `n`
  independent uniform numbers.
* `Randomized.randProb_forall_blocks` — a property of every block has probability the
  power of the one-block probability.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Finset
open Complexity.LogProg (bitsVal bitsVal_lt_two_pow)

/-! ### Elementary events and conditioning on a prefix -/

/-- A constant event has probability `1` or `0`. -/
theorem randProb_const (n : ℕ) (p : Prop) [Decidable p] :
    randProb n (fun _ => p) = if p then 1 else 0 := by
  by_cases hp : p
  · rw [if_pos hp, ← randProb_true (m := n)]
    exact randProb_congr fun _ => by simp [hp]
  · rw [if_neg hp, ← randProb_false (m := n)]
    exact randProb_congr fun _ => by simp [hp]

/-- An event of positive probability holds of some random string. -/
theorem exists_ofFn_of_randProb_pos {m : ℕ} {A : List Bool → Prop} [DecidablePred A]
    (h : 0 < randProb m A) : ∃ r : Fin m → Bool, A (List.ofFn r) := by
  by_contra hne
  push_neg at hne
  rw [randProb_congr (B := fun _ => False) fun r => by simp only [hne r],
    randProb_false] at h
  exact lt_irrefl _ h

/-- The fair first bit: `1/2` of the words of length one are `[c]`. -/
theorem randProb_one_eq (c : Bool) : randProb 1 (fun r => r = [c]) = 1 / 2 := by
  unfold randProb
  have h : (Finset.univ.filter fun r : Fin 1 → Bool => List.ofFn r = [c]).card = 1 := by
    cases c <;> decide
  rw [h]; norm_num

/-- **Conditioning on the first bit**: the probability over `n + 1` bits is the average of
the probabilities over `n` bits after a first bit `1` and after a first bit `0`.

**Proof sketch.** Split the event by the first coin (`randProb_or_disjoint`); each half is
the product of `Pr[first coin = c] = 1/2` (`randProb_one_eq`) and the probability over the
remaining `n` coins (`randProb_split`). -/
theorem randProb_succ (n : ℕ) (P : List Bool → Prop) [DecidablePred P] :
    randProb (n + 1) P =
      (randProb n (fun u => P (true :: u)) + randProb n (fun u => P (false :: u))) / 2 := by
  rw [show n + 1 = 1 + n from Nat.add_comm n 1]
  have e : ∀ c : Bool, randProb (1 + n) (fun w => w.take 1 = [c] ∧ P (c :: w.drop 1)) =
      1 / 2 * randProb n (fun u => P (c :: u)) := fun c => by
    rw [← randProb_one_eq c]
    exact randProb_split 1 n (fun r => r = [c]) (fun u => P (c :: u))
  calc randProb (1 + n) P
      = randProb (1 + n) (fun w => (w.take 1 = [true] ∧ P (true :: w.drop 1)) ∨
          (w.take 1 = [false] ∧ P (false :: w.drop 1))) := randProb_congr fun r => by
        obtain ⟨a, u, hw⟩ : ∃ a u, List.ofFn r = a :: u := by
          cases h : List.ofFn r with
          | nil => have := congrArg List.length h; simp at this
          | cons a u => exact ⟨a, u, rfl⟩
        rw [hw]; cases a <;> simp
    _ = randProb (1 + n) (fun w => w.take 1 = [true] ∧ P (true :: w.drop 1)) +
        randProb (1 + n) (fun w => w.take 1 = [false] ∧ P (false :: w.drop 1)) :=
        randProb_or_disjoint _ _ fun r h => by
          have := h.1.1.symm.trans h.2.1; simp at this
    _ = _ := by rw [e, e]; ring

/-- An event of the bits after the first `S` has, over `S + n` bits, its probability over
`n` bits. -/
theorem randProb_drop (S n : ℕ) (P : List Bool → Prop) [DecidablePred P] :
    randProb (S + n) (fun w => P (w.drop S)) = randProb n P := by
  calc randProb (S + n) (fun w => P (w.drop S))
      = randProb (S + n) (fun w => (fun _ => True) (w.take S) ∧ P (w.drop S)) :=
        randProb_congr fun r => by simp
    _ = randProb S (fun _ => True) * randProb n P := randProb_split S n (fun _ => True) P
    _ = randProb n P := by rw [randProb_true, one_mul]

/-- A condition on the slice `w[s, s+T)` of a uniform `m`-bit word has the probability of the
condition on a uniform `T`-bit word. -/
theorem randProb_drop_take {s T m : ℕ} (h : s + T ≤ m) (B : List Bool → Prop)
    [DecidablePred B] :
    randProb m (fun w => B ((w.drop s).take T)) = randProb T B := by
  have h1 : randProb m (fun w => B ((w.drop s).take T)) =
      randProb (s + T) (fun w => B ((w.drop s).take T)) := by
    rw [← randProb_take h (fun w => B ((w.drop s).take T))]
    refine randProb_congr fun r => ?_
    rw [List.drop_take, List.take_take, Nat.min_def, if_pos (by omega)]
  have h2 : randProb (s + T) (fun w => True ∧ B ((w.drop s).take T)) =
      randProb s (fun _ => True) * randProb T (fun v => B (v.take T)) := by
    convert randProb_split s T (fun _ => True) (fun v => B (v.take T)) using 1
  rw [h1, randProb_congr (B := fun w => True ∧ B ((w.drop s).take T)) fun r => by simp, h2,
    randProb_true, one_mul]
  refine randProb_congr fun r => ?_
  rw [List.take_of_length_le (by simp)]

/-- Conditioning on the first `b` coins: `Pr_{b+m}[A] = 𝔼_u Pr_m[A(u ++ ·)]`. -/
theorem randProb_append (b m : ℕ) (A : List Bool → Prop) [DecidablePred A] :
    randProb (b + m) A =
      (∑ u : Fin b → Bool, randProb m fun l => A (List.ofFn u ++ l)) / 2 ^ b := by
  unfold randProb
  rw [Finset.natCast_card_filter, ← (Fin.appendEquiv b m).sum_comp, Fintype.sum_prod_type,
    ← Finset.sum_div, div_div, pow_add, mul_comm ((2 : ℚ) ^ b)]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.natCast_card_filter]
  exact Finset.sum_congr rfl fun v _ =>
    if_congr (by
      show A (List.ofFn (Fin.append u v)) ↔ _
      rw [List.ofFn_fin_append]) rfl rfl

/-! ### Union bounds and block votes -/

/-- **Union bound**: if each of the `2^n` events `Bad v` has probability at most `δ` and
`2^n · δ < 1`, one random string avoids every one of them.

**Proof sketch.** Otherwise the `2^n` bad sets cover all `2^m` strings, so
`2^m ≤ 2^n · δ · 2^m < 2^m` (as in `adleman`). -/
theorem exists_forall_not_of_randProb_le {m n : ℕ} (Bad : (Fin n → Bool) → List Bool → Prop)
    [∀ v, DecidablePred (Bad v)] {δ : ℚ} (h : ∀ v, randProb m (Bad v) ≤ δ)
    (hδ : 2 ^ n * δ < 1) : ∃ r : Fin m → Bool, ∀ v, ¬ Bad v (List.ofFn r) := by
  by_contra hne
  push_neg at hne
  have hcover : (Finset.univ : Finset (Fin m → Bool)) ⊆ Finset.univ.biUnion
      (fun v => Finset.univ.filter fun r : Fin m → Bool => Bad v (List.ofFn r)) := by
    intro r _
    obtain ⟨v, hv⟩ := hne r
    exact Finset.mem_biUnion.mpr
      ⟨v, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
  have h1 := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  rw [card_univ_bitstrings] at h1
  have h2 : ((2 : ℚ)) ^ m ≤ ∑ v : Fin n → Bool,
      ((Finset.univ.filter fun r : Fin m → Bool => Bad v (List.ofFn r)).card : ℚ) := by
    exact_mod_cast h1
  have h3 : ∀ v, ((Finset.univ.filter fun r : Fin m → Bool => Bad v (List.ofFn r)).card : ℚ) ≤
      δ * 2 ^ m := fun v => by
    have := h v
    unfold randProb at this
    rwa [div_le_iff₀ (by positivity)] at this
  have h4 := h2.trans (Finset.sum_le_sum fun v _ => h3 v)
  rw [Finset.sum_const, card_univ_bitstrings, nsmul_eq_mul] at h4
  push_cast at h4
  have h5 := mul_lt_mul_of_pos_right hδ (pow_pos (two_pos : (0 : ℚ) < 2) m)
  nlinarith

/-- The blocks passing a test and the blocks failing it are all the blocks. -/
theorem blockCount_add_not (q K : ℕ) (B : List Bool → Bool) (l : List Bool) :
    blockCount q K B l + blockCount q K (fun l => !B l) l = K := by
  induction K generalizing l with
  | zero => simp [blockCount]
  | succ K ih =>
    rw [blockCount_succ, blockCount_succ]
    have := ih (l.drop q)
    cases B (l.take q) <;> simp <;> omega

/-! ### Numbers from random bits -/

/-- The number written in the `i`-th length-`b` block of `r`. -/
def blockVal (b : ℕ) (r : List Bool) (i : ℕ) : ℕ :=
  bitsVal ((r.drop (i * b)).take b)

/-- Every block value is below `2^b`. -/
theorem blockVal_lt (b : ℕ) (r : List Bool) (i : ℕ) : blockVal b r i < 2 ^ b :=
  (bitsVal_lt_two_pow _).trans_le (Nat.pow_le_pow_right (by norm_num) (List.length_take_le _ _))

/-- `bitsVal` of a bit tuple is `∑ⱼ fⱼ·2^j`. -/
theorem bitsVal_ofFn {L : ℕ} (f : Fin L → Bool) :
    bitsVal (List.ofFn f) = ∑ j : Fin L, (f j).toNat * 2 ^ (j : ℕ) := by
  induction L with
  | zero => simp [bitsVal]
  | succ L ih =>
    rw [List.ofFn_succ, bitsVal, ih, Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

/-- `L` random bits are a uniformly random number in `[0, 2^L)`. -/
def bitsEquiv (L : ℕ) : (Fin L → Bool) ≃ Fin (2 ^ L) :=
  (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- `bitsEquiv` is `bitsVal`. -/
theorem bitsEquiv_apply {L : ℕ} (f : Fin L → Bool) :
    (bitsEquiv L f : ℕ) = bitsVal (List.ofFn f) := by
  rw [bitsVal_ofFn, bitsEquiv, Equiv.trans_apply, finFunctionFinEquiv_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hb : ∀ c : Bool, ((finTwoEquiv.symm c : Fin 2) : ℕ) = c.toNat := by decide
  simp [Equiv.arrowCongr_apply, hb]

/-- The number read off `L` uniform bits is uniform on `[0, 2^L)`.

**Proof sketch.** `r ↦ bitsVal r` is the bijection `bitsEquiv` from `{0,1}^L` onto
`[0, 2^L)`, so it maps the strings satisfying `P ∘ bitsVal` bijectively onto
`{v < 2^L | P v}`. -/
theorem randProb_bitsVal (L : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    randProb L (fun r => P (bitsVal r)) = #{v ∈ range (2 ^ L) | P v} / 2 ^ L := by
  unfold randProb
  congr 2
  refine Finset.card_bij (fun r _ => bitsVal (List.ofFn r)) ?_ ?_ ?_
  · intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr
    simpa [hr] using bitsVal_lt_two_pow (List.ofFn r)
  · intro r _ r' _ h
    simp only at h
    rw [← bitsEquiv_apply, ← bitsEquiv_apply] at h
    exact (bitsEquiv L).injective (Fin.ext h)
  · intro v hv
    simp only [mem_filter, mem_range] at hv
    have hr : bitsVal (List.ofFn ((bitsEquiv L).symm ⟨v, hv.1⟩)) = v := by
      rw [← bitsEquiv_apply, Equiv.apply_symm_apply]
    refine ⟨(bitsEquiv L).symm ⟨v, hv.1⟩, ?_, hr⟩
    simp only [mem_filter, mem_univ, true_and]
    rw [hr]
    exact hv.2

/-- `n·b` random bits, cut into `n` blocks of `b`, as `n` numbers in `[0, 2^b)`. -/
def blocksEquiv (n b : ℕ) : (Fin (n * b) → Bool) ≃ (Fin n → Fin (2 ^ b)) :=
  ((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.curry _ _ _)).trans (Equiv.arrowCongr (Equiv.refl _) (bitsEquiv b))

/-- The `i`-th coordinate of `blocksEquiv` is the `i`-th block value. -/
theorem blocksEquiv_apply {n b : ℕ} (r : Fin (n * b) → Bool) (i : Fin n) :
    (blocksEquiv n b r i : ℕ) = blockVal b (List.ofFn r) i := by
  have hlist : ((List.ofFn r).drop (i * b)).take b =
      List.ofFn (fun j : Fin b => r (finProdFinEquiv (i, j))) := by
    have hib : (i : ℕ) * b + b ≤ n * b := by
      have := i.isLt
      nlinarith
    apply List.ext_getElem
    · simp
      omega
    · intro j h1 h2
      simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
      congr 1
      ext
      simp [finProdFinEquiv]
      ring
  rw [blockVal, hlist, ← bitsEquiv_apply]
  rfl

/-- The `n` numbers read off `n` blocks of `b` uniform bits are independent and uniform
on `[0, 2^b)`. -/
theorem randProb_blocks (n b : ℕ) (P : (Fin n → ℕ) → Prop) [DecidablePred P] :
    randProb (n * b) (fun r => P (fun i => blockVal b r i)) =
      #{f : Fin n → Fin (2 ^ b) | P (fun i => f i)} / (2 ^ b) ^ n := by
  unfold randProb
  rw [← pow_mul, mul_comm b n]
  congr 2
  refine Finset.card_equiv (blocksEquiv n b) fun r => ?_
  simp only [mem_filter, mem_univ, true_and]
  exact Iff.of_eq (congrArg P (funext fun i => (blocksEquiv_apply r i).symm))

/-- `randProb_blocks` with the block values ranging over `[0, 2^b)^n` as a `Fintype.piFinset`. -/
theorem randProb_blocks_piFinset (n b : ℕ) (P : (Fin n → ℕ) → Prop) [DecidablePred P] :
    randProb (n * b) (fun r => P fun i => blockVal b r i) =
      (#{f ∈ Fintype.piFinset fun _ : Fin n => range (2 ^ b) | P f} : ℚ) / 2 ^ (n * b) := by
  rw [randProb_blocks, ← pow_mul, mul_comm b n]
  congr 2
  refine Finset.card_bij (fun a _ => fun i => (a i : ℕ)) ?_ ?_ ?_
  · intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    simp [ha]
  · intro a _ a' _ h
    funext i
    exact Fin.ext (congrFun h i)
  · intro f hf
    simp only [mem_filter, Fintype.mem_piFinset, mem_range] at hf
    exact ⟨fun i => ⟨f i, hf.1 i⟩, by simpa using hf.2, rfl⟩

/-- The probability that all of `t` blocks of `L` uniform bits satisfy `Q` is the `t`-th
power of the one-block probability. -/
theorem randProb_forall_blocks (t L : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    randProb (t * L) (fun s => ∀ j : Fin t, Q (blockVal L s j)) =
      randProb L (fun r => Q (bitsVal r)) ^ t := by
  induction t with
  | zero =>
    rw [pow_zero, ← randProb_true (m := 0 * L)]
    exact randProb_congr fun r => by simp
  | succ t ih =>
    rw [show (t + 1) * L = L + t * L by ring, pow_succ', ← ih, ← randProb_split]
    refine randProb_congr fun r => ?_
    rw [Fin.forall_fin_succ]
    simp only [Fin.val_zero, Fin.val_succ, blockVal, zero_mul, List.drop_zero,
      List.drop_drop, show ∀ j : ℕ, (j + 1) * L = L + j * L from fun j => by ring]

/-! ### Conditioning on a prefix: bounds -/

/-- **Conditioning**: if the first `m₁` bits satisfy `A` with probability `p`, and for each
such prefix `u` the remaining `m₂` bits satisfy `C u` with probability `≥ ε`, then the
whole string satisfies `C` with probability `≥ p·ε`.

**Proof sketch.** Splitting strings by `Fin.append`, the count of good strings is the sum
over prefixes `u` of the count of good suffixes; bound each summand with `u ∈ A` below
by `ε·2^{m₂}` and drop the others. -/
theorem randProb_append_ge (m₁ m₂ : ℕ) (A : List Bool → Prop) [DecidablePred A]
    (C : List Bool → List Bool → Prop) [∀ u, DecidablePred (C u)] {ε : ℚ}
    (h : ∀ u : Fin m₁ → Bool, A (List.ofFn u) → ε ≤ randProb m₂ (C (List.ofFn u))) :
    randProb m₁ A * ε ≤ randProb (m₁ + m₂) (fun r => C (r.take m₁) (r.drop m₁)) := by
  have hcard : #{r : Fin (m₁ + m₂) → Bool | C ((List.ofFn r).take m₁)
      ((List.ofFn r).drop m₁)} = ∑ u : Fin m₁ → Bool,
        #{v : Fin m₂ → Bool | C (List.ofFn u) (List.ofFn v)} := by
    rw [← Finset.card_equiv (Fin.appendEquiv m₁ m₂)
      (s := {uv : (Fin m₁ → Bool) × (Fin m₂ → Bool) |
        C (List.ofFn uv.1) (List.ofFn uv.2)}) fun uv => by
        simp only [mem_filter, mem_univ, true_and]
        change _ ↔ C ((List.ofFn (Fin.append uv.1 uv.2)).take m₁)
          ((List.ofFn (Fin.append uv.1 uv.2)).drop m₁)
        rw [List.ofFn_fin_append, List.take_left' (by simp), List.drop_left' (by simp)]]
    rw [Finset.card_filter, Fintype.sum_prod_type]
    simp only [Finset.card_filter]
  have heq : randProb (m₁ + m₂) (fun r => C (r.take m₁) (r.drop m₁)) =
      (∑ u : Fin m₁ → Bool, randProb m₂ (C (List.ofFn u))) / 2 ^ m₁ := by
    unfold randProb
    rw [hcard, Nat.cast_sum, pow_add, ← Finset.sum_div, div_div, mul_comm]
  rw [heq]
  unfold randProb
  rw [mul_comm, ← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  calc ε * #{u : Fin m₁ → Bool | A (List.ofFn u)}
      = ∑ u ∈ {u : Fin m₁ → Bool | A (List.ofFn u)}, ε := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ u ∈ {u : Fin m₁ → Bool | A (List.ofFn u)}, randProb m₂ (C (List.ofFn u)) :=
        Finset.sum_le_sum fun u hu => h u (by simpa using hu)
    _ ≤ ∑ u : Fin m₁ → Bool, randProb m₂ (C (List.ofFn u)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => randProb_nonneg

/-- **Conditioning on a prefix, upper bound**: if `C u v` forces `A u`, and for each prefix
`u ∈ A` the suffix event has probability at most `ε`, then `Pr[C] ≤ Pr[A] · ε`.

**Proof sketch.** Bound the complement from below by `randProb_append_ge` twice: on `A` the
suffix misses `C` with probability at least `1 - ε`, off `A` always. -/
theorem randProb_append_le (m₁ m₂ : ℕ) (A : List Bool → Prop) [DecidablePred A]
    (C : List Bool → List Bool → Prop) [∀ u, DecidablePred (C u)] {ε : ℚ}
    (hCA : ∀ u v, C u v → A u)
    (h : ∀ u : Fin m₁ → Bool, A (List.ofFn u) → randProb m₂ (C (List.ofFn u)) ≤ ε) :
    randProb (m₁ + m₂) (fun r => C (r.take m₁) (r.drop m₁)) ≤ randProb m₁ A * ε := by
  have h1 := randProb_append_ge m₁ m₂ A (fun u v => A u ∧ ¬ C u v) (ε := 1 - ε) fun u hu => by
    rw [randProb_congr (B := fun v => ¬ C (List.ofFn u) v) fun r => by simp [hu],
      randProb_not]
    linarith [h u hu]
  have h2 := randProb_append_ge m₁ m₂ (fun u => ¬ A u) (fun u _ => ¬ A u) (ε := 1)
    fun u hu => le_of_eq (by
      rw [randProb_congr (B := fun _ => True) fun r => by simp [hu], randProb_true])
  have hsplit : randProb (m₁ + m₂) (fun r => ¬ C (r.take m₁) (r.drop m₁)) =
      randProb (m₁ + m₂) (fun r => A (r.take m₁) ∧ ¬ C (r.take m₁) (r.drop m₁)) +
        randProb (m₁ + m₂) (fun r => ¬ A (r.take m₁)) := by
    rw [← randProb_or_disjoint (fun r => A (r.take m₁) ∧ ¬ C (r.take m₁) (r.drop m₁))
      (fun r => ¬ A (r.take m₁)) fun r h => h.2 h.1.1]
    refine randProb_congr fun r => ?_
    by_cases hA : A ((List.ofFn r).take m₁)
    · simp [hA]
    · simp only [hA, false_and, not_false_eq_true, or_true, iff_true]
      exact fun hc => hA (hCA _ _ hc)
  have hnot : randProb (m₁ + m₂) (fun r => ¬ C (r.take m₁) (r.drop m₁)) =
      1 - randProb (m₁ + m₂) (fun r => C (r.take m₁) (r.drop m₁)) := randProb_not _
  have hA : randProb m₁ (fun u => ¬ A u) = 1 - randProb m₁ A := randProb_not _
  have h2' : randProb m₁ (fun u => ¬ A u) ≤
      randProb (m₁ + m₂) (fun r => ¬ A (r.take m₁)) := by simpa using h2
  have h1' : randProb m₁ A * (1 - ε) ≤
      randProb (m₁ + m₂) (fun r => A (r.take m₁) ∧ ¬ C (r.take m₁) (r.drop m₁)) := h1
  rw [mul_sub, mul_one] at h1'
  linarith

end Randomized
