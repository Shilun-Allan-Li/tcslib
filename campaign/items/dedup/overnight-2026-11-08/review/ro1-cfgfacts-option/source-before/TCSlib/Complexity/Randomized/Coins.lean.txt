/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.ExpectedTime
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Biased coins from fair coins and fair coins from biased coins

[AB09, §7.4.3]: a `ρ`-coin can be simulated from fair coins (Lemma 7.12) and a fair coin from
`ρ`-coins (Lemma 7.13, von Neumann). Both procedures are coin runs in the sense of
`TCSlib.Complexity.Randomized.ExpectedTime`, analysed with exact finite probabilities.

## Main definitions

* `Randomized.rhoCoinRun` — Lemma 7.12's procedure for the bit sequence `p` of `ρ`.
* `Randomized.binVal`, `Randomized.binDigit` — the value of a bit sequence, and the binary
  digits of `ρ ∈ [0, 1)`.
* `Randomized.biasedProb` — the probability of an event over `m` independent `ρ`-coins.
* `Randomized.vonNeumannRun` — Lemma 7.13's pairs procedure.

## Main results

* `Randomized.expTimeLe_rhoCoinRun` — the `ρ`-coin procedure reads at most 2 bits in
  expectation, and `Randomized.exists_expCost_rhoCoinRun_le` gives expected time `O(1)` when
  bit `i` costs `poly(i)`; `Randomized.randProb_rhoCoinRun_le_binVal`,
  `Randomized.binVal_le_randProb_rhoCoinRun_add`, `Randomized.tendsto_randProb_rhoCoinRun` —
  `Pr[heads] = ρ` in the limit; `Randomized.randProb_rhoCoinRun_binDigit` —
  `Pr[heads within K bits] = ⌊2^K ρ⌋ / 2^K` for `ρ ∈ [0, 1)`. [AB09, Lemma 7.12]
* `Randomized.biasedProb_word`, `Randomized.biasedProb_half` — the word weights, and
  `ρ = 1/2` recovers `randProb`.
* `Randomized.vonNeumann_heads_eq_tails`, `Randomized.vonNeumann_heads`,
  `Randomized.tendsto_vonNeumann_heads`, `Randomized.vonNeumann_expected_pairs` —
  [AB09, Lemma 7.13].
* `Randomized.exists_sum_rpow_div_two_pow_le` — [AB09, Exercise 7.2].

## Divergences

* Costs are counted in coins (Lemma 7.12) and pairs of coins (Lemma 7.13) rather than machine
  steps. Lemma 7.12's hypothesis "the `i`-th bit of `ρ` is computable in `poly(i)` time" enters
  only as a cost `(i+1)^c` per bit (`exists_expCost_rhoCoinRun_le`); the bits are given as a
  sequence.
* Lemma 7.12 answers heads when the fair bit is `0` and `ρ_i = 1` (the book's `b_i < ρ_i`);
  `rhoCoinRun` returns `ρ_i` at the first disagreement, which is the same rule.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Finset Filter Topology

/-! ### Lemma 7.12: a `ρ`-coin from fair coins -/

/-- Compare fair bits with the bits `p 0, p 1, …` of `ρ` until they differ, and answer the bit
of `ρ` there (`true` = heads). [AB09, Lemma 7.12] -/
def rhoCoinRun : (ℕ → Bool) → List Bool → Option Bool
  | _, [] => none
  | p, b :: w => if b = p 0 then rhoCoinRun (fun i => p (i + 1)) w else some (p 0)

/-- The value `∑ᵢ pᵢ 2^{-(i+1)}` of the bit sequence `p`. -/
noncomputable def binVal (p : ℕ → Bool) : ℝ :=
  ∑' i, (if p i then (1 : ℝ) else 0) / 2 ^ (i + 1)

/-- The `i`-th binary digit (after the point) of `ρ`: the parity of `⌊2^{i+1} ρ⌋`. -/
noncomputable def binDigit (ρ : ℝ) (i : ℕ) : Bool :=
  decide (⌊(2 : ℝ) ^ (i + 1) * ρ⌋₊ % 2 = 1)

/-- The `ρ`-coin procedure is a prefix-stable run. -/
theorem rhoCoinRun_isPrefixStable (p : ℕ → Bool) : IsPrefixStable (rhoCoinRun p) := by
  intro w
  induction w generalizing p with
  | nil => intro v a h; simp [rhoCoinRun] at h
  | cons b w ih =>
    intro v a h
    by_cases hb : b = p 0
    · simp only [rhoCoinRun, hb, if_true, List.cons_append] at h ⊢
      exact ih _ v a h
    · simpa only [rhoCoinRun, hb, if_false, List.cons_append] using h

/-- The `ρ`-coin procedure is still running after `K` bits with probability `2^{-K}`. -/
theorem notHaltedProb_rhoCoinRun (p : ℕ → Bool) (K : ℕ) :
    notHaltedProb (rhoCoinRun p) K = (1 / 2) ^ K := by
  unfold notHaltedProb
  induction K generalizing p with
  | zero =>
    rw [randProb_congr (B := fun _ => True) fun r => by simp [rhoCoinRun]]
    simpa using randProb_true
  | succ K ih =>
    have e : ∀ b, (randProb K fun w => rhoCoinRun p (b :: w) = none) =
        if b = p 0 then (1 / 2) ^ K else 0 := by
      intro b
      by_cases hb : b = p 0
      · rw [if_pos hb, ← ih (fun i => p (i + 1))]
        exact randProb_congr fun r => by simp [rhoCoinRun, hb]
      · rw [if_neg hb, ← randProb_false (m := K)]
        exact randProb_congr fun r => by simp [rhoCoinRun, hb]
    rw [randProb_succ, e, e]
    cases p 0 <;> simp <;> ring

/-- [AB09, Lemma 7.12]: the `ρ`-coin procedure reads at most `2` fair bits in expectation. -/
theorem expTimeLe_rhoCoinRun (p : ℕ → Bool) : ExpTimeLe (rhoCoinRun p) 2 := by
  intro K
  simp only [notHaltedProb_rhoCoinRun]
  have := geom_sum_Ico_le_of_lt_one (x := (1 / 2 : ℚ)) (by norm_num) (by norm_num) (m := 0)
    (n := K)
  rw [← range_eq_Ico] at this
  exact this.trans (by norm_num)

/-- `Pr[heads within K bits] = ∑_{i<K} pᵢ 2^{-(i+1)}`.

**Proof sketch.** Induction on `K`, for all bit sequences at once. Condition on the first fair
bit: if it equals `p₀` the procedure continues on the shifted sequence (probability `1/2`
times the partial sum for `p₁ p₂ …`), otherwise it stops with answer `p₀` (probability `1/2`
times `[p₀ = 1]`). The shifted partial sum, halved, is the original one minus its first
term. -/
theorem randProb_rhoCoinRun_eq_sum (p : ℕ → Bool) (K : ℕ) :
    randProb K (fun w => rhoCoinRun p w = some true) =
      ∑ i ∈ range K, (if p i then (1 : ℚ) else 0) / 2 ^ (i + 1) := by
  induction K generalizing p with
  | zero => rw [randProb_congr (B := fun _ => False) fun r => by simp [rhoCoinRun]]
            simpa using randProb_false
  | succ K ih =>
    have e : ∀ b, (randProb K fun w => rhoCoinRun p (b :: w) = some true) =
        if b = p 0 then ∑ i ∈ range K, (if p (i + 1) then (1 : ℚ) else 0) / 2 ^ (i + 1)
        else if p 0 then 1 else 0 := by
      intro b
      by_cases hb : b = p 0
      · rw [if_pos hb, ← ih (fun i => p (i + 1))]
        exact randProb_congr fun r => by simp [rhoCoinRun, hb]
      · rw [if_neg hb]
        by_cases hp : p 0 = true
        · rw [if_pos hp, randProb_congr (B := fun _ => True) fun r => by
            simp only [rhoCoinRun]; rw [if_neg hb]; simp [hp]]
          exact randProb_true
        · rw [if_neg hp, randProb_congr (B := fun _ => False) fun r => by
            simp only [rhoCoinRun]; rw [if_neg hb]; simp [hp]]
          exact randProb_false
    have hdiv : ∑ i ∈ range K, (if p (i + 1) then (1 : ℚ) else 0) / 2 ^ (i + 1 + 1) =
        (∑ i ∈ range K, (if p (i + 1) then (1 : ℚ) else 0) / 2 ^ (i + 1)) / 2 := by
      rw [Finset.sum_div]; exact sum_congr rfl fun i _ => by rw [pow_succ]; ring
    rw [randProb_succ, e, e, sum_range_succ', hdiv]
    cases p 0 <;> first | (simp; done) | (simp; ring)

/-- [AB09, Lemma 7.12, with Exercise 7.2]: if reading the `i`-th bit of `ρ` costs `(i+1)^c`
steps, the expected total cost `∑_t (t+1)^c · Pr[T > t]` is bounded by a constant depending
only on `c`, i.e. the procedure runs in expected time `O(1)`. -/
theorem exists_expCost_rhoCoinRun_le (c : ℕ) : ∃ C : ℚ, ∀ (p : ℕ → Bool) (K : ℕ),
    ∑ t ∈ range K, ((t : ℚ) + 1) ^ c * notHaltedProb (rhoCoinRun p) t ≤ C := by
  have hs : Summable fun n : ℕ => ((n : ℝ) + 1) ^ c * (1 / 2) ^ n := by
    have h := (summable_nat_add_iff 1).2
      (summable_pow_mul_geometric_of_norm_lt_one c (r := (1 / 2 : ℝ)) (by norm_num))
    refine (h.mul_left 2).congr fun n => ?_
    push_cast; ring
  obtain ⟨C, hC⟩ := exists_rat_gt (∑' n : ℕ, ((n : ℝ) + 1) ^ c * (1 / 2) ^ n)
  refine ⟨C, fun p K => ?_⟩
  simp only [notHaltedProb_rhoCoinRun]
  have h : ((∑ t ∈ range K, ((t : ℚ) + 1) ^ c * (1 / 2) ^ t : ℚ) : ℝ) ≤
      ∑' n : ℕ, ((n : ℝ) + 1) ^ c * (1 / 2) ^ n := by
    push_cast
    exact hs.sum_le_tsum _ (fun i _ => by positivity)
  exact_mod_cast h.trans hC.le

/-- The terms of `binVal` are summable. -/
theorem summable_binVal (p : ℕ → Bool) :
    Summable fun i => (if p i then (1 : ℝ) else 0) / 2 ^ (i + 1) := by
  refine (summable_geometric_two' 1).of_nonneg_of_le (fun i => by positivity) fun i => ?_
  rw [div_div, ← pow_succ']
  split_ifs <;> simp

/-- `Pr[heads within K bits]`, in `ℝ`, is the `K`-th partial sum of `binVal`. -/
theorem randProb_rhoCoinRun_eq_sum_real (p : ℕ → Bool) (K : ℕ) :
    (randProb K (fun w => rhoCoinRun p w = some true) : ℝ) =
      ∑ i ∈ range K, (if p i then (1 : ℝ) else 0) / 2 ^ (i + 1) := by
  rw [randProb_rhoCoinRun_eq_sum]; push_cast
  exact sum_congr rfl fun i _ => by split_ifs <;> simp

/-- [AB09, Lemma 7.12]: `Pr[heads within K bits] ≤ ρ`. -/
theorem randProb_rhoCoinRun_le_binVal (p : ℕ → Bool) (K : ℕ) :
    (randProb K (fun w => rhoCoinRun p w = some true) : ℝ) ≤ binVal p := by
  rw [randProb_rhoCoinRun_eq_sum_real, binVal,
    ← (summable_binVal p).sum_add_tsum_nat_add K]
  exact le_add_of_nonneg_right (tsum_nonneg fun i => by positivity)

/-- [AB09, Lemma 7.12]: `ρ ≤ Pr[heads within K bits] + 2^{-K}`.

**Proof sketch.** `ρ` is the partial sum plus the tail `∑_{i ≥ K} pᵢ 2^{-(i+1)}`, and the
tail is at most `∑_{i ≥ K} 2^{-(i+1)} = 2^{-K}`. -/
theorem binVal_le_randProb_rhoCoinRun_add (p : ℕ → Bool) (K : ℕ) :
    binVal p ≤ (randProb K (fun w => rhoCoinRun p w = some true) : ℝ) + (1 / 2) ^ K := by
  rw [randProb_rhoCoinRun_eq_sum_real, binVal,
    ← (summable_binVal p).sum_add_tsum_nat_add K]
  gcongr
  have hg : Summable fun i : ℕ => (1 / 2 : ℝ) ^ K * (1 / 2 / 2 ^ i) :=
    (summable_geometric_two' 1).mul_left _
  calc ∑' i, (if p (i + K) then (1 : ℝ) else 0) / 2 ^ (i + K + 1)
      ≤ ∑' i : ℕ, (1 / 2 : ℝ) ^ K * (1 / 2 / 2 ^ i) := by
        refine ((summable_nat_add_iff K).2 (summable_binVal p)).tsum_le_tsum (fun i => ?_) hg
        have hr : (1 / 2 : ℝ) ^ K * (1 / 2 / 2 ^ i) = 1 / 2 ^ (i + K + 1) := by
          rw [one_div_pow, pow_succ, pow_add]; field_simp
        rw [hr]
        gcongr
        split_ifs <;> norm_num
    _ = (1 / 2) ^ K := by rw [tsum_mul_left, tsum_geometric_two', mul_one]

/-- [AB09, Lemma 7.12]: `Pr[heads within K bits] → ρ`, so the procedure outputs heads with
probability exactly `ρ`. -/
theorem tendsto_randProb_rhoCoinRun (p : ℕ → Bool) :
    Tendsto (fun K => (randProb K (fun w => rhoCoinRun p w = some true) : ℝ)) atTop
      (𝓝 (binVal p)) := by
  have hlow : Tendsto (fun K : ℕ => binVal p - (1 / 2 : ℝ) ^ K) atTop (𝓝 (binVal p)) := by
    simpa using tendsto_const_nhds.sub
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun K => ?_)
    (fun K => randProb_rhoCoinRun_le_binVal p K)
  linarith [binVal_le_randProb_rhoCoinRun_add p K]

/-- The all-ones sequence has value `1`. -/
theorem binVal_const_true : binVal (fun _ => true) = 1 := by
  calc binVal (fun _ => true) = ∑' i : ℕ, (1 : ℝ) / 2 / 2 ^ i :=
        tsum_congr fun i => by rw [if_pos rfl, pow_succ]; ring
    _ = 1 := tsum_geometric_two' 1

/-- For `ρ < 1`, the partial sums of the digits of `ρ` are `⌊2^K ρ⌋ / 2^K`.

**Proof sketch.** Induction on `K`: `⌊2^{K+1} ρ⌋ = 2 ⌊2^K ρ⌋ + d_K` where `d_K` is its
parity, since `⌊2^{K+1} ρ⌋ / 2 = ⌊2^K ρ⌋`. -/
theorem sum_binDigit {ρ : ℝ} (h1 : ρ < 1) (K : ℕ) :
    ∑ i ∈ range K, (if binDigit ρ i then (1 : ℝ) else 0) / 2 ^ (i + 1) =
      ⌊(2 : ℝ) ^ K * ρ⌋₊ / 2 ^ K := by
  induction K with
  | zero => simp [Nat.floor_eq_zero.mpr h1]
  | succ K ih =>
    rw [sum_range_succ, ih, binDigit]
    have hdiv : ⌊(2 : ℝ) ^ (K + 1) * ρ⌋₊ / 2 = ⌊(2 : ℝ) ^ K * ρ⌋₊ := by
      have := Nat.floor_div_natCast ((2 : ℝ) ^ (K + 1) * ρ) 2
      rw [show (2 : ℝ) ^ (K + 1) * ρ / ((2 : ℕ) : ℝ) = 2 ^ K * ρ by push_cast; ring] at this
      exact this.symm
    set n := ⌊(2 : ℝ) ^ (K + 1) * ρ⌋₊
    have hn : (n : ℝ) = 2 * ⌊(2 : ℝ) ^ K * ρ⌋₊ + (n % 2 : ℕ) := by
      rw [← hdiv]; exact_mod_cast (Nat.div_add_mod n 2).symm
    have hd : (if decide (n % 2 = 1) = true then (1 : ℝ) else 0) = ((n % 2 : ℕ) : ℝ) := by
      rcases Nat.mod_two_eq_zero_or_one n with hm | hm <;> simp [hm]
    rw [hd, hn, pow_succ]
    field_simp

/-- [AB09, Lemma 7.12] for `ρ < 1` with its binary digits: `Pr[heads within K bits]` is
`⌊2^K ρ⌋ / 2^K`, hence lies in `(ρ - 2^{-K}, ρ]`. -/
theorem randProb_rhoCoinRun_binDigit {ρ : ℝ} (h1 : ρ < 1) (K : ℕ) :
    (randProb K (fun w => rhoCoinRun (binDigit ρ) w = some true) : ℝ) =
      ⌊(2 : ℝ) ^ K * ρ⌋₊ / 2 ^ K := by
  rw [randProb_rhoCoinRun_eq_sum_real, sum_binDigit h1]

/-- The binary digits of `ρ ∈ [0, 1)` have value `ρ`. -/
theorem binVal_binDigit {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) : binVal (binDigit ρ) = ρ := by
  refine le_antisymm ?_ ?_
  · refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    have h := binVal_le_randProb_rhoCoinRun_add (binDigit ρ) K
    rw [randProb_rhoCoinRun_binDigit h1] at h
    have hfl : (⌊(2 : ℝ) ^ K * ρ⌋₊ : ℝ) / 2 ^ K ≤ ρ := by
      rw [div_le_iff₀ (by positivity), mul_comm]; exact Nat.floor_le (by positivity)
    linarith
  · refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    have h := randProb_rhoCoinRun_le_binVal (binDigit ρ) K
    rw [randProb_rhoCoinRun_binDigit h1] at h
    have hfl : ρ < (⌊(2 : ℝ) ^ K * ρ⌋₊ : ℝ) / 2 ^ K + (1 / 2) ^ K := by
      rw [one_div_pow, ← add_div, lt_div_iff₀ (by positivity), mul_comm]
      exact Nat.lt_floor_add_one _
    linarith

/-! ### The biased measure -/

open Classical in
/-- `Pr[A]` over `m` independent `ρ`-coins (`true` with probability `ρ`), by conditioning on
the first coin. [AB09, §7.4.3] On words of length `m` this is the coin-word form of
`biasedProbability` (`BooleanAnalysis/.../SharpThresholds/Definitions.lean`) on `BoolCube m`. -/
noncomputable def biasedProb (ρ : ℝ) : ℕ → (List Bool → Prop) → ℝ
  | 0, A => if A [] then 1 else 0
  | m + 1, A => ρ * biasedProb ρ m (fun w => A (true :: w)) +
      (1 - ρ) * biasedProb ρ m (fun w => A (false :: w))

variable {ρ : ℝ}

/-- Conditioning on the first `ρ`-coin. -/
theorem biasedProb_succ (m : ℕ) (A : List Bool → Prop) :
    biasedProb ρ (m + 1) A = ρ * biasedProb ρ m (fun w => A (true :: w)) +
      (1 - ρ) * biasedProb ρ m (fun w => A (false :: w)) := rfl

/-- Events agreeing on all words of length `m` have the same probability. -/
theorem biasedProb_congr {m : ℕ} {A B : List Bool → Prop}
    (h : ∀ w : List Bool, w.length = m → (A w ↔ B w)) : biasedProb ρ m A = biasedProb ρ m B := by
  induction m generalizing A B with
  | zero =>
    have hAB := h [] rfl
    by_cases hA : A []
    · simp [biasedProb, hA, hAB.mp hA]
    · simp [biasedProb, hA, mt hAB.mpr hA]
  | succ m ih =>
    rw [biasedProb_succ, biasedProb_succ, ih fun w hw => h _ (by simp [hw]),
      ih fun w hw => h _ (by simp [hw])]

/-- The certain event has probability one. -/
@[simp] theorem biasedProb_true (m : ℕ) : biasedProb ρ m (fun _ => True) = 1 := by
  induction m with
  | zero => simp [biasedProb]
  | succ m ih => rw [biasedProb_succ, ih]; ring

/-- The impossible event has probability zero. -/
@[simp] theorem biasedProb_false (m : ℕ) : biasedProb ρ m (fun _ => False) = 0 := by
  induction m with
  | zero => simp [biasedProb]
  | succ m ih => rw [biasedProb_succ, ih]; ring

/-- The probability of a single word is the product of its coin weights `ρ` (for `1`) and
`1 - ρ` (for `0`). [AB09, §7.4.3] -/
theorem biasedProb_word (u : List Bool) :
    biasedProb ρ u.length (fun w => w = u) = (u.map fun b => if b then ρ else 1 - ρ).prod := by
  induction u with
  | nil => simp [biasedProb]
  | cons b u ih =>
    rw [List.length_cons, biasedProb_succ, List.map_cons, List.prod_cons]
    cases b
    · rw [biasedProb_congr (A := fun w => true :: w = false :: u) (B := fun _ => False)
          fun w _ => by simp,
        biasedProb_congr (A := fun w => false :: w = false :: u) (B := fun w => w = u)
          fun w _ => by simp, ih]
      simp
    · rw [biasedProb_congr (A := fun w => true :: w = true :: u) (B := fun w => w = u)
          fun w _ => by simp,
        biasedProb_congr (A := fun w => false :: w = true :: u) (B := fun _ => False)
          fun w _ => by simp, ih]
      simp

/-- Fair coins: `biasedProb (1/2)` is `randProb`. -/
theorem biasedProb_half (m : ℕ) (A : List Bool → Prop) [DecidablePred A] :
    biasedProb (1 / 2) m A = (randProb m A : ℝ) := by
  induction m generalizing A with
  | zero =>
    by_cases hA : A []
    · rw [randProb_congr (B := fun _ => True) fun r => by simp [hA], randProb_true]
      simp [biasedProb, hA]
    · rw [randProb_congr (B := fun _ => False) fun r => by simp [hA], randProb_false]
      simp [biasedProb, hA]
  | succ m ih =>
    rw [biasedProb_succ, randProb_succ, ih, ih]
    push_cast; ring

/-! ### Lemma 7.13: von Neumann's fair coin from `ρ`-coins -/

/-- Read the coins in pairs until a pair differs, and answer its first coin.
[AB09, Lemma 7.13] -/
def vonNeumannRun : List Bool → Option Bool
  | a :: b :: w => if a = b then vonNeumannRun w else some a
  | _ => none

/-- Two `ρ`-coins at once. -/
theorem biasedProb_two (K : ℕ) (A : List Bool → Prop) :
    biasedProb ρ (2 * (K + 1)) A =
      ρ * (ρ * biasedProb ρ (2 * K) (fun w => A (true :: true :: w)) +
        (1 - ρ) * biasedProb ρ (2 * K) (fun w => A (true :: false :: w))) +
      (1 - ρ) * (ρ * biasedProb ρ (2 * K) (fun w => A (false :: true :: w)) +
        (1 - ρ) * biasedProb ρ (2 * K) (fun w => A (false :: false :: w))) := by
  rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring]; rfl

/-- After `K` pairs, von Neumann's procedure is still running with probability
`(ρ² + (1 - ρ)²)^K`. -/
theorem vonNeumann_none (K : ℕ) :
    biasedProb ρ (2 * K) (fun w => vonNeumannRun w = none) = (ρ ^ 2 + (1 - ρ) ^ 2) ^ K := by
  induction K with
  | zero => simp [biasedProb, vonNeumannRun]
  | succ K ih =>
    rw [biasedProb_two]
    simp only [vonNeumannRun, if_true, Bool.true_eq_false, Bool.false_eq_true, if_false,
      reduceCtorEq, biasedProb_false, ih]
    ring

/-- Within `K` pairs, von Neumann's procedure answers heads with probability
`(1 - (ρ² + (1 - ρ)²)^K) / 2`. [AB09, Lemma 7.13] -/
theorem vonNeumann_heads (K : ℕ) :
    biasedProb ρ (2 * K) (fun w => vonNeumannRun w = some true) =
      (1 - (ρ ^ 2 + (1 - ρ) ^ 2) ^ K) / 2 := by
  induction K with
  | zero => simp [biasedProb, vonNeumannRun]
  | succ K ih =>
    rw [biasedProb_two]
    simp only [vonNeumannRun, if_true, Bool.true_eq_false, Bool.false_eq_true, if_false,
      biasedProb_false, biasedProb_true, ih, Option.some.injEq]
    ring

/-- Within `K` pairs, von Neumann's procedure answers tails with probability
`(1 - (ρ² + (1 - ρ)²)^K) / 2`. [AB09, Lemma 7.13] -/
theorem vonNeumann_tails (K : ℕ) :
    biasedProb ρ (2 * K) (fun w => vonNeumannRun w = some false) =
      (1 - (ρ ^ 2 + (1 - ρ) ^ 2) ^ K) / 2 := by
  induction K with
  | zero => simp [biasedProb, vonNeumannRun]
  | succ K ih =>
    rw [biasedProb_two]
    simp only [vonNeumannRun, if_true, Bool.true_eq_false, Bool.false_eq_true, if_false,
      biasedProb_false, biasedProb_true, ih, Option.some.injEq]
    ring

/-- **von Neumann** [AB09, Lemma 7.13]: for every `ρ` and every number `K` of pairs, heads and
tails are equally likely, so the output is a fair coin conditioned on halting. -/
theorem vonNeumann_heads_eq_tails (K : ℕ) :
    biasedProb ρ (2 * K) (fun w => vonNeumannRun w = some true) =
      biasedProb ρ (2 * K) (fun w => vonNeumannRun w = some false) := by
  rw [vonNeumann_heads, vonNeumann_tails]

/-- [AB09, Lemma 7.13]: for `0 < ρ < 1`, `Pr[heads within K pairs] → 1/2`. -/
theorem tendsto_vonNeumann_heads (h0 : 0 < ρ) (h1 : ρ < 1) :
    Tendsto (fun K => biasedProb ρ (2 * K) (fun w => vonNeumannRun w = some true)) atTop
      (𝓝 (1 / 2)) := by
  simp only [vonNeumann_heads]
  have hs0 : 0 ≤ ρ ^ 2 + (1 - ρ) ^ 2 := by positivity
  have hs1 : ρ ^ 2 + (1 - ρ) ^ 2 < 1 := by nlinarith
  simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hs0 hs1).const_sub 1).div_const 2

/-- **von Neumann** [AB09, Lemma 7.13]: for `0 < ρ < 1` the expected number of pairs read is at
most `1 / (2ρ(1 - ρ))`: every tail sum `∑_{K<M} Pr[not halted after K pairs]` is bounded. -/
theorem vonNeumann_expected_pairs (h0 : 0 < ρ) (h1 : ρ < 1) (M : ℕ) :
    ∑ K ∈ range M, biasedProb ρ (2 * K) (fun w => vonNeumannRun w = none) ≤
      1 / (2 * ρ * (1 - ρ)) := by
  simp only [vonNeumann_none]
  have hs : ρ ^ 2 + (1 - ρ) ^ 2 = 1 - 2 * ρ * (1 - ρ) := by ring
  have hpos : 0 < 2 * ρ * (1 - ρ) := mul_pos (by linarith) (by linarith)
  have := geom_sum_Ico_le_of_lt_one (x := ρ ^ 2 + (1 - ρ) ^ 2) (by positivity)
    (by rw [hs]; linarith) (m := 0) (n := M)
  rw [hs]
  rwa [← range_eq_Ico, pow_zero, hs, sub_sub_cancel] at this

/-! ### Exercise 7.2 -/

/-- **[AB09, Exercise 7.2]**: for every real `c` there is `D` with `∑_{i=1}^n i^c / 2^i ≤ D` for
all `n ≥ 1`. (Stated for every real `c`, the book's `c > 0` included.)

**Proof sketch.** For `i ≥ 1`, `i^c ≤ i^⌈c⌉`, and `∑ i^⌈c⌉ (1/2)^i` converges
(`summable_pow_mul_geometric_of_norm_lt_one`); take `D` its sum. -/
theorem exists_sum_rpow_div_two_pow_le (c : ℝ) :
    ∃ D : ℝ, ∀ n : ℕ, 1 ≤ n → ∑ i ∈ Icc 1 n, (i : ℝ) ^ c / 2 ^ i ≤ D := by
  set k := ⌈c⌉₊
  have hs : Summable fun i : ℕ => (i : ℝ) ^ k * (1 / 2) ^ i :=
    summable_pow_mul_geometric_of_norm_lt_one k (r := (1 / 2 : ℝ)) (by norm_num)
  refine ⟨∑' i : ℕ, (i : ℝ) ^ k * (1 / 2) ^ i, fun n _ => ?_⟩
  calc ∑ i ∈ Icc 1 n, (i : ℝ) ^ c / 2 ^ i
      ≤ ∑ i ∈ Icc 1 n, (i : ℝ) ^ k * (1 / 2) ^ i := by
        refine sum_le_sum fun i hi => ?_
        have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (mem_Icc.mp hi).1
        rw [one_div_pow, mul_one_div]
        gcongr
        calc (i : ℝ) ^ c ≤ (i : ℝ) ^ (k : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hi1 (Nat.le_ceil c)
          _ = (i : ℝ) ^ k := Real.rpow_natCast _ _
    _ ≤ ∑' i : ℕ, (i : ℝ) ^ k * (1 / 2) ^ i := hs.sum_le_tsum _ (fun i _ => by positivity)

end Randomized
