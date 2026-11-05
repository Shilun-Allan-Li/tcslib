/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.Coins
import TCSlib.Complexity.Randomized.ErrorReduction
import TCSlib.Complexity.Randomized.PTMEquiv

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probabilistic machines with a `ρ`-coin

The setting of [AB09, §7.4.3] and Exercise 7.5: a PTM whose coins come up `1` with probability
`ρ` instead of `1/2`. The probability of an event over `m` such coins is `Randomized.biasedProb`
(`TCSlib.Complexity.Randomized.Coins`). This file identifies it with the product Bernoulli
measure `Randomized.iidBernoulli`, so that Hoeffding's bound applies to `ρ`-coins, defines
bounded-error decision with a `ρ`-coin, and turns polynomial-time verifiers into such machines.

## Main definitions

* `Turing.FinNDTM.biasedOutputProb` — `Pr[M(x) = v]` over `t` `ρ`-coins.
* `Turing.FinNDTM.BiasedBPDecidesInTime`, `Randomized.biasedBPTIME`, `Randomized.biasedBPP` —
  [AB09, Def 7.2] with a `ρ`-coin.

## Main results

* `Randomized.biasedProb_eq_toReal_iidBernoulli` — `biasedProb` is the product measure.
* `Randomized.biasedProb_count_dev_le` — Hoeffding for `ρ`-coins.
* `Randomized.biasedBPP_half` — with `ρ = 1/2` the class is `BPP` ([AB09, Def 7.2]).
* `Randomized.mem_biasedBPP_of_eff` — a polynomial-time verifier correct with probability
  `≥ 2/3` over `ρ`-coins gives a language in `biasedBPP ρ`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Finset MeasureTheory Complexity Turing
open scoped NNReal ENNReal

variable {ρ : ℝ}

/-! ### Elementary properties of `biasedProb` -/

/-- Complement rule for `ρ`-coins. -/
theorem biasedProb_not (m : ℕ) (A : List Bool → Prop) :
    biasedProb ρ m (fun w => ¬ A w) = 1 - biasedProb ρ m A := by
  induction m generalizing A with
  | zero => by_cases h : A [] <;> simp [biasedProb, h]
  | succ m ih => rw [biasedProb_succ, biasedProb_succ, ih, ih]; ring

/-- `ρ`-coin probabilities are monotone in the event, for `0 ≤ ρ ≤ 1`. -/
theorem biasedProb_mono (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {m : ℕ} {A B : List Bool → Prop}
    (h : ∀ w : List Bool, w.length = m → A w → B w) : biasedProb ρ m A ≤ biasedProb ρ m B := by
  induction m generalizing A B with
  | zero =>
    by_cases hA : A []
    · simp [biasedProb, hA, h [] rfl hA]
    · simp only [biasedProb, hA, if_false]; split_ifs <;> norm_num
  | succ m ih =>
    rw [biasedProb_succ, biasedProb_succ]
    have e1 := ih (A := fun w => A (true :: w)) (B := fun w => B (true :: w))
      fun w hw => h _ (by simp [hw])
    have e2 := ih (A := fun w => A (false :: w)) (B := fun w => B (false :: w))
      fun w hw => h _ (by simp [hw])
    have := mul_le_mul_of_nonneg_left e1 h0
    have := mul_le_mul_of_nonneg_left e2 (by linarith : (0 : ℝ) ≤ 1 - ρ)
    linarith

/-- An event of the coins after the first `s` has its probability over the remaining coins. -/
theorem biasedProb_drop (s n : ℕ) (P : List Bool → Prop) :
    biasedProb ρ (s + n) (fun w => P (w.drop s)) = biasedProb ρ n P := by
  induction s generalizing n with
  | zero => simp
  | succ s ih =>
    rw [show s + 1 + n = (s + n) + 1 by omega, biasedProb_succ]
    simp only [List.drop_succ_cons]
    rw [ih]; ring

/-- An event of the first `n` coins has its probability over `n` coins. -/
theorem biasedProb_take (n t : ℕ) (P : List Bool → Prop) :
    biasedProb ρ (n + t) (fun w => P (w.take n)) = biasedProb ρ n P := by
  induction n generalizing P with
  | zero =>
    classical
    simp only [List.take_zero, Nat.zero_add]
    by_cases h : P []
    · simp [h, biasedProb]
    · simp [h, biasedProb]
  | succ n ih =>
    rw [show n + 1 + t = (n + t) + 1 by omega, biasedProb_succ, biasedProb_succ]
    simp only [List.take_succ_cons]
    rw [ih (fun w => P (true :: w)), ih (fun w => P (false :: w))]

/-- A condition on the slice `w[s, s+T)` of `m ≥ s + T` `ρ`-coins has its probability over
`T` coins. -/
theorem biasedProb_drop_take {s T m : ℕ} (h : s + T ≤ m) (B : List Bool → Prop) :
    biasedProb ρ m (fun w => B ((w.drop s).take T)) = biasedProb ρ T B := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_assoc, biasedProb_drop s (T + e) (fun v => B (v.take T)), biasedProb_take]

/-- **Projection onto marked coordinates preserves `ρ`-coins**: the coins of a `ρ`-coin word at
the marked positions of `mask` are independent `ρ`-coins. -/
theorem biasedProb_maskSelect (mask : List Bool) (A : List Bool → Prop) :
    biasedProb ρ mask.length (fun w => A (maskSelect mask w)) =
      biasedProb ρ (mask.filter id).length A := by
  induction mask generalizing A with
  | nil =>
    simp only [List.length_nil, List.filter_nil]
    rfl
  | cons emit mask ih =>
    rw [List.length_cons, biasedProb_succ]
    cases emit with
    | false =>
      simp only [maskSelect, if_false, List.nil_append, List.filter_cons, id,
        Bool.false_eq_true]
      rw [ih A]
      ring
    | true =>
      simp only [maskSelect, if_true, List.singleton_append, List.filter_cons, id,
        List.length_cons]
      rw [ih (fun u => A (true :: u)), ih (fun u => A (false :: u)), biasedProb_succ]

/-! ### `biasedProb` is the product Bernoulli measure -/

/-- `biasedProb` as a sum of word weights `∏ᵢ (ρ if wᵢ = 1 else 1 - ρ)` over the event. -/
theorem biasedProb_eq_sum (m : ℕ) (A : List Bool → Prop) [DecidablePred A] :
    biasedProb ρ m A = ∑ w : Fin m → Bool,
      if A (List.ofFn w) then ∏ i, (if w i then ρ else 1 - ρ) else 0 := by
  induction m generalizing A with
  | zero =>
    by_cases hA : A [] <;> simp [biasedProb, hA]
  | succ m ih =>
    rw [biasedProb_succ, ih, ih, ← (Fin.consEquiv fun _ => Bool).sum_comp,
      Fintype.sum_prod_type, Fintype.sum_bool, mul_sum, mul_sum]
    congr 1 <;> refine sum_congr rfl fun w _ => ?_ <;>
      simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
        Fin.prod_univ_succ, if_true, Bool.false_eq_true, if_false] <;>
      split_ifs <;> simp

/-- **`biasedProb` is the product measure**: for `0 ≤ ρ ≤ 1`, the probability of `A` over `m`
`ρ`-coins is the `iidBernoulli m ρ` measure of the words in `A`. [AB09, §7.4.3]

**Proof sketch.** Both are sums of word weights: `biasedProb_eq_sum` on one side, the
singleton masses `∏ᵢ Bernoulli(ωᵢ)` of the product measure (`Measure.pi_pi`) on the other. -/
theorem biasedProb_eq_toReal_iidBernoulli {p : ℝ≥0} (hp : p ≤ 1) (m : ℕ)
    (A : List Bool → Prop) :
    biasedProb (p : ℝ) m A = (iidBernoulli m p hp {ω | A (List.ofFn ω)}).toReal := by
  classical
  have hS : {ω : Fin m → Bool | A (List.ofFn ω)} =
      ↑(univ.filter fun ω : Fin m → Bool => A (List.ofFn ω)) := by ext; simp
  have hsing : ∀ ω : Fin m → Bool, iidBernoulli m p hp {ω} =
      ∏ i, (PMF.bernoulli p hp) (ω i) := fun ω => by
    rw [← Set.univ_pi_singleton, iidBernoulli, Measure.pi_pi]
    refine prod_congr rfl fun i _ => ?_
    exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)
  rw [hS, ← sum_measure_singleton, biasedProb_eq_sum, sum_filter,
    ENNReal.toReal_sum fun ω _ => ?_]
  · refine sum_congr rfl fun ω _ => ?_
    split_ifs
    · rw [hsing, ENNReal.toReal_prod]
      refine prod_congr rfl fun i _ => ?_
      cases ω i
      · simp only [PMF.bernoulli_apply, cond_false, Bool.false_eq_true, if_false]
        rw [ENNReal.coe_toReal, NNReal.coe_sub hp, NNReal.coe_one]
      · simp
    · rfl
  · split_ifs <;> simp

/-- The number of `1`s in `ω` is `successCount ω`. -/
theorem successCount_eq_count {k : ℕ} (ω : Fin k → Bool) :
    successCount ω = ((List.ofFn ω).count true : ℝ) := by
  induction k with
  | zero => simp [successCount]
  | succ k ih =>
    have := ih (fun i => ω i.succ)
    simp only [successCount] at this ⊢
    rw [Fin.sum_univ_succ, this, List.ofFn_succ, List.count_cons]
    cases ω 0 <;> simp; ring

/-- **Hoeffding for `ρ`-coins**: over `k > 0` `ρ`-coins, the fraction of `1`s is more than `δ`
away from `ρ` with probability at most `2e^{-2δ²k}`. -/
theorem biasedProb_count_dev_le {p : ℝ≥0} (hp : p ≤ 1) {k : ℕ} (hk : 0 < k) {δ : ℝ}
    (hδ : 0 < δ) :
    biasedProb (p : ℝ) k (fun w => δ < |(w.count true : ℝ) / k - p|) ≤
      2 * Real.exp (-2 * δ ^ 2 * k) := by
  rw [biasedProb_eq_toReal_iidBernoulli hp]
  have h := iid_bernoulli_avg_concentration hp hk hδ
  simp only [successCount_eq_count] at h
  calc _ ≤ (ENNReal.ofReal (2 * Real.exp (-2 * δ ^ 2 * k))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = _ := ENNReal.toReal_ofReal (by positivity)

end Randomized

/-! ### Machines with a `ρ`-coin -/

namespace Turing.FinNDTM

/-- `Pr[M(x) = v]` over `t` `ρ`-coins: the `ρ`-weight of the coin words of length `t` whose run
on `x` ends with output `v`. [AB09, §7.4.3] -/
noncomputable def biasedOutputProb (ρ : ℝ) (N : FinNDTM Bool) (x : List Bool) (t : ℕ)
    (v : List Bool) : ℝ :=
  Randomized.biasedProb ρ t fun w => N.outputWith x w = v

/-- The PTM `N` with a `ρ`-coin decides `L` in time `T` with bounded error: every branch halts
within `T(|x|)` steps and `Pr[M(x) = L(x)] ≥ 2/3`. [AB09, Def 7.2 with a `ρ`-coin, §7.4.3] -/
def BiasedBPDecidesInTime (ρ : ℝ) (N : FinNDTM Bool) (L : Language Bool) (T : ℕ → ℕ) :
    Prop :=
  ∀ x : List Bool, N.tm.HaltsWithin x (T x.length) ∧
    2/3 ≤ N.biasedOutputProb ρ x (T x.length) [MultiTapeTM.indicator (L : Set (List Bool)) x]

end Turing.FinNDTM

namespace Randomized

open Complexity Turing

/-- `BPTIME(T)` with a `ρ`-coin. [AB09, Def 7.2, §7.4.3] -/
def biasedBPTIME (ρ : ℝ) (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (N : FinNDTM Bool), N.BiasedBPDecidesInTime ρ L fun n => c * T n}

/-- `BPP` with a `ρ`-coin: `⋃_c biasedBPTIME ρ (n^c + 1)`. [AB09, §7.4.3, Exercise 7.5] -/
def biasedBPP (ρ : ℝ) : Set (Language Bool) := ⋃ c : ℕ, biasedBPTIME ρ fun n => n ^ c + 1

/-- With a fair coin the class is `BPP`: `biasedBPP (1/2) = BPP_PTM`. [AB09, Def 7.2] -/
theorem biasedBPP_half : biasedBPP (1 / 2) = BPP_PTM := by
  classical
  have h : ∀ (N : FinNDTM Bool) (L : Language Bool) (T : ℕ → ℕ),
      N.BiasedBPDecidesInTime (1 / 2) L T ↔ N.BPDecidesInTime L T := fun N L T => by
    refine forall_congr' fun x => and_congr Iff.rfl ?_
    rw [FinNDTM.biasedOutputProb, biasedProb_half, FinNDTM.outputProb]
    rw [show (2 / 3 : ℝ) = ((2 / 3 : ℚ) : ℝ) by norm_num, Rat.cast_le]
  ext L
  simp only [biasedBPP, BPP_PTM, Set.mem_iUnion, biasedBPTIME, BPTIME, Set.mem_setOf_eq, h]

/-- **Verifiers to `ρ`-coin machines**: a polynomial-time verifier `M` drawing `polyLen a k`
coins is simulated by a PTM running in time `K·(n^e + 1)` whose output distribution under
`ρ`-coins is that of `M(x, ·)` under `ρ`-coins, for every `ρ`.

**Proof sketch.** The machine of `exists_FinNDTM_maskSelect_of_eff` reads a coordinate
projection of a slice of its coins; such projections of `ρ`-coin words are `ρ`-coin words
(`biasedProb_drop_take`, `biasedProb_maskSelect`). -/
theorem exists_FinNDTM_biased_of_eff {M : List Bool → List Bool → Bool} {a k : ℕ}
    (hM : polyTimeModel.Eff (boolVerifier M)) :
    ∃ (K e : ℕ) (N : FinNDTM Bool), ∀ x : List Bool,
      N.tm.HaltsWithin x (K * (x.length ^ e + 1)) ∧
      ∀ (ρ : ℝ) (b : Bool), N.biasedOutputProb ρ x (K * (x.length ^ e + 1)) [b] =
        biasedProb ρ (polyLen a k x.length) fun u => M x u = b := by
  obtain ⟨K, e, N, hN⟩ := exists_FinNDTM_maskSelect_of_eff (a := a) (k := k) hM
  refine ⟨K, e, N, fun x => ?_⟩
  obtain ⟨s, mask, hcount, hle, hrun⟩ := hN x
  refine ⟨fun w hw => (hrun w hw).1, fun ρ b => ?_⟩
  unfold FinNDTM.biasedOutputProb
  rw [biasedProb_congr (B := fun w => M x (maskSelect mask ((w.drop s).take mask.length)) = b)
    fun w hw => by rw [(hrun w hw).2.1, List.singleton_inj],
    biasedProb_drop_take hle (fun v => M x (maskSelect mask v) = b),
    biasedProb_maskSelect mask (fun u => M x u = b), hcount]

/-- **A verifier over `ρ`-coins decides in `biasedBPP ρ`**: if a polynomial-time verifier `M`
with `polyLen a k` coins answers `L(x)` with `ρ`-coin probability at least `2/3` on every `x`,
then `L ∈ biasedBPP ρ`. [AB09, Def 7.2 ⇐ Def 7.3, with a `ρ`-coin] -/
theorem mem_biasedBPP_of_eff {ρ : ℝ} {L : Language Bool} {M : List Bool → List Bool → Bool}
    {a k : ℕ} (hM : polyTimeModel.Eff (boolVerifier M))
    (hL : ∀ x : List Bool, 2/3 ≤ biasedProb ρ (polyLen a k x.length)
      fun u => M x u = MultiTapeTM.indicator (L : Set (List Bool)) x) :
    L ∈ biasedBPP ρ := by
  obtain ⟨K, e, N, hN⟩ := exists_FinNDTM_biased_of_eff (a := a) (k := k) hM
  refine Set.mem_iUnion.mpr ⟨e, K, N, fun x => ⟨(hN x).1, ?_⟩⟩
  rw [(hN x).2]
  exact hL x

end Randomized
