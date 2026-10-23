/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.BiasedCoin
import TCSlib.Complexity.ClassP.BinaryArith.Loops
import TCSlib.Complexity.CircuitComplexity.UHalt
import Mathlib.Analysis.SpecificLimits.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# An uncomputable coin decides an undecidable language

[AB09, Exercise 7.5]: [AB09, Lemma 7.12] needs `ρ` to be efficiently computable. Here `ρ` has base-4
digits `h₀ h₁ h₂ … ∈ {0, 1}`, `hⱼ = 1` iff `j ∈ Nat.Partrec.Code.haltingSet`. Then
`4^J ρ = A_J + τ` with `A_J = ∑_{j<J} hⱼ 4^{J-1-j} ∈ ℕ` and `τ ∈ [0, 1/3]`, so an estimate of
`ρ` within `1/(4·4^J)` reads `A_J` and `h_{J-1}` off. The language is
`L = {1^N 0 y : J = ⌊log₄|y|⌋ ≥ 1, N = A_{J-1}, h_{J-1} = 1}`: the input carries the unary
padding `y` that pays for the `32(n+1)² ≥ 32·16^J` coins of the estimate. A polynomial-time
verifier counting the `1`s among `32(n+1)²` `ρ`-coins decides `L` with error `< 1/3`, so
`L ∈ biasedBPP ρ`, while `L` is not computable: `A_j` and then `h_j` would be computable by
recursion on `j`.

## Main definitions

* `Randomized.haltDigit`, `Randomized.haltCoin` — the digits and the real `ρ`.
* `Randomized.haltLang` — the language; `Randomized.haltCoinVerifier` — the verifier.

## Main results

* `Randomized.not_computablePred_haltLang` — `L` is undecidable.
* `Randomized.haltLang_mem_biasedBPP` — `L ∈ biasedBPP ρ`.
* `Randomized.exists_biasedBPP_not_computablePred` — [AB09, Exercise 7.5].

## Divergences

* Undecidability is Mathlib's `ComputablePred` (no partial recursive decision procedure).
* The book leaves the language open; ours is a padded, prefix-checked form of the halting set
  (the padding is what makes `poly(n)` coins enough to read the needed digit).
* The machine is obtained from a polynomial-time verifier (`mem_biasedBPP_of_eff`); the time
  bound is that of [AB09, Def 7.2], with all `ρ`-coins drawn from the same coin.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Finset Complexity Turing
open scoped NNReal

/-! ### The halting coin -/

/-- The halting digits: `haltDigit j` iff `j ∈ Nat.Partrec.Code.haltingSet`, i.e. the code
numbered `j.unpair.1` halts on input `j.unpair.2`. -/
def haltDigit (j : ℕ) : Prop := j ∈ Nat.Partrec.Code.haltingSet

/-- The halting digits are not computable (the halting problem). -/
theorem not_computablePred_haltDigit : ¬ ComputablePred haltDigit :=
  Nat.Partrec.Code.not_computablePred_mem_haltingSet

open Classical in
/-- The `j`-th digit as a number in `{0, 1}`. -/
noncomputable def haltBit (j : ℕ) : ℕ := if haltDigit j then 1 else 0

/-- A digit is `0` or `1`. -/
theorem haltBit_le_one (j : ℕ) : haltBit j ≤ 1 := by
  unfold haltBit; split_ifs <;> norm_num

/-- The halting coin `ρ = ∑ⱼ hⱼ 4^{-(j+1)}`. [AB09, Exercise 7.5] -/
noncomputable def haltCoin : ℝ := ∑' j : ℕ, (haltBit j : ℝ) * (1 / 4) ^ (j + 1)

/-- The integer part `A_J = ∑_{j<J} hⱼ 4^{J-1-j}` of `4^J ρ`, by `A_{J+1} = 4A_J + h_J`. -/
noncomputable def haltPrefix : ℕ → ℕ
  | 0 => 0
  | J + 1 => 4 * haltPrefix J + haltBit J

/-- The terms of `haltCoin` are summable, from any offset. -/
theorem summable_haltCoin (J : ℕ) :
    Summable fun j : ℕ => (haltBit (j + J) : ℝ) * (1 / 4) ^ (j + 1) := by
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 4 : ℝ) < 1)).mul_left
      (1 / 4))
  have : (haltBit (j + J) : ℝ) ≤ 1 := by exact_mod_cast haltBit_le_one _
  rw [pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 4) j]

/-- **The digits of `ρ`**: `4^J ρ = A_J + τ` with `0 ≤ τ ≤ 1/3`.

**Proof sketch.** Split the series after `J` terms. The head, times `4^J`, is `A_J` (induction
on `J`); the tail, times `4^J`, is `∑ⱼ h_{j+J} 4^{-(j+1)} ∈ [0, ∑ⱼ 4^{-(j+1)}] = [0, 1/3]`. -/
theorem haltCoin_mul_pow (J : ℕ) :
    ∃ τ : ℝ, haltCoin * 4 ^ J = haltPrefix J + τ ∧ 0 ≤ τ ∧ τ ≤ 1 / 3 := by
  have hhead : ∀ J, (haltPrefix J : ℝ) =
      4 ^ J * ∑ j ∈ range J, (haltBit j : ℝ) * (1 / 4) ^ (j + 1) := by
    intro J
    induction J with
    | zero => simp [haltPrefix]
    | succ J ih =>
      have h4 : (4 : ℝ) ^ (J + 1) * (1 / 4) ^ (J + 1) = 1 := by rw [← mul_pow]; norm_num
      rw [haltPrefix, sum_range_succ]
      push_cast
      rw [ih]
      linear_combination (-(haltBit J : ℝ)) * h4
  have hs0 : Summable fun j : ℕ => (haltBit j : ℝ) * (1 / 4) ^ (j + 1) := by
    simpa using summable_haltCoin 0
  set τ := ∑' j : ℕ, (haltBit (j + J) : ℝ) * (1 / 4) ^ (j + 1)
  refine ⟨τ, ?_, tsum_nonneg fun j => by positivity, ?_⟩
  · have hsplit := (Summable.sum_add_tsum_nat_add J hs0).symm
    have h4 : (4 : ℝ) ^ J * (1 / 4) ^ J = 1 := by rw [← mul_pow]; norm_num
    rw [haltCoin, hsplit, hhead, add_mul, mul_comm]
    congr 1
    rw [mul_comm, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [show j + J + 1 = (j + 1) + J by ring, pow_add]
    linear_combination ((haltBit (j + J) : ℝ) * (1 / 4) ^ (j + 1)) * h4
  · have hg : Summable fun j : ℕ => (1 / 4 : ℝ) ^ (j + 1) :=
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 4 : ℝ) < 1)).mul_left
        (1 / 4)).congr fun j => by rw [pow_succ]; ring
    calc τ ≤ ∑' j : ℕ, (1 / 4 : ℝ) ^ (j + 1) :=
          (summable_haltCoin J).tsum_le_tsum (fun j => by
            have : (haltBit (j + J) : ℝ) ≤ 1 := by exact_mod_cast haltBit_le_one _
            nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 4) (j + 1)]) hg
      _ = 1 / 3 := by
          rw [show (fun j : ℕ => (1 / 4 : ℝ) ^ (j + 1)) = fun j => 1 / 4 * (1 / 4) ^ j from
            funext fun j => by ring, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num)
            (by norm_num)]
          norm_num

/-- `0 ≤ ρ ≤ 1/3`. -/
theorem haltCoin_mem : 0 ≤ haltCoin ∧ haltCoin ≤ 1 / 3 := by
  obtain ⟨τ, h, h0, h1⟩ := haltCoin_mul_pow 0
  simp [haltPrefix] at h
  exact ⟨h ▸ h0, h ▸ h1⟩

/-! ### The language -/

/-- The unary number `N` of an input `1^N 0 y`. -/
def hlN (x : List Bool) : ℕ := (BinArith.uHead x).length

/-- The precision exponent `J = ⌊log₄ |y|⌋` of an input `1^N 0 y`. -/
def hlJ (x : List Bool) : ℕ := Nat.log 4 (BinArith.uRest x).length

/-- [AB09, Exercise 7.5]: the inputs `1^N 0 y` with `J = ⌊log₄|y|⌋ ≥ 1`, `N = A_{J-1}` and
`h_{J-1} = 1`. -/
def haltLang : Language Bool :=
  {x | 1 ≤ hlJ x ∧ hlN x = haltPrefix (hlJ x - 1) ∧ haltDigit (hlJ x - 1)}

/-- **Where `4^J ρ` lies**: on members `4^J ρ ∈ [4N + 1, 4N + 4/3]`; on non-members
`4^J ρ ≤ 4N + 1/3` or `4^J ρ ≥ 4N + 4`.

**Proof sketch.** `4^J ρ = A_J + τ` with `τ ∈ [0, 1/3]` (`haltCoin_mul_pow`). For `J = 0`,
`4^0 ρ = τ ≤ 1/3`. For `J = j + 1`, `A_J = 4A_j + h_j`: members have `N = A_j`, `h_j = 1`, so
`A_J = 4N + 1`; for non-members, `N < A_j` gives `A_J ≥ 4N + 4`, while `N > A_j`, or `N = A_j`
with `h_j = 0`, gives `A_J ≤ 4N` (`A_J ≤ 4N - 3` in the first case). -/
theorem haltCoin_mul_pow_hlJ (x : List Bool) :
    (x ∈ haltLang → 4 * hlN x + 1 ≤ haltCoin * 4 ^ hlJ x ∧
      haltCoin * 4 ^ hlJ x ≤ 4 * hlN x + 4 / 3) ∧
    (x ∉ haltLang → haltCoin * 4 ^ hlJ x ≤ 4 * hlN x + 1 / 3 ∨
      4 * hlN x + 4 ≤ haltCoin * 4 ^ hlJ x) := by
  obtain ⟨τ, hτ, h0, h1⟩ := haltCoin_mul_pow (hlJ x)
  rw [hτ]
  have hN : (0 : ℝ) ≤ hlN x := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos (hlJ x) with hJ | hJ
  · have hx : x ∉ haltLang := fun h => by have := h.1; omega
    refine ⟨fun h => absurd h hx, fun _ => Or.inl ?_⟩
    rw [hJ, haltPrefix]; push_cast; linarith
  obtain ⟨j, hj⟩ : ∃ j, hlJ x = j + 1 := ⟨hlJ x - 1, by omega⟩
  have hb : (haltBit j : ℝ) ≤ 1 := by exact_mod_cast haltBit_le_one j
  have hmem : x ∈ haltLang ↔ hlN x = haltPrefix j ∧ haltDigit j := by
    show 1 ≤ hlJ x ∧ hlN x = haltPrefix (hlJ x - 1) ∧ haltDigit (hlJ x - 1) ↔ _
    rw [hj]
    simp
  rw [hmem, hj, haltPrefix]
  push_cast
  refine ⟨fun ⟨hA, hd⟩ => ?_, fun hx => ?_⟩
  · have : haltBit j = 1 := by simp [haltBit, hd]
    rw [hA, this]; push_cast; constructor <;> linarith
  · rcases lt_trichotomy (hlN x) (haltPrefix j) with hlt | heq | hgt
    · right
      have : (hlN x : ℝ) + 1 ≤ haltPrefix j := by exact_mod_cast hlt
      linarith
    · left
      have : haltBit j = 0 := by
        by_contra h
        exact hx ⟨heq, by by_contra hd; simp [haltBit, hd] at h⟩
      rw [heq, this]; push_cast; linarith
    · left
      have : (haltPrefix j : ℝ) + 1 ≤ hlN x := by exact_mod_cast hgt
      linarith

/-! ### Undecidability -/

/-- The input `1^N 0 1^{4^{j+1}}` asking whether `N = A_j` and `h_j = 1`. -/
def hlQuery (N j : ℕ) : List Bool :=
  List.replicate N true ++ false :: List.replicate (4 ^ (j + 1)) true

/-- The query reads back as `N` and `J = j + 1`. -/
theorem hlN_hlQuery (N j : ℕ) : hlN (hlQuery N j) = N ∧ hlJ (hlQuery N j) = j + 1 := by
  have h := BinArith.uHead_encodeNat N (List.replicate (4 ^ (j + 1)) true)
  have h' := BinArith.uRest_encodeNat N (List.replicate (4 ^ (j + 1)) true)
  have he : BoolCircuit.encodeNat N ++ List.replicate (4 ^ (j + 1)) true = hlQuery N j := by
    simp [BoolCircuit.encodeNat, hlQuery]
  rw [he] at h h'
  refine ⟨by simp [hlN, h], ?_⟩
  simp only [hlJ, h', List.length_replicate]
  exact Nat.log_pow (by norm_num) _

/-- On the query with `N = A_j`, membership is the digit `h_j`. -/
theorem hlQuery_mem_iff (j : ℕ) : hlQuery (haltPrefix j) j ∈ haltLang ↔ haltDigit j := by
  obtain ⟨h1, h2⟩ := hlN_hlQuery (haltPrefix j) j
  show 1 ≤ hlJ _ ∧ hlN _ = haltPrefix (hlJ _ - 1) ∧ haltDigit (hlJ _ - 1) ↔ _
  rw [h1, h2]
  simp

/-- **[AB09, Exercise 7.5], undecidability**: `L` is not computable.

**Proof sketch.** From a decision procedure for `L`, compute `A_j` by the recursion
`A_{j+1} = 4A_j + [hlQuery A_j j ∈ L]` (`Computable.nat_rec`), and then `h_j` as
`[hlQuery A_j j ∈ L]` (`hlQuery_mem_iff`): the halting digits would be computable. -/
theorem not_computablePred_haltLang : ¬ ComputablePred (· ∈ haltLang) := by
  rintro ⟨D, hD⟩
  have hrep : Computable fun n : ℕ => List.replicate n true := by
    refine (Computable.nat_rec (g := fun _ => ([] : List Bool))
      (h := fun _ p => true :: p.2) Computable.id (Computable.const [])
      (Computable.list_cons.comp (Computable.const true)
        (Computable.snd.comp Computable.snd)).to₂).of_eq fun n => ?_
    induction n with
    | zero => rfl
    | succ n ih =>
      calc _ = true :: List.replicate n true := by rw [← ih]; rfl
        _ = _ := rfl
  have hpow : Computable fun j : ℕ => 4 ^ (j + 1) := by
    refine (Computable.nat_rec (g := fun _ => 4) (h := fun _ p => 4 * p.2) Computable.id
      (Computable.const 4) (Primrec.nat_mul.to_comp.comp (Computable.const 4)
        (Computable.snd.comp Computable.snd)).to₂).of_eq fun n => ?_
    induction n with
    | zero => rfl
    | succ n ih =>
      calc _ = 4 * 4 ^ (n + 1) := by rw [← ih]; rfl
        _ = _ := by ring
  have hq : Computable₂ hlQuery :=
    Primrec.list_append.to_comp.comp (hrep.comp Computable.fst)
      (Computable.list_cons.comp (Computable.const false)
        (hrep.comp (hpow.comp Computable.snd)))
  let s : ℕ × ℕ → ℕ := fun p => 4 * p.2 + cond (decide (hlQuery p.2 p.1 ∈ haltLang)) 1 0
  have hs : Computable s :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const 4) Computable.snd)
      (Computable.cond (hD.comp (hq.comp Computable.snd Computable.fst))
        (Computable.const 1) (Computable.const 0))
  have hA : Computable haltPrefix := by
    refine (Computable.nat_rec (g := fun _ => 0) (h := fun _ p => s p) Computable.id
      (Computable.const 0) (hs.comp Computable.snd).to₂).of_eq fun n => ?_
    induction n with
    | zero => rfl
    | succ n ih =>
      calc _ = s (n, haltPrefix n) := by rw [← ih]; rfl
        _ = haltPrefix (n + 1) := by
          show 4 * haltPrefix n + _ = 4 * haltPrefix n + haltBit n
          congr 1
          by_cases h : haltDigit n
          · have := (hlQuery_mem_iff n).mpr h
            simp [haltBit, h, this]
          · have := mt (hlQuery_mem_iff n).mp h
            simp [haltBit, h, this]
  exact not_computablePred_haltDigit (ComputablePred.of_eq
    ⟨fun j => D _, hD.comp (hq.comp hA Computable.id)⟩ hlQuery_mem_iff)

/-! ### The verifier -/

/-- The precision `D = 4^J` of an input. -/
def hlD (x : List Bool) : ℕ := 4 ^ hlJ x

/-- [AB09, Exercise 7.5]: with `c` ones among the `k` coins `r`, accept iff
`(c/k)·D ∈ (4N + 2/3, 4N + 2)`, i.e. `k(12N + 2) < 3cD` and `cD < k(4N + 2)`. -/
def haltCoinVerifier (x r : List Bool) : Bool :=
  decide (r.length * (12 * hlN x + 2) < r.count true * (hlD x * 3)) &&
    decide (r.count true * hlD x < r.length * (4 * hlN x + 2))

/-- **The verifier is right on a good estimate**: if `k > 0` and the fraction of ones is within
`1/(4D)` of `ρ`, the verifier answers `x ∈ L`.

**Proof sketch.** The estimate `e = (c/k)·D` is within `1/4` of `Dρ`. On members `Dρ ∈
[4N + 1, 4N + 4/3]`, so `e ∈ (4N + 2/3, 4N + 2)`; on non-members `Dρ ≤ 4N + 1/3` or
`Dρ ≥ 4N + 4` (`haltCoin_mul_pow_hlJ`), so `e` is outside. -/
theorem haltCoinVerifier_eq {x r : List Bool} (hk : 0 < r.length)
    (he : |(r.count true : ℝ) / r.length - haltCoin| ≤ 1 / (4 * hlD x)) :
    haltCoinVerifier x r = MultiTapeTM.indicator (haltLang : Set (List Bool)) x := by
  have hk0 : (0 : ℝ) < r.length := by exact_mod_cast hk
  have hD0 : (0 : ℝ) < hlD x := by unfold hlD; positivity
  have hρ : haltCoin * (hlD x : ℝ) = haltCoin * 4 ^ hlJ x := by simp [hlD]
  have hest : |(r.count true : ℝ) * hlD x / r.length - haltCoin * hlD x| ≤ 1 / 4 := by
    have : (r.count true : ℝ) * hlD x / r.length - haltCoin * hlD x =
        ((r.count true : ℝ) / r.length - haltCoin) * hlD x := by ring
    rw [this, abs_mul, abs_of_pos hD0]
    calc |(r.count true : ℝ) / r.length - haltCoin| * hlD x ≤ 1 / (4 * hlD x) * hlD x :=
          mul_le_mul_of_nonneg_right he hD0.le
      _ = 1 / 4 := by field_simp
  generalize hE : (r.count true : ℝ) * hlD x / r.length = e at hest
  rw [abs_le] at hest
  have t1 : (r.length * (12 * hlN x + 2) < r.count true * (hlD x * 3)) ↔
      4 * (hlN x : ℝ) + 2 / 3 < e := by
    rw [← hE, lt_div_iff₀ hk0, ← @Nat.cast_lt ℝ]
    push_cast
    constructor <;> intro h <;> linarith
  have t2 : (r.count true * hlD x < r.length * (4 * hlN x + 2)) ↔ e < 4 * (hlN x : ℝ) + 2 := by
    rw [← hE, div_lt_iff₀ hk0, ← @Nat.cast_lt ℝ]
    push_cast
    constructor <;> intro h <;> linarith
  obtain ⟨hmem, hnot⟩ := haltCoin_mul_pow_hlJ x
  rw [← hρ] at hmem hnot
  by_cases hx : x ∈ haltLang
  · obtain ⟨h1, h2⟩ := hmem hx
    rw [show MultiTapeTM.indicator (haltLang : Set (List Bool)) x = true from
      indicator_eq_true_iff.mpr hx, haltCoinVerifier, Bool.and_eq_true, decide_eq_true_iff,
      decide_eq_true_iff, t1, t2]
    constructor <;> linarith
  · rw [show MultiTapeTM.indicator (haltLang : Set (List Bool)) x = false from
      indicator_eq_false_iff.mpr hx, haltCoinVerifier, Bool.and_eq_false_iff,
      decide_eq_false_iff_not, decide_eq_false_iff_not, t1, t2]
    rcases hnot hx with h | h
    · left; linarith
    · right; linarith

/-- The precision is at most `|x| + 1`. -/
theorem hlD_le (x : List Bool) : hlD x ≤ x.length + 1 := by
  have hr := BinArith.length_uRest_le x
  rcases Nat.eq_zero_or_pos (BinArith.uRest x).length with h | h
  · simp [hlD, hlJ, h]
  · have := Nat.pow_log_le_self 4 h.ne'
    simp only [hlD, hlJ]; omega

/-- **The verifier errs with probability `< 1/3`** over `32(n+1)²` `ρ`-coins.

**Proof sketch.** With `k = 32(n+1)² ≥ 32D²` coins, Hoeffding (`biasedProb_count_dev_le`) bounds
the probability that the fraction of ones is more than `1/(4D)` from `ρ` by
`2e^{-2k/(16D²)} ≤ 2e^{-4} < 1/3`; otherwise the verifier is right (`haltCoinVerifier_eq`). -/
theorem haltCoinVerifier_prob (x : List Bool) :
    2 / 3 ≤ biasedProb haltCoin (polyLen 32 2 x.length)
      fun u => haltCoinVerifier x u = MultiTapeTM.indicator (haltLang : Set (List Bool)) x := by
  obtain ⟨h0, h1⟩ := haltCoin_mem
  have hk : 0 < polyLen 32 2 x.length := by unfold polyLen; positivity
  have hkR : ((polyLen 32 2 x.length : ℕ) : ℝ) = 32 * ((x.length : ℝ) + 1) ^ 2 := by
    unfold polyLen; push_cast; ring
  have hD0 : (0 : ℝ) < hlD x := by unfold hlD; positivity
  have hDx : (hlD x : ℝ) ≤ x.length + 1 := by exact_mod_cast hlD_le x
  have hp : (⟨haltCoin, h0⟩ : ℝ≥0) ≤ 1 := by
    rw [← NNReal.coe_le_coe, NNReal.coe_mk, NNReal.coe_one]; linarith
  have hbad := biasedProb_count_dev_le hp hk (δ := 1 / (4 * hlD x)) (by positivity)
  simp only [NNReal.coe_mk] at hbad
  have hexp : 2 * Real.exp (-2 * (1 / (4 * (hlD x : ℝ))) ^ 2 *
      ((polyLen 32 2 x.length : ℕ) : ℝ)) ≤ 1 / 3 := by
    have h2 : -2 * (1 / (4 * (hlD x : ℝ))) ^ 2 * ((polyLen 32 2 x.length : ℕ) : ℝ) ≤ -4 := by
      rw [hkR]
      have hsq : (hlD x : ℝ) ^ 2 ≤ ((x.length : ℝ) + 1) ^ 2 := pow_le_pow_left₀ hD0.le hDx 2
      have hr : -2 * (1 / (4 * (hlD x : ℝ))) ^ 2 * (32 * ((x.length : ℝ) + 1) ^ 2) =
          -4 * (((x.length : ℝ) + 1) ^ 2 / (hlD x : ℝ) ^ 2) := by field_simp; ring
      have h1 : 1 ≤ ((x.length : ℝ) + 1) ^ 2 / (hlD x : ℝ) ^ 2 := by
        rw [le_div_iff₀ (by positivity)]; linarith
      rw [hr]; linarith
    have h6 : (6 : ℝ) ≤ Real.exp 4 := by
      have := Real.add_one_le_exp 2
      rw [show (4 : ℝ) = 2 + 2 by norm_num, Real.exp_add]
      nlinarith
    have he : Real.exp (-4) ≤ 1 / 6 :=
      calc Real.exp (-4) = (Real.exp 4)⁻¹ := Real.exp_neg 4
        _ ≤ (6 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h6
        _ = 1 / 6 := by norm_num
    linarith [Real.exp_le_exp.mpr h2]
  have hgood : 2 / 3 ≤ biasedProb haltCoin (polyLen 32 2 x.length) (fun w =>
      ¬ (1 / (4 * (hlD x : ℝ)) <
        |(w.count true : ℝ) / (polyLen 32 2 x.length : ℕ) - haltCoin|)) := by
    rw [biasedProb_not]; linarith
  refine hgood.trans (biasedProb_mono h0 (by linarith) fun w hw hgw => ?_)
  rw [not_lt] at hgw
  exact haltCoinVerifier_eq (by omega) (by rw [hw]; exact hgw)

/-! ### The verifier in polynomial time -/

/-- The length test `|snd z| ≤ |fst z|`. -/
def lenLeB (z : List Bool) : Bool := decide ((pairSndD z).length ≤ (pairFstD z).length)

/-- One round of the power-of-`4` loop on `⟨m, d⟩`: replace `d` by `dddd` if that is no longer
than `m`. -/
def pow4Step (z : List Bool) : List Bool :=
  pairEncode (pairFstD z)
    (if lenLeB (pairEncode (pairFstD z) (pairSndD z ++ pairSndD z ++ pairSndD z ++ pairSndD z))
      then pairSndD z ++ pairSndD z ++ pairSndD z ++ pairSndD z else pairSndD z)

/-- The rounds of the power-of-`4` loop: after `t` rounds `|d| = 4^{min(t, ⌊log₄|m|⌋)}`.

**Proof sketch.** Induction on `t`, with `J = ⌊log₄|m|⌋`: the round quadruples `d` iff
`4 · 4^{min(t, J)} ≤ |m|`, iff `t < J` (`Nat.le_log_iff_pow_le`), and then
`min(t + 1, J) = min(t, J) + 1`; otherwise `min(t + 1, J) = min(t, J) = J`. -/
theorem iterate_pow4Step (m : List Bool) (t : ℕ) : ∃ w : List Bool,
    pow4Step^[t] (pairEncode m [true]) = pairEncode m w ∧
      w.length = 4 ^ min t (Nat.log 4 m.length) := by
  induction t with
  | zero => exact ⟨[true], rfl, by simp⟩
  | succ t ih =>
    obtain ⟨w, hw, hl⟩ := ih
    rw [Function.iterate_succ_apply', hw]
    have hiff : 4 * 4 ^ min t (Nat.log 4 m.length) ≤ m.length ↔ t < Nat.log 4 m.length := by
      rcases Nat.eq_zero_or_pos m.length with h | h
      · simp [h]
      · rw [← pow_succ', ← Nat.le_log_iff_pow_le (by norm_num) h.ne']
        omega
    by_cases ht : t < Nat.log 4 m.length
    · have h4 := hiff.mpr ht
      refine ⟨w ++ w ++ w ++ w, ?_, ?_⟩
      · have hc : lenLeB (pairEncode m (w ++ w ++ w ++ w)) = true := by
          simp only [lenLeB, pairFstD_pairEncode, pairSndD_pairEncode, List.length_append, hl,
            decide_eq_true_iff]
          omega
        simp only [pow4Step, pairFstD_pairEncode, pairSndD_pairEncode, hc, if_true]
      · simp only [List.length_append, hl, show min (t + 1) (Nat.log 4 m.length) =
          min t (Nat.log 4 m.length) + 1 by omega, pow_succ]
        ring
    · have h4 := mt hiff.mp ht
      refine ⟨w, ?_, ?_⟩
      · have hc : lenLeB (pairEncode m (w ++ w ++ w ++ w)) = false := by
          simp only [lenLeB, pairFstD_pairEncode, pairSndD_pairEncode, List.length_append, hl,
            decide_eq_false_iff_not]
          omega
        simp only [pow4Step, pairFstD_pairEncode, pairSndD_pairEncode, hc]
        rfl
      · rw [hl]; congr 1; omega

/-- The word of length `D = 4^J` computed from `x`. -/
def hlDWord (x : List Bool) : List Bool :=
  pairSndD (pairSndD (BinArith.forLoop pow4Step
    (pairEncode (BinArith.uRest x) (pairEncode (BinArith.uRest x) [true]))))

/-- `|hlDWord x| = D`. -/
theorem length_hlDWord (x : List Bool) : (hlDWord x).length = hlD x := by
  obtain ⟨w, hw, hl⟩ := iterate_pow4Step (BinArith.uRest x) (BinArith.uRest x).length
  simp only [hlDWord, BinArith.forLoop_pairEncode, pairSndD_pairEncode, hw, hl, hlD, hlJ]
  rw [min_eq_right (Nat.log_le_self _ _)]

/-- The ones of a word. -/
def onesW (w : List Bool) : List Bool :=
  transduce (σ := Unit) (fun _ _ => ()) (fun _ b => if b then some true else none) () w

/-- `|onesW w|` is the number of ones of `w`. -/
theorem length_onesW (w : List Bool) : (onesW w).length = w.count true := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [onesW, transduce] at ih ⊢
    cases b <;> simp [ih]

/-- `|r| · (nN + 2)` in unary on `⟨x, r⟩`, with `N = |uHead x|`. -/
def hcLin (n : ℕ) (z : List Bool) : List Bool :=
  BinArith.mulU (pairEncode (pairSndD z)
    (BinArith.mulU (pairEncode (List.replicate n true) (BinArith.uHead (pairFstD z))) ++
      [true, true]))

/-- `c · D` in unary on `⟨x, r⟩`, with `c` the number of ones of `r`. -/
def hcCD (z : List Bool) : List Bool :=
  BinArith.mulU (pairEncode (onesW (pairSndD z)) (hlDWord (pairFstD z)))

/-- `c · 3D` in unary on `⟨x, r⟩`. -/
def hcCD3 (z : List Bool) : List Bool :=
  BinArith.mulU (pairEncode (onesW (pairSndD z))
    (BinArith.mulU (pairEncode (hlDWord (pairFstD z)) [true, true, true])))

/-- The verifier on `⟨x, r⟩`, from unary arithmetic: products by `mulU`, comparisons of lengths
by `lenLeB`. -/
def haltCoinTest (z : List Bool) : Bool :=
  !lenLeB (pairEncode (hcLin 12 z) (hcCD3 z)) && !lenLeB (pairEncode (hcCD z) (hcLin 4 z))

/-- The test computes the verifier. -/
theorem haltCoinTest_pairEncode (x r : List Bool) :
    haltCoinTest (pairEncode x r) = haltCoinVerifier x r := by
  simp only [haltCoinTest, hcLin, hcCD, hcCD3, haltCoinVerifier, lenLeB, pairFstD_pairEncode,
    pairSndD_pairEncode, BinArith.length_mulU, List.length_append, List.length_replicate,
    length_onesW, length_hlDWord, hlN, List.length_cons, List.length_nil, ← decide_not,
    Nat.not_le]

/-- A round of the power-of-`4` loop is polynomial-time. -/
theorem polyTimeComputable_pow4Step : PolyTimeComputable pow4Step := by
  have hx : PolyTimeComputable pairFstD := polyTimeComputable_pairFstD
  have hr : PolyTimeComputable pairSndD := polyTimeComputable_pairSndD
  have hquad : PolyTimeComputable fun z => pairSndD z ++ pairSndD z ++ pairSndD z ++ pairSndD z :=
    ((hr.append hr).append hr).append hr
  have ht : PolyTimeComputable fun z =>
      [lenLeB (pairEncode (pairFstD z) (pairSndD z ++ pairSndD z ++ pairSndD z ++ pairSndD z))] :=
    polyTimeComputable_lenLe.comp (hx.pairEncode hquad)
  exact hx.pairEncode (polyTimeComputable_ite ht hquad hr)

/-- The word of length `D` is computed in polynomial time.

**Proof sketch.** The counted loop `BinArith.forLoop` of `pow4Step` keeps its context `m`, and a
round replaces `d` by `dddd` only when that is no longer than `m`, so it adds at most `|m|`
letters (`forLoop_bound_of_ctx`). -/
theorem polyTimeComputable_hlDWord : PolyTimeComputable fun z => hlDWord (pairFstD z) := by
  have hloop := BinArith.polyTimeComputable_forLoop polyTimeComputable_pow4Step _ _
    (BinArith.forLoop_bound_of_ctx 2 (fun d => by simp only [pow4Step, pairFstD_pairEncode])
      fun d => by
        have h1 := length_pair_components_le d
        have h2 : (pow4Step d).length ≤ 2 * (pairFstD d).length + 2 + ((pairSndD d).length +
            (pairFstD d).length) := by
          unfold pow4Step
          rw [length_pairEncode]
          split_ifs with h
          · simp only [lenLeB, pairFstD_pairEncode, pairSndD_pairEncode, decide_eq_true_eq] at h
            omega
          · omega
        omega)
  have hu : PolyTimeComputable fun z => BinArith.uRest (pairFstD z) :=
    BinArith.polyTimeComputable_uRest.comp polyTimeComputable_pairFstD
  exact BinArith.polyTimeComputable_slot3.comp
    (hloop.comp (hu.pairEncode (hu.pairEncode (polyTimeComputable_const [true]))))

/-- The unary products of the test are polynomial-time. -/
theorem polyTimeComputable_hcLin (n : ℕ) : PolyTimeComputable (hcLin n) := by
  have hN : PolyTimeComputable fun z => BinArith.uHead (pairFstD z) :=
    BinArith.polyTimeComputable_app BinArith.polyTimeComputable_uHead polyTimeComputable_pairFstD
  have hm : PolyTimeComputable fun z =>
      BinArith.mulU (pairEncode (List.replicate n true) (BinArith.uHead (pairFstD z))) :=
    BinArith.polyTimeComputable_app BinArith.polyTimeComputable_mulU
      ((polyTimeComputable_const _).pairEncode hN)
  have hp : PolyTimeComputable fun z => pairEncode (pairSndD z)
      (BinArith.mulU (pairEncode (List.replicate n true) (BinArith.uHead (pairFstD z))) ++
        [true, true]) :=
    polyTimeComputable_pairSndD.pairEncode (hm.append (polyTimeComputable_const _))
  unfold hcLin
  exact BinArith.polyTimeComputable_app BinArith.polyTimeComputable_mulU hp

/-- The ones of the coins, as a function of `⟨x, r⟩`, are polynomial-time. -/
theorem polyTimeComputable_onesW_snd : PolyTimeComputable fun z => onesW (pairSndD z) :=
  BinArith.polyTimeComputable_app (polyTimeComputable_transduce _ _ _) polyTimeComputable_pairSndD

/-- `c · D` is polynomial-time. -/
theorem polyTimeComputable_hcCD : PolyTimeComputable hcCD := by
  have hp : PolyTimeComputable fun z => pairEncode (onesW (pairSndD z)) (hlDWord (pairFstD z)) :=
    polyTimeComputable_onesW_snd.pairEncode polyTimeComputable_hlDWord
  unfold hcCD
  exact BinArith.polyTimeComputable_app BinArith.polyTimeComputable_mulU hp

/-- `c · 3D` is polynomial-time. -/
theorem polyTimeComputable_hcCD3 : PolyTimeComputable hcCD3 := by
  have h3 : PolyTimeComputable fun z =>
      BinArith.mulU (pairEncode (hlDWord (pairFstD z)) [true, true, true]) :=
    BinArith.polyTimeComputable_app BinArith.polyTimeComputable_mulU
      (polyTimeComputable_hlDWord.pairEncode (polyTimeComputable_const _))
  have hp : PolyTimeComputable fun z => pairEncode (onesW (pairSndD z))
      (BinArith.mulU (pairEncode (hlDWord (pairFstD z)) [true, true, true])) :=
    polyTimeComputable_onesW_snd.pairEncode h3
  unfold hcCD3
  exact BinArith.polyTimeComputable_app BinArith.polyTimeComputable_mulU hp

/-- The test is polynomial-time: unary products, length tests and Boolean connectives. -/
theorem polyTimeComputable_haltCoinTest : PolyTimeComputable fun z => [haltCoinTest z] := by
  have t1 : PolyTimeComputable fun z => [lenLeB (pairEncode (hcLin 12 z) (hcCD3 z))] :=
    BinArith.polyTimeComputable_test_app (p := lenLeB) polyTimeComputable_lenLe
      ((polyTimeComputable_hcLin 12).pairEncode polyTimeComputable_hcCD3)
  have t2 : PolyTimeComputable fun z => [lenLeB (pairEncode (hcCD z) (hcLin 4 z))] :=
    BinArith.polyTimeComputable_test_app (p := lenLeB) polyTimeComputable_lenLe
      (polyTimeComputable_hcCD.pairEncode (polyTimeComputable_hcLin 4))
  exact polyTimeComputable_and (polyTimeComputable_not t1) (polyTimeComputable_not t2)

/-- The verifier is polynomial-time. -/
theorem eff_haltCoinVerifier : polyTimeModel.Eff (boolVerifier haltCoinVerifier) :=
  eff_boolVerifier_of_test polyTimeComputable_haltCoinTest haltCoinTest_pairEncode

/-! ### Exercise 7.5 -/

/-- `L` is decided with bounded error in polynomial time with a `ρ`-coin. -/
theorem haltLang_mem_biasedBPP : haltLang ∈ biasedBPP haltCoin :=
  mem_biasedBPP_of_eff eff_haltCoinVerifier haltCoinVerifier_prob

/-- **[AB09, Exercise 7.5]**: there is a real `ρ ∈ [0, 1]` such that a polynomial-time PTM with
a `ρ`-coin decides an undecidable language with bounded error. -/
theorem exists_biasedBPP_not_computablePred : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ ≤ 1 ∧ ∃ L : Language Bool,
    ¬ ComputablePred (· ∈ L) ∧ L ∈ biasedBPP ρ :=
  ⟨haltCoin, haltCoin_mem.1, haltCoin_mem.2.trans (by norm_num), haltLang,
    not_computablePred_haltLang, haltLang_mem_biasedBPP⟩

end Randomized
