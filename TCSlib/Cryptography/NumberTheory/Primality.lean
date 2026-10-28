/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.NumberTheory.Chebyshev
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Complexity.Randomized.Closure
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Analysis.Complex.Exponential

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Primality testing and sampling a random prime

The Miller–Rabin test [PS10, §2.6.5] and the prime sampler [PS10, §2.6.6]:

* the set `L_N` of Miller–Rabin *liars* [PS10, p. 49], in the corrected form: for `N` with
  `N − 1 = u · 2^j`, `u` odd, `α ∈ L_N` iff `α^{N−1} = 1` and none of the intermediate powers
  `α^{u 2^i}` (`i < j`) is a non-trivial square root of `1`;
* the `t`-round test `millerRabin N t` [PS10, Algorithm 49.13] on bases `α ∈ [1, N−1]`;
* [PS10, Lemma 50.15]: for prime `N`, `L_N` is all of `Z_N \ {0}` (`|L_N| = N − 1`, proved);
  for odd composite `N`, `|L_N| ≤ (N−1)/2` (proved, the subgroup argument of [CLRS09]);
* [PS10, Theorem 49.14]: the test accepts every prime (proved) and rejects a composite
  except with probability `≤ 2^{−t}` (proved);
* `SamplePrime(n)` [PS10, Algorithm 50.16] as a truncated rejection sampler: `T` uniform
  `n`-bit strings, the first prime one (`firstHit` of `Sampling.lean`), and
  [PS10, Lemma 51.17]: the output is uniform on `Π_n` conditioned on success (proved), the
  failure probability is `≤ (1 − 1/(2n))^T` (proved), `≤ e^{−n}` at `T = 2n²` (proved), and
  the sampler is a PPT given a polynomial-time primality test (proved; machine level).

**Deviation (source error):** the text defines `L_N` with "`N = u2^j`" and a condition on
`i = j` only, which is vacuous; the intended `N − 1 = u 2^j` and `∀ i < j` are used.
**Deviation:** the text draws `α ← Z_N`, which includes `α = 0 ∉ L_N` and would make the
test reject primes with positive probability; the test draws `α ∈ [1, N−1]` as in the
standard presentation, matching `|L_N| = N − 1`. Even `N > 2` are rejected outright (the text
handles only the base case `N = 2`). **Deviation:** [PS10, Theorem 49.14] says "with
probability `1 − 2^{−t}`" for "at least"; Lemma 50.15's composite case needs `N` odd.
**Deviation:** `SamplePrime` is truncated to `T` trials (strict PPT with failure `⊥`, D10)
and tests primality exactly (`Nat.Prime`); with Miller–Rabin in place of the exact test the
output would only be statistically close to uniform. §2.6.6 (p. 50) misquotes the prime
density as `1/n` (it is `1/(2n)`, Claim-33.1).

## Main definitions

* `TCSlib.Cryptography.NumberTheory.mrExp`, `TCSlib.Cryptography.NumberTheory.mrOdd` — the
  decomposition `N − 1 = u · 2^j`.
* `TCSlib.Cryptography.NumberTheory.MRLiar`, `TCSlib.Cryptography.NumberTheory.mrLiars` —
  the liar set `L_N` [PS10, Definition on p. 49, corrected].
* `TCSlib.Cryptography.NumberTheory.millerRabin` — the test [PS10, Algorithm 49.13].
* `TCSlib.Cryptography.NumberTheory.samplePrime` — `SamplePrime` [PS10, Algorithm 50.16].
* `TCSlib.Cryptography.NumberTheory.samplePrimeCoins`,
  `TCSlib.Cryptography.NumberTheory.chunk` — its coin polynomial and coin layout.

## Main results

* `TCSlib.Cryptography.NumberTheory.mrLiar_iff_of_prime`,
  `TCSlib.Cryptography.NumberTheory.card_mrLiars_of_prime` — `|L_N| = N − 1` for prime `N`
  [PS10, Lemma 50.15, first half].
* `TCSlib.Cryptography.NumberTheory.two_mul_card_mrLiars_le` — `|L_N| ≤ (N−1)/2` for odd
  composite `N` [PS10, Lemma 50.15, second half].
* `TCSlib.Cryptography.NumberTheory.millerRabin_of_prime`,
  `TCSlib.Cryptography.NumberTheory.uprob_millerRabin_le` — [PS10, Theorem 49.14].
* `TCSlib.Cryptography.NumberTheory.samplePrime_uniform_of_some`,
  `TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le`,
  `TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le_exp`,
  `TCSlib.Cryptography.NumberTheory.statClose_samplePrime`,
  `TCSlib.Cryptography.NumberTheory.exists_samplePrime_nuppt` — [PS10, Lemma 51.17].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.6.5: the set `L_N`, Algorithm 49.13, Theorem 49.14, Lemma 50.15; §2.6.6:
  Algorithm 50.16, Lemma 51.17.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer `uprob`).
* [CLRS09] T. H. Cormen, C. E. Leiserson, R. L. Rivest, C. Stein, *Introduction to
  Algorithms*, 3rd ed., MIT Press, 2009. (Theorem 31.38 and 31.39: the Miller–Rabin
  liar bound.)
-/

namespace TCSlib.Cryptography.NumberTheory

open Finset Complexity Turing

/-! ### The Miller–Rabin liar set -/

/-- The exponent `j` of the decomposition `N − 1 = u · 2^j` with `u` odd [PS10, p. 49]
(the `2`-adic valuation of `N − 1`). -/
def mrExp (N : ℕ) : ℕ := (N - 1).factorization 2

/-- The odd part `u` of the decomposition `N − 1 = u · 2^j` [PS10, p. 49]. -/
def mrOdd (N : ℕ) : ℕ := (N - 1) / 2 ^ mrExp N

/-- `2^j · u = N − 1`. -/
theorem two_pow_mrExp_mul_mrOdd (N : ℕ) : 2 ^ mrExp N * mrOdd N = N - 1 :=
  Nat.ordProj_mul_ordCompl_eq_self (N - 1) 2

/-- `u` is odd for `N ≥ 2`. -/
theorem mrOdd_odd {N : ℕ} (hN : 2 ≤ N) : Odd (mrOdd N) := by
  have h := Nat.not_dvd_ordCompl Nat.prime_two (show N - 1 ≠ 0 by omega)
  exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)

/-- `u · 2^j = N − 1`, so the last intermediate power is `α^{N−1}`. -/
theorem mrOdd_mul_two_pow (N : ℕ) : mrOdd N * 2 ^ mrExp N = N - 1 := by
  rw [mul_comm, two_pow_mrExp_mul_mrOdd]

/-- **The Miller–Rabin liar set `L_N`** [PS10, §2.6.5, p. 49, corrected]: with
`N − 1 = u · 2^j` (`u` odd), `α ∈ L_N` iff `α^{N−1} = 1` and for every `i < j`, if
`α^{u 2^{i+1}} = 1` then `α^{u 2^i} ∈ {1, −1}` — no intermediate power encountered by
repeated squaring is a non-trivial square root of `1`.

**Deviation (source error):** the text writes `N = u 2^j` and states the second condition
for `i = j` only (vacuous); this is the intended definition. -/
def MRLiar (N : ℕ) (α : ZMod N) : Prop :=
  α ^ (N - 1) = 1 ∧ ∀ i < mrExp N, α ^ (mrOdd N * 2 ^ (i + 1)) = 1 →
    α ^ (mrOdd N * 2 ^ i) = 1 ∨ α ^ (mrOdd N * 2 ^ i) = -1

instance (N : ℕ) : DecidablePred (MRLiar N) := fun _ => by
  unfold MRLiar
  infer_instance

/-- The liar set `L_N` as a finset of `Z_N` [PS10, p. 49]. -/
def mrLiars (N : ℕ) [NeZero N] : Finset (ZMod N) := univ.filter (MRLiar N)

/-- Unfolding of membership in `L_N`. -/
theorem mem_mrLiars {N : ℕ} [NeZero N] (α : ZMod N) : α ∈ mrLiars N ↔ MRLiar N α := by
  simp [mrLiars]

/-- A liar is nonzero (for `N ≥ 2`): `0^{N−1} = 0 ≠ 1`. -/
theorem MRLiar.ne_zero {N : ℕ} (hN : 2 ≤ N) {α : ZMod N} (h : MRLiar N α) : α ≠ 0 := by
  rintro rfl
  haveI : Fact (1 < N) := ⟨by omega⟩
  obtain ⟨h1, -⟩ := h
  rw [zero_pow (by omega)] at h1
  exact zero_ne_one h1

/-- **Primes have only liars** [PS10, Lemma 50.15, first half]: for prime `N`, `α ∈ L_N` iff
`α ≠ 0`.

**Proof sketch.** Fermat's little theorem gives `α^{N−1} = 1` for `α ≠ 0`
(`ZMod.pow_card_sub_one_eq_one`); in the field `Z_N`, `β² = 1` forces `β = ±1`
(`mul_self_eq_one_iff`), applied to `β = α^{u 2^i}` whose square is `α^{u 2^{i+1}}`.
Conversely `0 ∉ L_N`. -/
theorem mrLiar_iff_of_prime {N : ℕ} [hN : Fact N.Prime] (α : ZMod N) : MRLiar N α ↔ α ≠ 0 := by
  constructor
  · exact MRLiar.ne_zero hN.out.two_le
  · intro hα
    refine ⟨ZMod.pow_card_sub_one_eq_one hα, fun i _ h => ?_⟩
    have hsq : α ^ (mrOdd N * 2 ^ i) * α ^ (mrOdd N * 2 ^ i) = 1 := by
      rw [← pow_add, ← two_mul, mul_left_comm, ← pow_succ']
      exact h
    exact mul_self_eq_one_iff.1 hsq

/-- **`|L_N| = N − 1` for prime `N`** [PS10, Lemma 50.15, first half]. -/
theorem card_mrLiars_of_prime {N : ℕ} [Fact N.Prime] : (mrLiars N).card = N - 1 := by
  rw [mrLiars, Finset.filter_congr (fun α _ => mrLiar_iff_of_prime α), Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]

/-! #### The subgroup of liars ([CLRS09, Theorem 31.38]) -/

/-- A liar is a unit: `α^{N−1} = 1` with `N − 1 ≥ 1` (`IsUnit.of_pow_eq_one`). -/
private theorem mrLiar_isUnit {N : ℕ} (hN : 2 ≤ N) {α : ZMod N} (h : MRLiar N α) : IsUnit α :=
  IsUnit.of_pow_eq_one h.1 (by omega)

/-- `w^m = 1` in `(Z_N)^*` iff `w^m = 1` in `Z_N`. -/
private theorem units_pow_eq_one_iff {N m : ℕ} (w : (ZMod N)ˣ) :
    w ^ m = 1 ↔ (w : ZMod N) ^ m = 1 := by
  rw [← Units.val_inj, Units.val_pow_eq_pow_val, Units.val_one]

/-- `w^m = −1` in `(Z_N)^*` iff `w^m = −1` in `Z_N`. -/
private theorem units_pow_eq_neg_one_iff {N m : ℕ} (w : (ZMod N)ˣ) :
    w ^ m = -1 ↔ (w : ZMod N) ^ m = -1 := by
  rw [← Units.val_inj, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]

/-- **Lagrange:** a proper subgroup of a finite group has at most half the elements
(`Subgroup.card_subgroup_dvd_card`; the index is not `1` by `Subgroup.eq_top_of_card_eq`). -/
private theorem two_mul_card_le_of_ne_top {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hH : H ≠ ⊤) : 2 * Nat.card H ≤ Nat.card G := by
  obtain ⟨k, hk⟩ := H.card_subgroup_dvd_card
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hne : Nat.card H ≠ Nat.card G := fun h => hH (Subgroup.eq_top_of_card_eq H h)
  rcases k with _ | _ | k
  · omega
  · rw [Nat.zero_add, mul_one] at hk
    exact absurd hk.symm hne
  · rw [hk]
    nlinarith

/-- If every liar is (the value of) an element of a subgroup `H` of `(Z_N)^*`, then
`|L_N| ≤ |H|` (the map `α ↦ α` as a unit is injective, `Nat.card_le_card_of_injective`). -/
private theorem card_mrLiars_le_card {N : ℕ} [NeZero N] (hN : 2 ≤ N) (H : Subgroup (ZMod N)ˣ)
    (hH : ∀ α : ZMod N, MRLiar N α → ∀ hu : IsUnit α, hu.unit ∈ H) :
    (mrLiars N).card ≤ Nat.card H := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_le_card_of_injective
    (fun a : {x // x ∈ mrLiars N} =>
      (⟨(mrLiar_isUnit hN ((mem_mrLiars a.1).1 a.2)).unit,
        hH a.1 ((mem_mrLiars a.1).1 a.2) _⟩ : H)) ?_
  intro a b hab
  have := congrArg (fun x : H => ((x : (ZMod N)ˣ) : ZMod N)) hab
  simp only [IsUnit.unit_spec] at this
  exact Subtype.ext this

/-- The subgroup `{x ∈ (Z_N)^* | x^m = 1}` (the kernel of `x ↦ x^m`). -/
private def powOneSubgroup (N m : ℕ) : Subgroup (ZMod N)ˣ where
  carrier := {x | x ^ m = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [mul_pow, ha, hb, one_mul]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [inv_pow, ha, inv_one]

/-- Membership in `powOneSubgroup`. -/
private theorem mem_powOneSubgroup {N m : ℕ} (x : (ZMod N)ˣ) :
    x ∈ powOneSubgroup N m ↔ x ^ m = 1 := Iff.rfl

/-- The subgroup `{x ∈ (Z_N)^* | x^m = ±1}` (the preimage of `{±1}` under `x ↦ x^m`). -/
private def powPmOneSubgroup (N m : ℕ) : Subgroup (ZMod N)ˣ where
  carrier := {x | x ^ m = 1 ∨ x ^ m = -1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [mul_pow]
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> simp
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [inv_pow]
    have hinv : (-1 : (ZMod N)ˣ)⁻¹ = -1 :=
      inv_eq_of_mul_eq_one_right (by rw [neg_one_mul, neg_neg])
    rcases ha with ha | ha <;> rw [ha] <;> simp [hinv]

/-- Membership in `powPmOneSubgroup`. -/
private theorem mem_powPmOneSubgroup {N m : ℕ} (x : (ZMod N)ˣ) :
    x ∈ powPmOneSubgroup N m ↔ x ^ m = 1 ∨ x ^ m = -1 := Iff.rfl

/-- `−1 ≠ 1` in `Z_d` for a divisor `d > 1` of an odd number (`d ≠ 2`, so `d ≥ 3`). -/
private theorem neg_one_ne_one_of_dvd_odd {N d : ℕ} (hodd : Odd N) (hd : d ∣ N) (h1 : 1 < d) :
    (-1 : ZMod d) ≠ 1 := by
  have hne := Odd.ne_two_of_dvd_nat hodd hd
  haveI : Fact (2 < d) := ⟨by omega⟩
  exact ZMod.neg_one_ne_one

/-- **A Carmichael number is not a prime power** [CLRS09, Theorem 31.39, Case 1]: if every
unit of `Z_N` satisfies `a^{N−1} = 1` and `N = p^a` is a proper prime power, contradiction.

**Proof sketch.** `|Z_N^*| = Φ(p^a) = p^{a−1}(p−1)` is divisible by `p` (`a ≥ 2`), so by
Cauchy's theorem (`exists_prime_orderOf_dvd_card`) some unit `g` has order `p`; then
`g^{N−1} = 1` gives `p ∣ N − 1`, while `p ∣ N`, so `p ∣ 1`. -/
private theorem not_prime_pow_of_forall_pow {N : ℕ} [NeZero N] (hN : ¬ N.Prime) (h2 : 2 < N)
    (hA : ∀ a : (ZMod N)ˣ, a ^ (N - 1) = 1) {p a : ℕ} (hp : p.Prime) (hNp : N = p ^ a) :
    False := by
  have ha : 2 ≤ a := by
    rcases a with _ | _ | a
    · rw [pow_zero] at hNp; omega
    · exfalso
      rw [Nat.zero_add, pow_one] at hNp
      exact hN (hNp ▸ hp)
    · omega
  haveI := Fact.mk hp
  have hdvd : p ∣ Fintype.card (ZMod N)ˣ := by
    rw [ZMod.card_units_eq_totient, hNp, Nat.totient_prime_pow hp (by omega)]
    exact Dvd.dvd.mul_right (dvd_pow_self p (by omega)) _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card p hdvd
  have h1 : p ∣ N - 1 := hg ▸ orderOf_dvd_of_pow_eq_one (hA g)
  have h3 : p ∣ N := hNp ▸ dvd_pow_self p (by omega)
  have : p ∣ 1 := by
    have := Nat.dvd_sub h3 h1
    rwa [Nat.sub_sub_self (by omega : 1 ≤ N)] at this
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

/-- A composite `N > 2` all of whose units satisfy `a^{N−1} = 1` splits as `N = n₁ n₂` with
`n₁, n₂ > 1` coprime: `n₁ = ordProj[p] N`, `n₂ = ordCompl[p] N` for `p = N.minFac`
(`n₂ = 1` would make `N` a prime power, `not_prime_pow_of_forall_pow`). -/
private theorem exists_coprime_factorization {N : ℕ} [NeZero N] (hN : ¬ N.Prime) (h2 : 2 < N)
    (hA : ∀ a : (ZMod N)ˣ, a ^ (N - 1) = 1) :
    ∃ n₁ n₂ : ℕ, n₁ * n₂ = N ∧ Nat.Coprime n₁ n₂ ∧ 1 < n₁ ∧ 1 < n₂ := by
  have hN0 : N ≠ 0 := by omega
  have hp : N.minFac.Prime := Nat.minFac_prime (by omega)
  refine ⟨ordProj[N.minFac] N, ordCompl[N.minFac] N, Nat.ordProj_mul_ordCompl_eq_self N _,
    (Nat.coprime_ordCompl hp hN0).pow_left _, ?_, ?_⟩
  · have hpos := hp.factorization_pos_of_dvd hN0 (Nat.minFac_dvd N)
    exact Nat.one_lt_pow (by omega) hp.one_lt
  · by_contra h
    have hpos := Nat.ordCompl_pos N.minFac hN0
    have h1 : ordCompl[N.minFac] N = 1 := by omega
    have := Nat.ordProj_mul_ordCompl_eq_self N N.minFac
    rw [h1, mul_one] at this
    exact not_prime_pow_of_forall_pow hN h2 hA hp this.symm

/-- **The CRT witness** [CLRS09, Theorem 31.39, Case 2]: for odd `N = n₁ n₂` with coprime
`n₁, n₂ > 1` and a unit `v` with `v^m = −1`, the unit `w ≡ v (mod n₁)`, `w ≡ 1 (mod n₂)`
(`Nat.chineseRemainder`) has `w^m ∉ {1, −1}`.

**Proof sketch.** Under the reductions `Z_N → Z_{n₁}`, `Z_N → Z_{n₂}` (`ZMod.castHom`),
`w^m ↦ v^m = −1` and `w^m ↦ 1` respectively; `w^m = 1` would give `−1 = 1` in `Z_{n₁}` and
`w^m = −1` would give `−1 = 1` in `Z_{n₂}`, impossible for odd moduli `> 1`
(`neg_one_ne_one_of_dvd_odd`). `w` is a unit since `w` is coprime to `n₁` (as `v` is) and to
`n₂` (as `1` is) (`ZMod.unitOfCoprime`). -/
private theorem exists_unit_pow_ne {N : ℕ} [NeZero N] (hodd : Odd N) {n₁ n₂ : ℕ}
    (hN : n₁ * n₂ = N) (hcop : Nat.Coprime n₁ n₂) (h1 : 1 < n₁) (h2 : 1 < n₂) {m : ℕ}
    (v : (ZMod N)ˣ) (hv : v ^ m = -1) : ∃ w : (ZMod N)ˣ, w ^ m ≠ 1 ∧ w ^ m ≠ -1 := by
  have hd₁ : n₁ ∣ N := ⟨n₂, hN.symm⟩
  have hd₂ : n₂ ∣ N := ⟨n₁, by rw [← hN, mul_comm]⟩
  obtain ⟨k, hk₁, hk₂⟩ := Nat.chineseRemainder hcop (v : ZMod N).val 1
  have hkcop : Nat.Coprime k N := by
    rw [← hN, Nat.coprime_mul_iff_right]
    constructor
    · rw [Nat.Coprime, hk₁.gcd_eq]
      exact Nat.Coprime.coprime_dvd_right hd₁ (ZMod.val_coe_unit_coprime v)
    · rw [Nat.Coprime, hk₂.gcd_eq]
      exact Nat.gcd_one_left _
  have hπ₁ : ZMod.castHom hd₁ (ZMod n₁) (k : ZMod N) =
      ZMod.castHom hd₁ (ZMod n₁) (v : ZMod N) := by
    rw [ZMod.castHom_apply, ZMod.castHom_apply, ZMod.cast_natCast hd₁, ← ZMod.natCast_val]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hk₁
  have hw : ((ZMod.unitOfCoprime k hkcop : (ZMod N)ˣ) : ZMod N) = (k : ZMod N) :=
    ZMod.coe_unitOfCoprime k hkcop
  have hv' : (v : ZMod N) ^ m = -1 := (units_pow_eq_neg_one_iff v).1 hv
  have hA : ZMod.castHom hd₁ (ZMod n₁) ((k : ZMod N) ^ m) = -1 := by
    rw [map_pow, hπ₁, ← map_pow, hv', map_neg, map_one]
  have hB : ZMod.castHom hd₂ (ZMod n₂) ((k : ZMod N) ^ m) = 1 := by
    rw [map_pow, ZMod.castHom_apply, ZMod.cast_natCast hd₂,
      (ZMod.natCast_eq_natCast_iff _ _ _).2 hk₂, Nat.cast_one, one_pow]
  refine ⟨ZMod.unitOfCoprime k hkcop, fun h => ?_, fun h => ?_⟩
  · have h' : (k : ZMod N) ^ m = 1 := by rw [← hw]; exact (units_pow_eq_one_iff _).1 h
    rw [h', map_one] at hA
    exact neg_one_ne_one_of_dvd_odd hodd hd₁ h1 hA.symm
  · have h' : (k : ZMod N) ^ m = -1 := by rw [← hw]; exact (units_pow_eq_neg_one_iff _).1 h
    rw [h', map_neg, map_one] at hB
    exact neg_one_ne_one_of_dvd_odd hodd hd₂ h2 hB

/-- **Every liar lands in `{±1}` at the critical exponent:** if `j'` is at least every
`i ≤ j − 1` for which some unit `v` has `v^{u 2^i} = −1`, then every liar `α` has
`α^{u 2^{j'}} ∈ {1, −1}` [CLRS09, Theorem 31.39, Case 2].

**Proof sketch.** Induction on `i ≤ j` for the claim "`α^{u 2^i} = 1` implies
`α^{u 2^{j'}} ∈ {±1}`", applied at `i = j` where `α^{u 2^j} = α^{N−1} = 1`. At `i = 0`,
`α^u = 1` forces `α^{u 2^{j'}} = 1`. At `i + 1`: by the liar condition `α^{u 2^i} ∈ {±1}`; if
`1`, use the induction hypothesis; if `−1`, then `α` (a unit) witnesses the index `i`, so
`i ≤ j'` by maximality and `α^{u 2^{j'}} = (−1)^{2^{j'−i}}`, which is `−1` for `j' = i` and `1`
for `j' > i` (`Even.neg_one_pow`). -/
private theorem liar_pow_mem {N : ℕ} (hN : 2 < N) {j' : ℕ}
    (hmax : ∀ i ≤ mrExp N - 1, (∃ v : (ZMod N)ˣ, v ^ (mrOdd N * 2 ^ i) = -1) → i ≤ j')
    {α : ZMod N} (hα : MRLiar N α) :
    α ^ (mrOdd N * 2 ^ j') = 1 ∨ α ^ (mrOdd N * 2 ^ j') = -1 := by
  have hunit : IsUnit α := mrLiar_isUnit (by omega) hα
  have key : ∀ i ≤ mrExp N, α ^ (mrOdd N * 2 ^ i) = 1 →
      α ^ (mrOdd N * 2 ^ j') = 1 ∨ α ^ (mrOdd N * 2 ^ j') = -1 := by
    intro i
    induction i with
    | zero =>
      intro _ h0
      left
      rw [pow_zero, mul_one] at h0
      rw [pow_mul, h0, one_pow]
    | succ i ih =>
      intro hi hsucc
      rcases hα.2 i (by omega) hsucc with h1 | h1
      · exact ih (by omega) h1
      · have hle : i ≤ j' := hmax i (by omega)
          ⟨hunit.unit, by rw [units_pow_eq_neg_one_iff, IsUnit.unit_spec]; exact h1⟩
        have hsplit : mrOdd N * 2 ^ j' = mrOdd N * 2 ^ i * 2 ^ (j' - i) := by
          rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
        rw [hsplit, pow_mul, h1]
        rcases Nat.eq_or_lt_of_le hle with heq | hlt
        · subst heq
          right
          simp
        · left
          exact Even.neg_one_pow (Nat.even_pow.2 ⟨even_two, by omega⟩)
  exact key (mrExp N) le_rfl (by rw [mrOdd_mul_two_pow]; exact hα.1)

/-- **Odd composites have few liars** [PS10, Lemma 50.15, second half]: for odd composite
`N > 2`, `|L_N| ≤ (N−1)/2`, stated as `2 |L_N| ≤ N − 1`.

**Deviation:** the text says `N > 2` composite (oddness is needed) and `<` (the proof gives
`≤ Φ(N)/2 < (N−1)/2`, so `<` also holds; the weaker form suffices for Theorem 49.14).

**Proof sketch.** ([CLRS09, Theorems 31.38–31.39].) Every liar is a unit (`α^{N−1} = 1`,
`mrLiar_isUnit`), so it suffices to exhibit a proper subgroup of `Z_N^*` containing every
liar (`card_mrLiars_le_card`, `two_mul_card_le_of_ne_top`, `|Z_N^*| = Φ(N) < N`). If some
unit `a` has `a^{N−1} ≠ 1`, take `{x | x^{N−1} = 1}` (`powOneSubgroup`). Otherwise (`N` a
Carmichael number) `N` is not a prime power (`not_prime_pow_of_forall_pow`: by Cauchy's
result, for `N = p^k`, `k ≥ 2`, a unit of order `p` would give `p ∣ N − 1`), so `N = n₁ n₂`
with coprime `n₁, n₂ > 1` (`exists_coprime_factorization`); let `j'` be the largest
`i ≤ j − 1` such that some unit `v` has `v^{u 2^{i}} = −1` (`Nat.findGreatest`; `i = 0`
qualifies with `v = −1`, `u` odd); then `B = {x ∈ Z_N^* | x^{u 2^{j'}} = ±1}`
(`powPmOneSubgroup`) contains every liar (`liar_pow_mem`), and the unit `w` with
`w ≡ v (mod n₁)`, `w ≡ 1 (mod n₂)` (CRT, `exists_unit_pow_ne`) has `w^{u 2^{j'}} ∉ {±1}`,
so `B` is proper. -/
theorem two_mul_card_mrLiars_le {N : ℕ} [NeZero N] (hN : ¬ N.Prime) (hodd : N % 2 = 1)
    (h2 : 2 < N) : 2 * (mrLiars N).card ≤ N - 1 := by
  classical
  -- it suffices to find a proper subgroup of the units containing every liar
  suffices h : ∃ H : Subgroup (ZMod N)ˣ, H ≠ ⊤ ∧
      ∀ α : ZMod N, MRLiar N α → ∀ hu : IsUnit α, hu.unit ∈ H by
    obtain ⟨H, hH, hL⟩ := h
    have h1 := card_mrLiars_le_card (by omega) H hL
    have h3 := two_mul_card_le_of_ne_top H hH
    have h4 : Nat.card (ZMod N)ˣ = N.totient := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    have h5 := Nat.totient_lt N (by omega)
    omega
  by_cases hA : ∃ a : (ZMod N)ˣ, a ^ (N - 1) ≠ 1
  · -- some unit violates Fermat: the liars lie in the kernel of `x ↦ x^{N−1}`
    obtain ⟨a, ha⟩ := hA
    refine ⟨powOneSubgroup N (N - 1), fun htop => ha ?_, fun α hα hu => ?_⟩
    · exact (mem_powOneSubgroup a).1 (htop ▸ Subgroup.mem_top a)
    · rw [mem_powOneSubgroup, units_pow_eq_one_iff, IsUnit.unit_spec]
      exact hα.1
  · -- `N` is a Carmichael number: the largest-index construction
    push_neg at hA
    have hj : 0 < mrExp N :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two (by omega)
        (Nat.dvd_of_mod_eq_zero (by omega))
    have hu : Odd (mrOdd N) := mrOdd_odd (by omega)
    set P : ℕ → Prop := fun i => ∃ v : (ZMod N)ˣ, v ^ (mrOdd N * 2 ^ i) = -1 with hP
    have hP0 : P 0 := ⟨-1, by rw [pow_zero, mul_one]; exact hu.neg_one_pow⟩
    have hj'P : P (Nat.findGreatest P (mrExp N - 1)) :=
      Nat.findGreatest_spec (Nat.zero_le _) hP0
    have hmax : ∀ i ≤ mrExp N - 1, P i → i ≤ Nat.findGreatest P (mrExp N - 1) :=
      fun i hi hPi => Nat.le_findGreatest hi hPi
    obtain ⟨v, hv⟩ := hj'P
    obtain ⟨n₁, n₂, hN12, hcop, hn₁, hn₂⟩ := exists_coprime_factorization hN h2 hA
    obtain ⟨w, hw1, hw2⟩ := exists_unit_pow_ne (Nat.odd_iff.2 hodd) hN12 hcop hn₁ hn₂ v hv
    refine ⟨powPmOneSubgroup N (mrOdd N * 2 ^ Nat.findGreatest P (mrExp N - 1)),
      fun htop => ?_, fun α hα hunit => ?_⟩
    · rcases (mem_powPmOneSubgroup w).1 (htop ▸ Subgroup.mem_top w) with h | h
      exacts [hw1 h, hw2 h]
    · rw [mem_powPmOneSubgroup, units_pow_eq_one_iff, units_pow_eq_neg_one_iff,
        IsUnit.unit_spec]
      exact liar_pow_mem h2 hmax hα

/-! ### The Miller–Rabin test -/

/-- **The Miller–Rabin test** [PS10, Algorithm 49.13] with `t` rounds on the bases
`α_1, …, α_t ∈ [1, N−1]` (the base `i : Fin (N−1)` is `i + 1`): accept `N = 2`; reject even
`N > 2`; otherwise output "prime" (`true`) iff every base is a liar.

**Deviation:** bases in `[1, N−1]` rather than the text's `Z_N` (which contains `0 ∉ L_N`);
even `N` rejected directly. -/
def millerRabin (N t : ℕ) (α : Fin t → Fin (N - 1)) : Bool :=
  if N = 2 then true
  else if N % 2 = 0 then false
  else decide (∀ i, MRLiar N (((α i : ℕ) + 1 : ℕ) : ZMod N))

/-- A base `i + 1` with `i < N − 1` is a nonzero residue. -/
private theorem base_ne_zero {N : ℕ} (hN : 2 ≤ N) (i : Fin (N - 1)) :
    (((i : ℕ) + 1 : ℕ) : ZMod N) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by omega) h
  have := i.2
  omega

/-- **Miller–Rabin accepts every prime** [PS10, Theorem 49.14, second sentence]: for prime
`N` and every choice of bases the test outputs "prime".

**Proof sketch.** `N = 2` is the base case; a prime is odd otherwise; every base `α ≠ 0` is a
liar by `mrLiar_iff_of_prime`. -/
theorem millerRabin_of_prime {N : ℕ} [hN : Fact N.Prime] (t : ℕ) (α : Fin t → Fin (N - 1)) :
    millerRabin N t α = true := by
  unfold millerRabin
  split_ifs with h2 heven
  · rfl
  · exfalso
    have := hN.out.eq_two_or_odd.resolve_left h2
    omega
  · simp only [decide_eq_true_eq]
    intro i
    exact (mrLiar_iff_of_prime _).2 (base_ne_zero hN.out.two_le (α i))

/-- **Miller–Rabin rejects composites with probability `≥ 1 − 2^{−t}`**
[PS10, Theorem 49.14, first sentence]: for composite `N > 2` and `t` uniform independent
bases in `[1, N−1]`, the test outputs "prime" with probability at most `(1/2)^t`.

**Deviation:** "at least" `1 − 2^{−t}` (the text says "with probability").

**Proof sketch.** Even `N > 2` are rejected outright. For odd composite `N` the test accepts
iff all `t` bases are liars; the bases are independent (`uprob_pi_forall`), so the
probability is `Pr[α ∈ L_N]^t` with `Pr[α ∈ L_N] = |L_N ∖ {0}| / (N−1) = |L_N| / (N−1)`
(`0 ∉ L_N`, `MRLiar.ne_zero`; the map `i ↦ i + 1` is a bijection of `[0, N−2]` onto
`Z_N ∖ {0}`), and `|L_N| ≤ (N−1)/2` by `two_mul_card_mrLiars_le`. -/
theorem uprob_millerRabin_le {N : ℕ} (hN : ¬ N.Prime) (h2 : 2 < N) (t : ℕ) :
    uprob (fun α : Fin t → Fin (N - 1) => millerRabin N t α = true) ≤ (1 / 2 : ℝ) ^ t := by
  haveI : NeZero N := ⟨by omega⟩
  by_cases heven : N % 2 = 0
  · -- even composites are rejected outright
    have hfalse : ∀ α : Fin t → Fin (N - 1), millerRabin N t α = true ↔ False := by
      intro α
      unfold millerRabin
      rw [if_neg (by omega), if_pos heven]
      simp
    rw [OneWay.uprob_congr hfalse, uprob_false]
    positivity
  have hodd : N % 2 = 1 := by omega
  -- the test accepts iff every base is a liar
  have hiff : ∀ α : Fin t → Fin (N - 1), millerRabin N t α = true ↔
      ∀ i, MRLiar N (((α i : ℕ) + 1 : ℕ) : ZMod N) := by
    intro α
    unfold millerRabin
    rw [if_neg (by omega), if_neg heven]
    simp
  rw [OneWay.uprob_congr hiff,
    OneWay.uprob_pi_forall (fun i : Fin (N - 1) => MRLiar N (((i : ℕ) + 1 : ℕ) : ZMod N)),
    Fintype.card_fin]
  refine pow_le_pow_left₀ (uprob_nonneg _) ?_ t
  -- the bases `i + 1` that are liars are in bijection with `L_N` (`0 ∉ L_N`)
  rw [uprob_eq_card_filter, Fintype.card_fin]
  have hcard : (univ.filter fun i : Fin (N - 1) => MRLiar N (((i : ℕ) + 1 : ℕ) : ZMod N)).card =
      (mrLiars N).card := by
    refine Finset.card_bij (fun i _ => (((i : ℕ) + 1 : ℕ) : ZMod N)) ?_ ?_ ?_
    · intro i hi
      rw [mem_mrLiars]
      exact (mem_filter.1 hi).2
    · intro i _ j _ hij
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        at hij
      exact Fin.ext (by omega)
    · intro α hα
      rw [mem_mrLiars] at hα
      have hne : α.val ≠ 0 := fun h => hα.ne_zero (by omega) ((ZMod.val_eq_zero α).1 h)
      have hlt := α.val_lt
      refine ⟨⟨α.val - 1, by omega⟩, ?_, ?_⟩
      · rw [mem_filter]
        refine ⟨mem_univ _, ?_⟩
        simp only
        rw [show α.val - 1 + 1 = α.val by omega, ZMod.natCast_zmod_val]
        exact hα
      · simp only
        rw [show α.val - 1 + 1 = α.val by omega, ZMod.natCast_zmod_val]
  rw [hcard]
  have hle := two_mul_card_mrLiars_le hN hodd h2
  rw [div_le_div_iff₀ (by exact_mod_cast (by omega : 0 < N - 1)) (by norm_num), one_mul]
  exact_mod_cast (by omega : (mrLiars N).card * 2 ≤ N - 1)

/-! ### Sampling a random prime -/

/-- **`SamplePrime(n)`** [PS10, Algorithm 50.16], truncated to `T` trials: given `T` uniform
`n`-bit strings `x_1, …, x_T`, output the first one that reads (`bitsToNat`) as a prime, or
`⊥` (`none`) if none does. The instance of `firstHit` (lemma C4) for the predicate
"prime" on `n`-bit numbers.

**Deviation:** strict PPT with `T` trials and failure output instead of the text's expected
polynomial-time loop (D10); exact primality (`Nat.Prime`) instead of Miller–Rabin. -/
def samplePrime (n T : ℕ) (xs : Fin T → (Fin n → Bool)) : Option (Fin n → Bool) :=
  firstHit (fun b : Fin n → Bool => (bitsToNat b).Prime) xs

/-- `SamplePrime` fails exactly when none of the `T` strings is prime. -/
theorem samplePrime_eq_none_iff (n T : ℕ) (xs : Fin T → (Fin n → Bool)) :
    samplePrime n T xs = none ↔ ∀ t, ¬ (bitsToNat (xs t)).Prime :=
  firstHit_eq_none_iff _ xs

/-- A successful output of `SamplePrime` is prime. -/
theorem samplePrime_prime {n T : ℕ} {xs : Fin T → (Fin n → Bool)} {b : Fin n → Bool}
    (h : samplePrime n T xs = some b) : (bitsToNat b).Prime :=
  firstHit_eq_some_imp (fun b : Fin n → Bool => (bitsToNat b).Prime) h

/-- **Uniformity of `SamplePrime`** [PS10, Lemma 51.17, "a randomly selected `n`-bit prime"]:
conditioned on success the output is uniform on the primes — any two `n`-bit primes are
output with the same probability (lemma C4, `firstHit_uniform_of_some`). -/
theorem samplePrime_uniform_of_some (n T : ℕ) {b b' : Fin n → Bool} (hb : (bitsToNat b).Prime)
    (hb' : (bitsToNat b').Prime) :
    uprob (fun xs : Fin T → (Fin n → Bool) => samplePrime n T xs = some b) =
      uprob (fun xs : Fin T → (Fin n → Bool) => samplePrime n T xs = some b') :=
  firstHit_uniform_of_some _ T hb hb'

/-- The failure probability of `SamplePrime` is exactly `(1 − Pr[prime])^T`. -/
theorem uprob_samplePrime_none (n T : ℕ) :
    uprob (fun xs : Fin T → (Fin n → Bool) => samplePrime n T xs = none) =
      (1 - uprob (fun b : Fin n → Bool => (bitsToNat b).Prime)) ^ T :=
  uprob_firstHit_none _ T

/-- **Failure probability of `SamplePrime`** [PS10, Lemma 51.17 and p. 50]: for `n ≥ 2`,
`SamplePrime` fails with probability at most `(1 − 1/(2n))^T` (prime density `≥ 1/(2n)`,
Claim-33.1).

**Deviation:** the text's density `1/n` (p. 50) is `1/(2n)`. -/
theorem uprob_samplePrime_none_le (n T : ℕ) (hn : 2 ≤ n) :
    uprob (fun xs : Fin T → (Fin n → Bool) => samplePrime n T xs = none) ≤
      (1 - 1 / (2 * n : ℝ)) ^ T := by
  rw [uprob_samplePrime_none]
  have hdens := one_div_le_uprob_prime n hn
  rw [← uprob_prime_bits] at hdens
  have h1 := uprob_le_one (fun b : Fin n → Bool => (bitsToNat b).Prime)
  exact pow_le_pow_left₀ (by linarith) (by linarith) T

/-- **`SamplePrime` with `2n²` trials fails with probability at most `e^{−n}`**
[PS10, Lemma 51.17]: the truncation of the text's expected-polynomial loop at `T = 2n²`.

**Proof sketch.** `(1 − 1/(2n))^{2n²} = (1 − n/(2n²))^{2n²} ≤ e^{−n}`
(`Real.one_sub_div_pow_le_exp_neg`). -/
theorem uprob_samplePrime_none_le_exp (n : ℕ) (hn : 2 ≤ n) :
    uprob (fun xs : Fin (2 * n ^ 2) → (Fin n → Bool) => samplePrime n (2 * n ^ 2) xs = none) ≤
      Real.exp (-n) := by
  refine (uprob_samplePrime_none_le n (2 * n ^ 2) hn).trans ?_
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnn : (n : ℝ) * 1 ≤ n * n := mul_le_mul_of_nonneg_left hn' (by linarith)
  have h := Real.one_sub_div_pow_le_exp_neg (n := 2 * n ^ 2) (t := n)
    (by push_cast; nlinarith)
  have heq : (1 - (n : ℝ) / ((2 * n ^ 2 : ℕ) : ℝ)) = 1 - 1 / (2 * n : ℝ) := by
    push_cast
    field_simp
  rw [heq] at h
  exact h

/-- **`SamplePrime` with `2n²` trials fails with probability at most `2^{−n}`**: the form of
[PS10, Lemma 51.17] used by the collections (`e^{−n} ≤ 2^{−n}`). -/
theorem uprob_samplePrime_none_le_two_pow (n : ℕ) (hn : 2 ≤ n) :
    uprob (fun xs : Fin (2 * n ^ 2) → (Fin n → Bool) => samplePrime n (2 * n ^ 2) xs = none) ≤
      (1 / 2 : ℝ) ^ n := by
  refine (uprob_samplePrime_none_le_exp n hn).trans ?_
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hinv : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  calc Real.exp (-n) = Real.exp (-1) ^ n := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
    _ ≤ (1 / 2) ^ n := pow_le_pow_left₀ (Real.exp_pos _).le hinv n

/-- **`SamplePrime` is statistically close to uniform on `Π_n`** [PS10, Lemma 51.17, the form
consumed by the collections]: falling back to a fixed prime `d` on failure, the sampler is
within `(1 − 1/(2n))^T` of the uniform distribution on the `n`-bit primes (C4,
`statClose_firstHit`). -/
theorem statClose_samplePrime (n T : ℕ) (hn : 2 ≤ n) {d : Fin n → Bool}
    (hd : (bitsToNat d).Prime) :
    StatClose (fun xs : Fin T → (Fin n → Bool) => (samplePrime n T xs).getD d)
      (fun p : {b : Fin n → Bool // (bitsToNat b).Prime} => (p : Fin n → Bool))
      ((1 - 1 / (2 * n : ℝ)) ^ T) := by
  refine (statClose_firstHit (fun b : Fin n → Bool => (bitsToNat b).Prime) T hd).mono ?_
  have hdens := one_div_le_uprob_prime n hn
  rw [← uprob_prime_bits] at hdens
  have h1 := uprob_le_one (fun b : Fin n → Bool => (bitsToNat b).Prime)
  exact pow_le_pow_left₀ (by linarith) (by linarith) T

/-! ### `SamplePrime` as a machine -/

/-- The number read from a bit string on a tape (most significant bit first): the list form of
`bitsToNat`. -/
def listToNat (w : List Bool) : ℕ := w.foldl (fun a c => 2 * a + if c then 1 else 0) 0

/-- `bitsToNat` is `listToNat` of the list of bits. -/
theorem bitsToNat_eq_listToNat {n : ℕ} (b : Fin n → Bool) : bitsToNat b = listToNat (List.ofFn b) :=
  rfl

/-- The coin polynomial of `SamplePrime` at `T = 2n²` trials of `n` bits: `2n² · n`. -/
def samplePrimeCoins : PolyExpr :=
  PolyExpr.mul (PolyExpr.mul (PolyExpr.const 2) (PolyExpr.pow PolyExpr.var 2)) PolyExpr.var

/-- `samplePrimeCoins` evaluates to `2n² · n`. -/
theorem eval_samplePrimeCoins (n : ℕ) : samplePrimeCoins.eval n = 2 * n ^ 2 * n := rfl

/-- The `T` blocks of `n` bits of a coin string of length `T · n`: block `t` is the bits
`t·n, …, t·n + n − 1`. -/
def chunk (T n : ℕ) (r : Fin (T * n) → Bool) : Fin T → Fin n → Bool := fun t i =>
  r ⟨t * n + i, by
    have ht : (t : ℕ) + 1 ≤ T := t.2
    calc (t : ℕ) * n + i < (t : ℕ) * n + n := by omega
      _ = ((t : ℕ) + 1) * n := by ring
      _ ≤ T * n := Nat.mul_le_mul_right n ht⟩

/-! #### The `SamplePrime` state loop -/

/-- The step of the `SamplePrime` loop on the state word `⟨1^n, s⟩`: discard the first `n`
bits of the remaining coins `s`, keeping the parameter. -/
private def spStep (x : List Bool) : List Bool :=
  pairEncode (pairFstD x) ((pairSndD x).drop (PolyExpr.var.eval (pairFstD x).length))

/-- The current candidate of the `SamplePrime` loop on the state word `⟨1^n, s⟩`: the first
`n` bits of the remaining coins `s`. -/
private def spOut (x : List Bool) : List Bool :=
  (pairSndD x).take (PolyExpr.var.eval (pairFstD x).length)

/-- The acceptance test of the `SamplePrime` loop: the current candidate reads as a prime. -/
private def spAcc (x : List Bool) : Bool := decide (listToNat (spOut x)).Prime

/-- The step is polynomial-time (`Complexity.polyTimeComputable_pairDropPoly` at `var`). -/
private theorem spStep_poly : PolyTimeComputable spStep :=
  polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_pairDropPoly .var)

/-- The candidate is polynomial-time (`Complexity.polyTimeComputable_pairTakePoly` at `var`). -/
private theorem spOut_poly : PolyTimeComputable spOut := polyTimeComputable_pairTakePoly .var

/-- The acceptance test is polynomial-time given the primality test `hP`. -/
private theorem spAcc_poly
    (hP : PolyTimeComputable fun w : List Bool => [decide (listToNat w).Prime]) :
    PolyTimeComputable fun x => [spAcc x] := hP.comp spOut_poly

/-- The orbit of the step from `⟨u, s⟩`: after `i` rounds the state is `⟨u, s.drop (i·|u|)⟩`. -/
private theorem spStep_iterate (u s : List Bool) (i : ℕ) :
    spStep^[i] (pairEncode u s) = pairEncode u (s.drop (i * u.length)) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [spStep, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var,
      List.drop_drop]
    congr 2
    ring

/-- One step at most doubles the length: `|spStep x| ≤ 2|x| + 2`
(`Complexity.StateLoop.length_pairFstD_add_pairSndD_le`). -/
private theorem length_spStep_le (x : List Bool) : (spStep x).length ≤ 2 * x.length + 2 := by
  have := StateLoop.length_pairFstD_add_pairSndD_le x
  simp only [spStep, length_pairEncode, PolyExpr.eval_var, List.length_drop]
  omega

/-- From the first round on the state is a pair whose second component only shrinks. -/
private theorem length_spStep_spStep_le (x : List Bool) :
    (spStep (spStep x)).length ≤ (spStep x).length := by
  simp only [spStep, pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode,
    PolyExpr.eval_var, List.length_drop]
  omega

/-- The orbit bound `|spStep^[i] x| ≤ 2|x| + 2` demanded by the repetition lemma (for every
word `x`, not only for well-formed state words). -/
private theorem length_spStep_iterate_le (x : List Bool) (i : ℕ) :
    (spStep^[i] x).length ≤ 2 * x.length + 2 := by
  cases i with
  | zero => simp only [Function.iterate_zero, id]; omega
  | succ i =>
    induction i with
    | zero => exact length_spStep_le x
    | succ i ih =>
      rw [Function.iterate_succ_apply'] at ih ⊢
      rw [Function.iterate_succ_apply']
      exact (length_spStep_spStep_le _).trans ih

/-- Block `t` of the coin layout `chunk` is the `t`-th `n`-bit segment of the coin list. -/
private theorem ofFn_chunk {T n : ℕ} (r : Fin (T * n) → Bool) (t : Fin T) :
    List.ofFn (chunk T n r t) = ((List.ofFn r).drop (t * n)).take n := by
  have ht : ((t : ℕ) + 1) * n ≤ T * n := Nat.mul_le_mul_right n t.2
  rw [Nat.add_mul, one_mul] at ht
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take, List.length_drop]
    omega
  · intro i h1 h2
    simp [chunk]

/-- `firstHit` returns the first draw satisfying `E` (induction on the number of draws,
`List.finRange_succ`). -/
private theorem firstHit_eq_some_of_first {α : Type*} (E : α → Prop) [DecidablePred E] :
    ∀ {T : ℕ} (xs : Fin T → α) (t : Fin T), E (xs t) → (∀ t' < t, ¬ E (xs t')) →
      firstHit E xs = some (xs t)
  | 0, _, t, _, _ => t.elim0
  | T + 1, xs, t, ht, hfirst => by
    unfold firstHit
    rw [List.finRange_succ, List.findSome?_cons]
    rcases Fin.eq_zero_or_eq_succ t with rfl | ⟨t', rfl⟩
    · simp [ht]
    · have h0 : ¬ E (xs 0) := hfirst 0 (Fin.succ_pos t')
      simp only [h0, if_false]
      rw [List.findSome?_map]
      have ih := firstHit_eq_some_of_first E (fun s => xs s.succ) t' ht
        (fun s hs => hfirst s.succ (Fin.succ_lt_succ_iff.2 hs))
      unfold firstHit at ih
      exact ih

/-- Along the orbit from `⟨1^n, rs⟩`, the acceptance test at round `i` tests block `i`. -/
private theorem spAcc_iterate (n : ℕ) (rs : List Bool) (i : ℕ) :
    spAcc (spStep^[i] (pairEncode (List.replicate n true) rs)) =
      decide (listToNat ((rs.drop (i * n)).take n)).Prime := by
  rw [spStep_iterate]
  simp [spAcc, spOut]

/-- Along the orbit from `⟨1^n, rs⟩`, the candidate at round `i` is block `i`. -/
private theorem spOut_iterate (n : ℕ) (rs : List Bool) (i : ℕ) :
    spOut (spStep^[i] (pairEncode (List.replicate n true) rs)) = (rs.drop (i * n)).take n := by
  rw [spStep_iterate]
  simp [spOut]

/-- **The loop computes `SamplePrime`:** the `find?` form of the iterated search from the
state word `⟨1^n, r⟩` over `List.range (|⟨1^n, r⟩| + 1)` rounds is `samplePrime n (2n²)` on
the blocks of `r` (as bits, `[]` on failure).

**Proof sketch.** Round `i` tests block `i` (`spAcc_iterate`); blocks `i ≥ 2n²` are empty
and read `0`, not a prime; the range `|⟨1^n, r⟩| + 1 ≥ 2n²` covers every block. If the search
succeeds at round `k` (`List.find?_eq_some_iff_getElem`), then `k < 2n²`, block `k` is prime
and no earlier block is, so `firstHit` returns block `k` (`firstHit_eq_some_of_first`,
`ofFn_chunk`); if it fails, no block is prime and `samplePrime` returns `none`
(`samplePrime_eq_none_iff`). -/
private theorem spFind_eq (n : ℕ) (r : Fin (2 * n ^ 2 * n) → Bool) :
    (match (List.range (PolyExpr.var.eval
        (pairEncode (List.replicate n true) (List.ofFn r)).length + 1)).find?
        (fun i => spAcc (spStep^[i] (pairEncode (List.replicate n true) (List.ofFn r)))) with
      | some i => spOut (spStep^[i] (pairEncode (List.replicate n true) (List.ofFn r)))
      | none => []) =
      ((samplePrime n (2 * n ^ 2) (chunk (2 * n ^ 2) n r)).map List.ofFn).getD [] := by
  have hlen : (List.ofFn r).length = 2 * n ^ 2 * n := List.length_ofFn
  have hblock : ∀ t : Fin (2 * n ^ 2),
      decide (listToNat (((List.ofFn r).drop (t * n)).take n)).Prime =
        decide (bitsToNat (chunk (2 * n ^ 2) n r t)).Prime := by
    intro t
    rw [bitsToNat_eq_listToNat, ofFn_chunk]
  have hbig : ∀ i, 2 * n ^ 2 ≤ i →
      decide (listToNat (((List.ofFn r).drop (i * n)).take n)).Prime = false := by
    intro i hi
    have hnil : (List.ofFn r).drop (i * n) = [] :=
      List.drop_eq_nil_of_le (by rw [hlen]; exact Nat.mul_le_mul_right n hi)
    simp [hnil, listToNat, Nat.not_prime_zero]
  have hrange : 2 * n ^ 2 ≤
      PolyExpr.var.eval (pairEncode (List.replicate n true) (List.ofFn r)).length + 1 := by
    simp only [PolyExpr.eval_var, length_pairEncode, List.length_replicate, hlen]
    have : n ^ 2 ≤ n ^ 2 * n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · exact Nat.le_mul_of_pos_right _ h
    have h2 : 2 * n ^ 2 * n = 2 * (n ^ 2 * n) := by ring
    omega
  simp only [spAcc_iterate]
  split
  · rename_i k hf
    rw [List.find?_eq_some_iff_getElem] at hf
    obtain ⟨hpk, j, hj, hjk, hfirst⟩ := hf
    rw [List.getElem_range] at hjk
    subst hjk
    have hkT : j < 2 * n ^ 2 := by
      by_contra h
      rw [hbig j (not_lt.1 h)] at hpk
      exact Bool.false_ne_true hpk
    have hsome : samplePrime n (2 * n ^ 2) (chunk (2 * n ^ 2) n r) =
        some (chunk (2 * n ^ 2) n r ⟨j, hkT⟩) := by
      refine firstHit_eq_some_of_first _ _ ⟨j, hkT⟩ ?_ ?_
      · have := hblock ⟨j, hkT⟩
        rw [this] at hpk
        exact of_decide_eq_true hpk
      · intro t' ht'
        have h1 := hfirst t'.val (by simpa using ht')
        rw [List.getElem_range, hblock t'] at h1
        simpa using h1
    rw [hsome, spOut_iterate]
    simp only [Option.map_some, Option.getD_some, ofFn_chunk]
  · rename_i hf
    rw [List.find?_eq_none] at hf
    have hnone : samplePrime n (2 * n ^ 2) (chunk (2 * n ^ 2) n r) = none := by
      rw [samplePrime_eq_none_iff]
      intro t ht
      have := hf t (by rw [List.mem_range]; have := t.2; omega)
      rw [hblock t] at this
      exact this (by simpa using ht)
    rw [hnone]
    rfl

/-- **`SamplePrime` is a PPT** [PS10, Lemma 51.17, "in time `poly(n)`"], given a
polynomial-time primality test on binary strings (the hypothesis `Rem-33.2`/Q6 of the plan,
AKS or Miller–Rabin): there is a uniform `NUPPT` with coin polynomial `2n² · n` whose
activation at parameter `n` on the empty argument with coins `r` (read as `2n²` blocks of
`n` bits) outputs the bits of `samplePrime n (2n²)`, or `[]` on failure.

**Proof sketch.** Instance of `Complexity.polyTimeComputable_iterateFind` (M3): on the state
word `⟨1^n, r⟩`, the step `spStep` drops the first `n` bits of the second component
(`polyTimeComputable_pairDropPoly var`), the acceptance test `spAcc` is the primality test
`hP` on the first `n` bits (`polyTimeComputable_pairTakePoly var`), the payload `spOut` is
those `n` bits; `R = var` rounds (the input length `|⟨1^n, r⟩| ≥ 2n²` covers every block,
later rounds see the empty block), orbit length bounded by `P = 2·var + 2`
(`length_spStep_iterate_le`); the `List.range.find?` form of the iterated search is
`firstHit` over the blocks of `r` (`chunk`), `spFind_eq`. Package by
`NUPPT.ofPolyTimeUniform` with `coins = samplePrimeCoins` after the projection
`z ↦ ⟨inParam z, inCoins z⟩`, and read the activation through
`NUPPT.runAtL_ofPolyTimeUniform` and the layout projections. -/
theorem exists_samplePrime_nuppt
    (hP : PolyTimeComputable fun w : List Bool => [decide (listToNat w).Prime]) :
    ∃ A : NUPPT, A.Uniform ∧ A.coins = samplePrimeCoins ∧
      ∀ (n : ℕ) (r : Fin (2 * n ^ 2 * n) → Bool),
        A.runAtL n [] (List.ofFn r) =
          ((samplePrime n (2 * n ^ 2) (chunk (2 * n ^ 2) n r)).map List.ofFn).getD [] := by
  have hF := polyTimeComputable_iterateFind spStep_poly (spAcc_poly hP) spOut_poly
    PolyExpr.var (PolyExpr.add (.mul (.const 2) .var) (.const 2))
    (fun x i _ => by simpa using length_spStep_iterate_le x i)
  have hpre : PolyTimeComputable fun z => pairEncode (NUPPT.inParam z) (NUPPT.inCoins z) :=
    NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  refine ⟨NUPPT.ofPolyTimeUniform (hF.comp hpre) samplePrimeCoins,
    NUPPT.ofPolyTimeUniform_uniform _ _, rfl, fun n r => ?_⟩
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  have h1 : NUPPT.inParam (pairEncode (pairEncode (NUPPT.advInput n []) []) (List.ofFn r)) =
      List.replicate n true := by
    simp [NUPPT.inParam, NUPPT.advInput]
  have h2 : NUPPT.inCoins (pairEncode (pairEncode (NUPPT.advInput n []) []) (List.ofFn r)) =
      List.ofFn r := by
    simp [NUPPT.inCoins]
  simp only [Function.comp_apply, h1, h2]
  exact spFind_eq n r

end TCSlib.Cryptography.NumberTheory
