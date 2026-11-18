/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.CoinSampling.Basic
import Mathlib.Algebra.BigOperators.Fin

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The bucket sampler and rational laws

The single-draw sampler of a non-dyadic range: read `s` fair coins as a number `x < 2^s`; with
`q = ⌊2^s/N⌋`, accept iff `x < q·N` and output `x mod N`. Every residue has exactly `q`
preimages below `q·N` (equal buckets), so the output is exactly uniform on success, and the
sampler gives up on the leftover `2^s mod N` values: `fail = (2^s mod N)/2^s < N/2^s`. With
`b + t` coins for a modulus `N ≤ 2^b`, the failure is at most `2^{-t}`.

Laws other than uniform are pushforwards of a uniform seed. A rational law with integer weights
`w` is the first coordinate of a uniform `RatSeed w = Σ a, Fin (w a)` (weighted buckets), read
through Mathlib's cumulative enumeration `finSigmaFinEquiv`.

## Main definitions

* `CoinSampling.bucketDec N s`, `bucket N s`: the bucket decoder and sampler of `Fin N`.
* `CoinSampling.ofEquiv e s`: the bucket sampler of any finite type through `e : Ω ≃ Fin N`.
* `CoinSampling.RatSeed w`, `weighted w s`: the seed of a rational law and its sampler.

## Main results

* `CoinSampling.bucketDec_eq_some_iff`, `bucketDec_eq_none_iff`: the decoder in numbers.
* `CoinSampling.uprob_bucketDec_eq_some`: every residue has probability `⌊2^s/N⌋/2^s`.
* `CoinSampling.fail_bucket`: `fail = (2^s mod N)/2^s` exactly; `fail_bucket_lt`,
  `fail_bucket_le` (slack bits).
* `CoinSampling.uprob_ratSeed_fst`: a uniform rational seed has the law `w a / Σ w`.

## References

* [Lem19] D. Lemire, *Fast Random Integer Generation in an Interval*, ACM Trans. Model. Comput.
  Simul. 29(1), 2019; arXiv:1805.10941v4 (28 December 2018), §3.2 and Algorithm 4 (the Java
  algorithm: accept `x ∈ [0, 2^L − (2^L mod s))`, return `x mod s`), Lemma 2.1 (equal counts
  of each remainder on an interval whose length `s` divides).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Lemma 51.17 (rejection sampling is uniform conditioned on success).

**Deviation.** [Lem19, Algorithm 4] repeats the draw until it is accepted (a loop with an
unbounded number of coins); `bucket N s` makes one draw of `s` coins and gives up on rejection,
so that its coin count is fixed and the failure is an explicit term (`fail_bucket`). The
acceptance test `x < ⌊2^s/N⌋·N` is the algorithm's `x ∈ [0, 2^L − (2^L mod s))`.
-/

namespace TCSlib.Cryptography.CoinSampling

open Finset

/-- **The bucket decoder**: read the `s` coins as a number `x < 2^s` (`bitsToNat`, as
`uniformFromBits` does); with `q = ⌊2^s/N⌋`, accept iff `x < q·N` and output `x mod N`, the
second coordinate of `finProdFinEquiv.symm x : Fin q × Fin N`. One rejection trial
(`uniformFromBits`) at the threshold `q·N`, then a reduction: one round of
[Lem19, §3.2, Algorithm 4], giving up instead of retrying (see the module docstring). -/
def bucketDec (N s : ℕ) (c : Fin s → Bool) : Option (Fin N) :=
  (uniformFromBits (2 ^ s / N * N) s c).map fun x => (finProdFinEquiv.symm x).2

/-- `bucketDec N s c` is the one-trial rejection read `uniformFromBits (⌊2^s/N⌋·N) s c`,
reduced modulo `N` through `finProdFinEquiv.symm`. -/
theorem bucketDec_eq (N s : ℕ) (c : Fin s → Bool) :
    bucketDec N s c =
      (uniformFromBits (2 ^ s / N * N) s c).map fun x => (finProdFinEquiv.symm x).2 := rfl

/-- The bucket decoder outputs `a` exactly when the coins read below `⌊2^s/N⌋·N` and are
congruent to `a` mod `N`: `bucketDec N s c = some a ↔ x < ⌊2^s/N⌋·N ∧ x % N = a` with
`x = bitsToNat c`. -/
theorem bucketDec_eq_some_iff (N s : ℕ) (c : Fin s → Bool) (a : Fin N) :
    bucketDec N s c = some a ↔ bitsToNat c < 2 ^ s / N * N ∧ bitsToNat c % N = a := by
  rw [bucketDec_eq, Option.map_eq_some_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [uniformFromBits_eq_some_iff] at hx
    refine ⟨hx ▸ x.2, ?_⟩
    rw [hx, finProdFinEquiv_symm_apply, Fin.coe_modNat]
  · rintro ⟨hlt, hmod⟩
    refine ⟨⟨bitsToNat c, hlt⟩, (uniformFromBits_eq_some_iff c _).2 rfl, Fin.ext ?_⟩
    rw [finProdFinEquiv_symm_apply, Fin.coe_modNat]
    exact hmod

/-- The bucket decoder gives up exactly when the coins read at least `⌊2^s/N⌋·N`. -/
theorem bucketDec_eq_none_iff (N s : ℕ) (c : Fin s → Bool) :
    bucketDec N s c = none ↔ 2 ^ s / N * N ≤ bitsToNat c := by
  rw [bucketDec_eq, Option.map_eq_none_iff, uniformFromBits_eq_none_iff]

/-- **Equal buckets** [Lem19, Lemma 2.1]: below `q·N` (`q = ⌊2^s/N⌋`) each residue `a` mod `N`
has exactly `q` representatives: the fibre of `a` under `x ↦ (finProdFinEquiv.symm x).2` is
`{finProdFinEquiv (j, a) | j < q}`. -/
theorem card_filter_finProdFinEquiv_symm_snd (q N : ℕ) (a : Fin N) :
    (univ.filter fun x : Fin (q * N) => (finProdFinEquiv.symm x).2 = a).card = q := by
  rw [← Fintype.card_subtype]
  refine (Fintype.card_congr
    { toFun := fun x => (finProdFinEquiv.symm x.1).1
      invFun := fun j => ⟨finProdFinEquiv (j, a),
        congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (j, a))⟩
      left_inv := fun x => by
        rcases x with ⟨y, rfl⟩
        exact Subtype.ext (finProdFinEquiv.apply_symm_apply y)
      right_inv := fun j => by
        dsimp only
        rw [Equiv.symm_apply_apply] }).trans (Fintype.card_fin q)

/-- **Equal buckets**: every residue is output with probability `⌊2^s/N⌋ / 2^s`.

**Proof sketch.** The event is the union over the `q = ⌊2^s/N⌋` values `x < q·N` in the fibre of
`a` (`card_filter_finProdFinEquiv_symm_snd`) of `{uniformFromBits = some x}` (grouped by
`uprob_comp_eq_sum_fiber`, `Fintype.sum_option`), each of probability `1/2^s`
(`uprob_uniformFromBits_eq_some`, valid as `q·N ≤ 2^s`). -/
theorem uprob_bucketDec_eq_some (N s : ℕ) (a : Fin N) :
    uprob (fun c => bucketDec N s c = some a) = ((2 ^ s / N : ℕ) : ℝ) / 2 ^ s := by
  classical
  have hk : 2 ^ s / N * N ≤ 2 ^ s := Nat.div_mul_le_self _ _
  have h := uprob_comp_eq_sum_fiber (uniformFromBits (2 ^ s / N * N) s)
    (fun o => o.map (fun x => (finProdFinEquiv.symm x).2) = some a)
  rw [sum_filter, Fintype.sum_option, Option.map_none, if_neg (fun h' => by simp at h'),
    zero_add] at h
  refine h.trans ?_
  have hterm : ∀ x : Fin (2 ^ s / N * N),
      (if (some x).map (fun x => (finProdFinEquiv.symm x).2) = some a then
        uprob (fun c => uniformFromBits (2 ^ s / N * N) s c = some x) else 0) =
      if (finProdFinEquiv.symm x).2 = a then 1 / 2 ^ s else 0 := fun x => by
    by_cases hx : (finProdFinEquiv.symm x).2 = a
    · rw [if_pos (by rw [Option.map_some, hx]), if_pos hx, uprob_uniformFromBits_eq_some hk]
    · rw [if_neg (by rw [Option.map_some, Option.some_inj]; exact hx), if_neg hx]
  rw [Finset.sum_congr rfl fun x _ => hterm x, ← sum_filter, sum_const,
    card_filter_finProdFinEquiv_symm_snd, nsmul_eq_mul, mul_one_div]

/-- **The bucket sampler** of `Fin N` from `s` coins: `bucketDec N s`, exact on success by
`uprob_bucketDec_eq_some` [Lem19, §3.2, Algorithm 4] (one round). -/
def bucket (N s : ℕ) : CoinSampler (Fin N) s where
  dec := bucketDec N s
  uniform_of_some a a' := by rw [uprob_bucketDec_eq_some, uprob_bucketDec_eq_some]

/-- `(bucket N s).dec = bucketDec N s`. -/
theorem bucket_dec (N s : ℕ) : (bucket N s).dec = bucketDec N s := rfl

/-- **The bucket failure probability, exactly**: `(bucket N s).fail = (2^s mod N)/2^s`
(also for `N = 0`, where it is `1`).

**Proof sketch.** The decoder gives up iff the trial does (`Option.map_eq_none_iff`), so
`uprob_uniformFromBits_none` gives `1 − ⌊2^s/N⌋·N/2^s`, and
`2^s = ⌊2^s/N⌋·N + 2^s mod N` (`Nat.div_add_mod`). -/
theorem fail_bucket (N s : ℕ) : (bucket N s).fail = ((2 ^ s % N : ℕ) : ℝ) / 2 ^ s := by
  have hk : 2 ^ s / N * N ≤ 2 ^ s := Nat.div_mul_le_self _ _
  rw [CoinSampler.fail_eq, bucket_dec,
    OneWay.uprob_congr fun c =>
      (bucketDec_eq_none_iff N s c).trans (uniformFromBits_eq_none_iff c).symm,
    uprob_uniformFromBits_none hk]
  have hsum : ((2 ^ s / N * N : ℕ) : ℝ) + ((2 ^ s % N : ℕ) : ℝ) = 2 ^ s := by
    have := Nat.div_add_mod (2 ^ s) N
    rw [mul_comm] at this
    exact_mod_cast this
  have h2 : (0 : ℝ) < 2 ^ s := by positivity
  rw [eq_div_iff h2.ne', sub_mul, one_mul, div_mul_cancel₀ _ h2.ne']
  push_cast at hsum ⊢
  linarith

/-- **The design sketch's bound**: for `0 < N`, the bucket sampler fails with probability
`< N/2^s` (`fail_bucket`, `2^s mod N < N`). -/
theorem fail_bucket_lt {N : ℕ} (hN : 0 < N) (s : ℕ) : (bucket N s).fail < N / 2 ^ s := by
  rw [fail_bucket]
  have h2 : (0 : ℝ) < 2 ^ s := by positivity
  exact div_lt_div_of_pos_right (by exact_mod_cast Nat.mod_lt _ hN) h2

/-- **Slack bits**: if `0 < N ≤ 2^b`, the bucket sampler with `b + t` coins fails with
probability at most `2^{-t}`: `(bucket N (b + t)).fail ≤ (2⁻¹)^t` (`fail_bucket_lt` and
`N/2^{b+t} ≤ 2^b/2^{b+t} = 2^{-t}`). -/
theorem fail_bucket_le {N b : ℕ} (hN0 : 0 < N) (hN : N ≤ 2 ^ b) (t : ℕ) :
    (bucket N (b + t)).fail ≤ (2 : ℝ)⁻¹ ^ t := by
  refine (fail_bucket_lt hN0 (b + t)).le.trans ?_
  have hN' : (N : ℝ) ≤ 2 ^ b := by exact_mod_cast hN
  have h2 : (0 : ℝ) < 2 ^ (b + t) := by positivity
  calc (N : ℝ) / 2 ^ (b + t) ≤ 2 ^ b / 2 ^ (b + t) := div_le_div_of_nonneg_right hN' h2.le
    _ = (2 : ℝ)⁻¹ ^ t := by
      rw [pow_add, inv_pow, div_mul_eq_div_div, div_self (by positivity), one_div]

/-- **Uniform on any finite type through an enumeration** `e : Ω ≃ Fin N`: the bucket sampler
of `Fin N`, transported along `e.symm`. Efficient decoding needs a computable `e`
(`ZMod.finEquiv`, `finProdFinEquiv`, `finSigmaFinEquiv`); `Fintype.equivFin` serves laws only.
Glue. -/
def ofEquiv {Ω : Type} [Fintype Ω] {N : ℕ} (e : Ω ≃ Fin N) (s : ℕ) : CoinSampler Ω s :=
  (bucket N s).congr e.symm

/-- `(ofEquiv e s).dec c = (bucketDec N s c).map e.symm`. -/
theorem ofEquiv_dec {Ω : Type} [Fintype Ω] {N : ℕ} (e : Ω ≃ Fin N) (s : ℕ) (c : Fin s → Bool) :
    (ofEquiv e s).dec c = (bucketDec N s c).map e.symm := rfl

/-- `(ofEquiv e s).fail = (bucket N s).fail` (`CoinSampler.fail_congr`). -/
theorem fail_ofEquiv {Ω : Type} [Fintype Ω] {N : ℕ} (e : Ω ≃ Fin N) (s : ℕ) :
    (ofEquiv e s).fail = (bucket N s).fail :=
  CoinSampler.fail_congr _ _

/-- **The seed type of a rational law** with integer weights `w : α → ℕ`: one element per unit
of weight, `Σ a, Fin (w a)`. Its uniform law pushed along `Sigma.fst` is the law
`a ↦ w a / Σ_b w b` (`uprob_ratSeed_fst`): the weighted buckets of the design sketch. Glue. -/
abbrev RatSeed {α : Type} (w : α → ℕ) : Type := Σ a, Fin (w a)

/-- `RatSeed w = Σ a, Fin (w a)`. -/
theorem ratSeed_eq {α : Type} (w : α → ℕ) : RatSeed w = (Σ a, Fin (w a)) := rfl

/-- **The rational law of a seed**: a uniform seed of `RatSeed w` has first coordinate `a` with
probability `w a / Σ_b w b`: the fibre of `a` under `Sigma.fst` is `Fin (w a)` and the type has
`Σ_b w b` elements (`Fintype.card_sigma`). Glue. -/
theorem uprob_ratSeed_fst {α : Type} [Fintype α] (w : α → ℕ) (a : α) :
    uprob (fun x : RatSeed w => x.1 = a) = (w a : ℝ) / ∑ b, w b := by
  let e : {x : RatSeed w // x.1 = a} ≃ Fin (w a) :=
    { toFun := fun x => Fin.cast (congrArg w x.2) x.1.2
      invFun := fun j => ⟨⟨a, j⟩, rfl⟩
      left_inv := fun x => by
        rcases x with ⟨⟨b, j⟩, rfl⟩
        rfl
      right_inv := fun _ => rfl }
  rw [uprob_def, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin,
    Fintype.card_sigma]
  simp only [Fintype.card_fin]

/-- **Weighted buckets** for weights indexed by `Fin m`: the bucket sampler of
`Fin (Σ_i w i)` read through Mathlib's `finSigmaFinEquiv` (cumulative buckets: value `i` owns
the `w i` consecutive indices after `Σ_{i' < i} w i'`). Glue. -/
def weighted {m : ℕ} (w : Fin m → ℕ) (s : ℕ) : CoinSampler (RatSeed w) s :=
  ofEquiv finSigmaFinEquiv s

/-- `weighted w s = ofEquiv finSigmaFinEquiv s`. -/
theorem weighted_eq {m : ℕ} (w : Fin m → ℕ) (s : ℕ) :
    weighted w s = ofEquiv finSigmaFinEquiv s := rfl

/-- The weighted sampler fails as the bucket sampler of the total weight:
`(weighted w s).fail = (bucket (Σ_i w i) s).fail` (`fail_ofEquiv`). -/
theorem fail_weighted {m : ℕ} (w : Fin m → ℕ) (s : ℕ) :
    (weighted w s).fail = (bucket (∑ i, w i) s).fail :=
  fail_ofEquiv _ _

end TCSlib.Cryptography.CoinSampling
