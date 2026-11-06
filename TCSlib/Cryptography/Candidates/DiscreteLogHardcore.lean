/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Candidates.DiscreteLog
import TCSlib.Cryptography.NumberTheory.QuadraticResidues
import TCSlib.Cryptography.HardcoreBit.PairwiseIndependence
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The hard-core bit of the discrete logarithm

[PS10, §3.4.1]: under the discrete-log assumption, `half_{p−1}(x) = [x < (p−1)/2]` is a
hard-core predicate for the exponentiation `f_{p,g}(x) = g^x mod p` [PS10, Lemma 84.1], by the
bit-by-bit inversion of [PS10, Algorithm 84.2] with the randomized majority test of p. 85.

**The group.** The lemma, the algorithm and the proof work in the *full* group `Z_p^*` of
even order `p − 1` (the parity of the exponent is read off quadratic residuosity and
`g^{(p−1)/2} = −1`), not in the prime-order group of [PS10, Assumption 52.2]; the hypothesis is
therefore discrete-log hardness for the full-group collection (`FullDLAssumption`, the
exponentiation collection of `DiscreteLog` with `m = p − 1` and `g` a generator of `Z_p^*`),
restricted to primes `p ≡ 3 (mod 4)` so that the square roots of [PS10, Theorem 58.2] are one
modular exponentiation (decision log, open question 3).

**Two layers.** The *concrete* core (one prime `p`, one generator `g`, exact inequalities,
[Gar26]-style): the number theory behind the algorithm (`pow_half_eq_neg_one`,
`pow_mem_QR_iff`, `sq_eq_pow_two_mul_iff`, `neg_pow_eq`), the loop `dlLoop` of
Algorithm 84.2 with an oracle `O` (`dlBits` with the perfect half-oracle, `dlBits_pow`), the
majority test `majOracle` (p. 85) with its per-trial bound `uprob_trial_ge` and failure bound
`uprob_majOracle_ne_le`, the range reduction `shiftInverter` ("as we will show later", never
shown in the text) and the final inverter `dlInverter` with the bound
`invProb_dlInverter_ge`; the good-instance averaging `good_instances`. The *asymptotic*
wrapper `fullDLCollection_hardCore` packages the inverter as a non-uniform PPT.

**Deviation:** Lemma 84.1 vs Assumption 52.2: the assumption is for prime-order `G_q`, the lemma
and Algorithm 84.2 use `Z_p^*` (even order); `x ← Z_p` should be `x ← Z_{p−1}`;
"`ε = s(n)`" should be `1/s(n)`; the range reduction "as we will show later" is never shown;
the good-instance averaging over `(p, g)` is missing; the p. 86 analysis bounds
`Pr[noinc | low]` by `1/2 − ε/2`, which is the complementary event of its own increment rule
(the counter `lo` counts *disagreements* `b_i ≠ half(r_i)`, so `noinc` is the typical event
on a low instance). Concretely: `dlLoop` follows line 11 literally (the root is kept iff `A`
answers `1` = lower half, negated on `0`); `half_m(x) := [2x < m]` is a harmless strict
variant of the text's `0 ≤ x ≤ m/2` (they differ at the single point `x = m/2`, probability
`1/(p−1)`; the strict form is *not* required by the halving invariant, since the boundary
exponent `(p−1)/2` only arises as the second root of `y = 1`, whose canonical root `dlRoot`
is `1`); the majority test `majOracle` votes on agreements and resolves the text's
inconsistency, with Chebyshev's inequality for pairwise independent trials and an explicit
number `ℓ` of trials (`HardcoreBit.uprob_majority_fails_le`, [PS10, Lemma 189.8] being
garbled); generators of `Z_p^*` are restricted to `p ≡ 3 (mod 4)`; the asymptotic form takes
`p` of full length `n` except on a negligible set of the generator's coins
(`ExpGroupGen.FullLengthExcept`, run-3 audit P8-2) and the arithmetic bundle `ArithmeticFP`.
(Run-3 audit P8-3: the run-2 text claimed line 11 inverted and the strict `half` necessary;
neither is the case.)

## Main definitions

* `TCSlib.Cryptography.Candidates.expo`, `halfBit`, `IsGenerator`, `dlog` — exponentiation
  `Z_{p−1} → Z_p^*`, the predicate `half_{p−1}`, generators and the discrete logarithm.
* `TCSlib.Cryptography.Candidates.dlRoot`, `dlLoop`, `dlQueries`, `dlBits` —
  [PS10, Algorithm 84.2] with an oracle and with the perfect half-oracle.
* `TCSlib.Cryptography.Candidates.majOracle` — the randomized majority test of p. 85;
  `shiftInverter`, `dlInverter` — the range reduction and the inverter `B`.
* `TCSlib.Cryptography.Candidates.FullGroupValid`, `FullGroupGen`, `FullDLAssumption`,
  `fullDLCollection`, `halfPred`, `halfStr` — the asymptotic setting.

## Main results

* `TCSlib.Cryptography.Candidates.pow_half_eq_neg_one`, `pow_mem_QR_iff`,
  `sq_eq_pow_two_mul_iff`, `neg_pow_eq` — the number theory of p. 85 (Lem-84.1.1).
* `TCSlib.Cryptography.Candidates.dlBits_pow` — correctness of Algorithm 84.2 with a perfect
  oracle; `dlLoop_eq_dlBits` — the noisy loop agrees whenever every query is answered correctly.
* `TCSlib.Cryptography.Candidates.uprob_trial_ge` (Lem-84.1.3), `uprob_majOracle_ne_le`
  (Alg-85.a), `invProb_shiftInverter_ge` (Lem-84.1.4), `good_instances` (Lem-84.1.5),
  `invProb_dlInverter_ge` — the concrete core of [PS10, Lemma 84.1].
* `TCSlib.Cryptography.Candidates.halfStr_spec` (Lem-84.1.0),
  `TCSlib.Cryptography.Candidates.fullDLCollection_hardCore` — [PS10, Lemma 84.1].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.4.1: Lemma 84.1, Algorithm 84.2 and pp. 85–86; §2.12 Theorem 58.2; Appendix A.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5.1 (majority votes and pairwise-independent trials).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory Finset

/-! ## Exponentiation in `Z_p^*`, the predicate `half_{p−1}`, generators -/

section Concrete

variable {p : ℕ} [hp : Fact p.Prime] [NeZero (p - 1)]

/-- **The exponentiation function** `f_{p,g}(x) = g^x mod p` on `Z_{p−1}` [PS10, Lemma 84.1]. -/
def expo (g : (ZMod p)ˣ) (x : ZMod (p - 1)) : (ZMod p)ˣ := g ^ x.val

/-- **The predicate `half_m`** [PS10, p. 84, "`half_n(x)` is equal to `1` if and only if
`0 ≤ x ≤ n/2`"]: `half_m(x) = 1` iff `2x < m` (lower half).

**Deviation:** strict inequality at the boundary (`x = m/2` counts as upper half), a harmless
variant of the text's `x ≤ m/2`: the two differ at the single point `x = m/2` (for `m = p − 1`
even), of probability `1/(p−1)` under a uniform exponent, and Algorithm 84.2 is correct with
either (the boundary exponent `(p−1)/2` only arises as the second root `−1` of `y = 1`, and
`dlRoot g 1 = 1`). Run-3 audit P8-3 (the run-2 docstring called the strict form necessary). -/
def halfBit (m : ℕ) (x : ZMod m) : Bool := decide (2 * x.val < m)

/-- `g` is a *generator* of `Z_p^*` [PS10, Definition 52.1]: every unit is a power of `g`. -/
def IsGenerator (g : (ZMod p)ˣ) : Prop := ∀ x, x ∈ Subgroup.zpowers g

omit [NeZero (p - 1)] in
/-- A generator of `Z_p^*` has order `p − 1`. -/
theorem IsGenerator.orderOf_eq {g : (ZMod p)ˣ} (hg : IsGenerator g) : orderOf g = p - 1 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]

/-- **Exponentiation by a generator is injective on `Z_{p−1}`** [PS10, Theorem 52.3 remark]. -/
theorem expo_injective {g : (ZMod p)ˣ} (hg : IsGenerator g) : Function.Injective (expo g) := by
  intro x y h
  have h1 := pow_eq_pow_iff_modEq.1 h
  rw [hg.orderOf_eq] at h1
  apply ZMod.val_injective
  unfold Nat.ModEq at h1
  rwa [Nat.mod_eq_of_lt (ZMod.val_lt x), Nat.mod_eq_of_lt (ZMod.val_lt y)] at h1

/-- **Exponentiation by a generator is a bijection `Z_{p−1} → Z_p^*`** (the discrete-log
collection is a collection of permutations, [PS10, p. 53]). -/
theorem expo_bijective {g : (ZMod p)ˣ} (hg : IsGenerator g) : Function.Bijective (expo g) :=
  (Fintype.bijective_iff_injective_and_card _).2 ⟨expo_injective hg, by rw [ZMod.card, ZMod.card_units]⟩

/-- **The discrete logarithm** `dlog_g(y)`: the inverse of `expo g` (`Function.invFun`). -/
noncomputable def dlog (g : (ZMod p)ˣ) (y : (ZMod p)ˣ) : ZMod (p - 1) := Function.invFun (expo g) y

/-- `g^{dlog_g y} = y` for a generator `g`. -/
theorem expo_dlog {g : (ZMod p)ˣ} (hg : IsGenerator g) (y : (ZMod p)ˣ) : expo g (dlog g y) = y :=
  Function.invFun_eq ((expo_bijective hg).2 y)

/-- `dlog_g (g^x) = x` for a generator `g`. -/
theorem dlog_expo {g : (ZMod p)ˣ} (hg : IsGenerator g) (x : ZMod (p - 1)) : dlog g (expo g x) = x :=
  expo_injective hg (expo_dlog hg _)

/-! ### The number theory of p. 85 (Lem-84.1.1) -/

omit [NeZero (p - 1)] in
/-- For an odd prime, `(p − 1)/2 ≠ 0` and `2 · ((p − 1)/2) = p − 1`. -/
theorem two_mul_half (hp2 : p ≠ 2) : 2 * ((p - 1) / 2) = p - 1 ∧ 0 < (p - 1) / 2 := by
  have h2 := hp.out.two_le
  have hodd := hp.out.eq_two_or_odd'.resolve_left hp2
  obtain ⟨k, hk⟩ := hodd
  omega

omit [NeZero (p - 1)] in
/-- `−1 ≠ 1` in `Z_p^*` for an odd prime. -/
theorem neg_one_ne_one_units (hp2 : p ≠ 2) : (-1 : (ZMod p)ˣ) ≠ 1 := by
  haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)⟩
  intro h
  exact ZMod.neg_one_ne_one (by simpa [Units.ext_iff] using h)

omit [NeZero (p - 1)] in
/-- **`g^{(p−1)/2} = −1` for a generator `g` of `Z_p^*`** [PS10, p. 85, "recall that
`g^{p/2} = −1 mod p`"].

**Proof sketch.** `(g^{(p−1)/2})² = g^{p−1} = 1`, so `g^{(p−1)/2} = ±1`
(`Units.sq_eq_sq_iff_eq_or_eq_neg`); `+1` would make the order of `g` divide `(p−1)/2 < p − 1`. -/
theorem pow_half_eq_neg_one (hp2 : p ≠ 2) {g : (ZMod p)ˣ} (hg : IsGenerator g) :
    g ^ ((p - 1) / 2) = -1 := by
  obtain ⟨h2, hpos⟩ := two_mul_half hp2
  have hsq : (g ^ ((p - 1) / 2)) ^ 2 = (1 : (ZMod p)ˣ) ^ 2 := by
    rw [← pow_mul, mul_comm, h2, ZMod.units_pow_card_sub_one_eq_one, one_pow]
  rcases Units.sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exfalso
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hg.orderOf_eq] at hdvd
    have := Nat.le_of_dvd hpos hdvd
    omega
  · exact h

omit [NeZero (p - 1)] in
/-- **`g^e` is a square iff `e` is even** [PS10, p. 85, Algorithm 84.2 lines 3–7]: the parity
of the discrete logarithm is quadratic residuosity.

**Proof sketch.** Euler's criterion (`ZMod.euler_criterion_units`): `g^e ∈ QR_p` iff
`(g^e)^{(p−1)/2} = (g^{(p−1)/2})^e = (−1)^e = 1`, iff `e` is even (`−1 ≠ 1`). -/
theorem pow_mem_QR_iff (hp2 : p ≠ 2) {g : (ZMod p)ˣ} (hg : IsGenerator g) (e : ℕ) :
    g ^ e ∈ QR p ↔ Even e := by
  have hhalf : p / 2 = (p - 1) / 2 := by
    have := hp.out.two_le
    obtain ⟨k, hk⟩ := hp.out.eq_two_or_odd'.resolve_left hp2
    omega
  rw [mem_QR_iff, ZMod.euler_criterion_units, hhalf, ← pow_mul, mul_comm, pow_mul,
    pow_half_eq_neg_one hp2 hg]
  exact neg_one_pow_eq_one_iff_even (neg_one_ne_one_units hp2)

omit [NeZero (p - 1)] in
/-- **The square roots of `g^{2x}` are `g^x` and `−g^x`** [PS10, p. 85, "`y` has two square
roots: `g^x` and `g^{x + p/2}`"]. -/
theorem sq_eq_pow_two_mul_iff (g z : (ZMod p)ˣ) (x : ℕ) :
    z ^ 2 = g ^ (2 * x) ↔ z = g ^ x ∨ z = -(g ^ x) := by
  rw [mul_comm, pow_mul]
  exact Units.sq_eq_sq_iff_eq_or_eq_neg

omit [NeZero (p - 1)] in
/-- **`−g^x = g^{x + (p−1)/2}`** [PS10, p. 85]: the second root has the larger exponent. -/
theorem neg_pow_eq (hp2 : p ≠ 2) {g : (ZMod p)ˣ} (hg : IsGenerator g) (x : ℕ) :
    -(g ^ x) = g ^ (x + (p - 1) / 2) := by
  rw [pow_add, pow_half_eq_neg_one hp2 hg, mul_neg_one]

/-! ### Algorithm 84.2 -/

/-- **The root step of [PS10, Algorithm 84.2]** (lines 3–9): make `y` a square by dividing by
`g` if necessary, then take the square root `y^{(p+1)/4}` of [PS10, Theorem 58.2]
(`NumberTheory.sq_pow_div_four_succ`, valid for `p ≡ 3 (mod 4)`). -/
noncomputable def dlRoot (g y : (ZMod p)ˣ) : (ZMod p)ˣ :=
  (if y ∈ QR p then y else y * g⁻¹) ^ (p / 4 + 1)

/-- **The loop of [PS10, Algorithm 84.2]** with an oracle `O` for `half_{p−1}` of the
discrete logarithm, answering with per-round coins `κ`: for `k` rounds, record the parity bit
(`1` iff `y` is a non-square), take the root `dlRoot g y`, keep it if the oracle says
"lower half" (`true`) and its negative otherwise, and recurse; the output is the exponent
rebuilt from its bits (least significant first).

The root selection is the text's line 11 read literally: "IF `b = 0` THEN `y_{k−1} ← −y_{k−1}`"
keeps the root exactly when `A` answers `1` (= lower half, `half`'s convention) and negates it
otherwise (run-3 audit P8-3: the run-2 docstring wrongly called this a deviation).

**Deviation:** `k` is an explicit round count (the text's `k = |p|` decremented to `0`). -/
noncomputable def dlLoop (g : (ZMod p)ˣ) {κ : Type*} (O : (ZMod p)ˣ → κ → Bool) :
    (k : ℕ) → (ZMod p)ˣ → (Fin k → κ) → ℕ
  | 0, _, _ => 0
  | k + 1, y, c =>
    2 * dlLoop g O k (if O (dlRoot g y) (c 0) then dlRoot g y else -dlRoot g y) (fun j => c j.succ) +
      (if y ∈ QR p then 0 else 1)

/-- The sequence of roots submitted to the oracle by `dlLoop` (round `j` queries the root
taken at round `j`); the union bound over rounds is stated on these queries. -/
noncomputable def dlQueries (g : (ZMod p)ˣ) {κ : Type*} (O : (ZMod p)ˣ → κ → Bool) :
    (k : ℕ) → (ZMod p)ˣ → (Fin k → κ) → Fin k → (ZMod p)ˣ
  | 0, _, _ => Fin.elim0
  | k + 1, y, c =>
    Fin.cons (dlRoot g y)
      (dlQueries g O k (if O (dlRoot g y) (c 0) then dlRoot g y else -dlRoot g y) (fun j => c j.succ))

/-- **The perfect oracle**: `half_{p−1}` of the discrete logarithm. -/
noncomputable def halfOracle (g y : (ZMod p)ˣ) : Bool := halfBit (p - 1) (dlog g y)

/-- **Algorithm 84.2 with a perfect oracle** [PS10, Algorithm 84.2, "let us first assume that
`A` is always correct"]: `k` rounds of `dlLoop` driven by `halfOracle`. -/
noncomputable def dlBits (g : (ZMod p)ˣ) (k : ℕ) (y : (ZMod p)ˣ) : ℕ :=
  dlLoop g (fun y (_ : Unit) => halfOracle g y) k y (fun _ => ())

omit [NeZero (p - 1)] in
/-- Unfolding: `dlLoop` at `k + 1`. -/
theorem dlLoop_succ (g : (ZMod p)ˣ) {κ : Type*} (O : (ZMod p)ˣ → κ → Bool) (k : ℕ)
    (y : (ZMod p)ˣ) (c : Fin (k + 1) → κ) :
    dlLoop g O (k + 1) y c =
      2 * dlLoop g O k (if O (dlRoot g y) (c 0) then dlRoot g y else -dlRoot g y) (fun j => c j.succ) +
        (if y ∈ QR p then 0 else 1) := rfl

omit [NeZero (p - 1)] in
/-- Unfolding: the first query of `dlQueries` is the root of the input. -/
theorem dlQueries_zero (g : (ZMod p)ˣ) {κ : Type*} (O : (ZMod p)ˣ → κ → Bool) (k : ℕ)
    (y : (ZMod p)ˣ) (c : Fin (k + 1) → κ) : dlQueries g O (k + 1) y c 0 = dlRoot g y := by
  simp [dlQueries]

omit [NeZero (p - 1)] in
/-- Unfolding: the later queries of `dlQueries` are those of the recursive call. -/
theorem dlQueries_succ (g : (ZMod p)ˣ) {κ : Type*} (O : (ZMod p)ˣ → κ → Bool) (k : ℕ)
    (y : (ZMod p)ˣ) (c : Fin (k + 1) → κ) (j : Fin k) :
    dlQueries g O (k + 1) y c j.succ =
      dlQueries g O k (if O (dlRoot g y) (c 0) then dlRoot g y else -dlRoot g y) (fun j => c j.succ) j := by
  simp [dlQueries]

omit [NeZero (p - 1)] in
/-- **The noisy loop agrees with the perfect one whenever every query is answered
correctly**: if `O` answers `half_{p−1}(dlog)` on each of its `k` queries, then
`dlLoop g O k y c = dlBits g k y`.

**Proof sketch.** Induction on `k` generalizing `y, c`: both loops query `dlRoot g y` first
(`dlQueries_zero`), the hypothesis at `0` makes them select the same root, and the hypothesis
at `j.succ` (`dlQueries_succ`) is the hypothesis of the recursive call. -/
theorem dlLoop_eq_dlBits (g : (ZMod p)ˣ) {κ : Type*} (O : (ZMod p)ˣ → κ → Bool) :
    ∀ (k : ℕ) (y : (ZMod p)ˣ) (c : Fin k → κ),
      (∀ j, O (dlQueries g O k y c j) (c j) = halfOracle g (dlQueries g O k y c j)) →
        dlLoop g O k y c = dlBits g k y
  | 0, _, _, _ => rfl
  | k + 1, y, c, h => by
    have h0 := h 0
    rw [dlQueries_zero] at h0
    rw [dlLoop_succ, dlBits, dlLoop_succ, h0]
    congr 2
    rw [← dlBits]
    apply dlLoop_eq_dlBits g O k
    intro j
    have hj := h j.succ
    rw [dlQueries_succ, h0] at hj
    exact hj

omit [NeZero (p - 1)] in
/-- The root step on a power of a generator: `dlRoot g (g^e)` is `g^{⌊e/2⌋}` or its negative
(for `p ≡ 3 (mod 4)`). For even `e` the root is taken of `g^e = g^{2⌊e/2⌋}`, for odd `e` of
`g^e · g⁻¹ = g^{2⌊e/2⌋}`, a square (`pow_mem_QR_iff`) whose root squares back to it
(`sq_pow_div_four_succ`), so `sq_eq_pow_two_mul_iff` applies. -/
private theorem dlb_dlRoot_pow (hp3 : p % 4 = 3) {g : (ZMod p)ˣ} (hg : IsGenerator g) (e : ℕ) :
    dlRoot g (g ^ e) = g ^ (e / 2) ∨ dlRoot g (g ^ e) = -(g ^ (e / 2)) := by
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp3
  rw [← sq_eq_pow_two_mul_iff]
  unfold dlRoot
  by_cases hq : g ^ e ∈ QR p
  · rw [if_pos hq, sq_pow_div_four_succ hp3 hq]
    have he : Even e := (pow_mem_QR_iff hp2 hg e).1 hq
    rw [Nat.two_mul_div_two_of_even he]
  · rw [if_neg hq]
    have he : ¬ Even e := fun h => hq ((pow_mem_QR_iff hp2 hg e).2 h)
    have hodd : e = 2 * (e / 2) + 1 := by
      obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.1 he
      omega
    have hge : g ^ e * g⁻¹ = g ^ (2 * (e / 2)) := by
      conv_lhs => rw [hodd, pow_succ]
      rw [mul_inv_cancel_right]
    rw [hge, sq_pow_div_four_succ hp3 ((pow_mem_QR_iff hp2 hg _).2 (even_two_mul _))]

/-- The perfect oracle on a power: `halfOracle g (g^a) = half_{p−1}(a)` for `a < p − 1`
(`dlog_expo`). -/
private theorem dlb_halfOracle_pow_eq {g : (ZMod p)ˣ} (hg : IsGenerator g) {a : ℕ}
    (ha : a < p - 1) : halfOracle g (g ^ a) = halfBit (p - 1) (a : ZMod (p - 1)) := by
  have h1 : g ^ a = expo g (a : ZMod (p - 1)) := by
    unfold expo; rw [ZMod.val_cast_of_lt ha]
  unfold halfOracle
  rw [h1, dlog_expo hg]

/-- The perfect oracle on a power, as a comparison: `halfOracle g (g^a) = [2a < p − 1]` for
`a < p − 1`. -/
private theorem dlb_halfOracle_pow {g : (ZMod p)ˣ} (hg : IsGenerator g) {a : ℕ} (ha : a < p - 1) :
    halfOracle g (g ^ a) = decide (2 * a < p - 1) := by
  rw [dlb_halfOracle_pow_eq hg ha]; unfold halfBit; rw [ZMod.val_cast_of_lt ha]

/-- **The perfect oracle keeps the root `g^{⌊e/2⌋}`** (the step of `dlBits_pow`): for
`e < p − 1`, the root kept by one round of Algorithm 84.2 on `g^e` is `g^{⌊e/2⌋}`, because the
other root `−g^{⌊e/2⌋} = g^{⌊e/2⌋ + (p−1)/2}` lies in the upper half (`neg_pow_eq`). -/
private theorem dlb_keep (hp3 : p % 4 = 3) {g : (ZMod p)ˣ} (hg : IsGenerator g) {e : ℕ}
    (he : e < p - 1) :
    (if halfOracle g (dlRoot g (g ^ e)) then dlRoot g (g ^ e) else -dlRoot g (g ^ e)) =
      g ^ (e / 2) := by
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp3
  obtain ⟨h2, hpos⟩ := two_mul_half (p := p) hp2
  have ha : e / 2 < p - 1 := by omega
  have hlow : halfOracle g (g ^ (e / 2)) = true := by
    rw [dlb_halfOracle_pow hg ha]; simp; omega
  rcases dlb_dlRoot_pow hp3 hg e with h | h
  · rw [h, hlow, if_pos rfl]
  · have hhi : halfOracle g (-(g ^ (e / 2))) = false := by
      rw [neg_pow_eq hp2 hg, dlb_halfOracle_pow hg (by omega)]; simp; omega
    rw [h, hhi, if_neg (by simp), neg_neg]

omit [NeZero (p - 1)] in
/-- **Correctness of Algorithm 84.2 with a perfect oracle** [PS10, p. 85, "we can iteratively
divide, take square roots, and then choose the root with smaller discrete log until we
eventually end up at `1`"]: for `p ≡ 3 (mod 4)`, a generator `g` and `e < p − 1` with
`e < 2^k`, `dlBits g k (g^e) = e`.

**Proof sketch.** Induction on `k` generalizing `e`. At `k = 0`, `e = 0`. At `k + 1`: if `e`
is even, `g^e ∈ QR_p` (`pow_mem_QR_iff`) and `dlRoot g (g^e) = (g^e)^{(p+1)/4}` is a root of
`g^e = g^{2(e/2)}` (`sq_pow_div_four_succ`), hence `g^{e/2}` or `−g^{e/2} = g^{e/2 + (p−1)/2}`
(`sq_eq_pow_two_mul_iff`, `neg_pow_eq`); the perfect oracle answers `true` on `g^{e/2}`
(`dlog_expo`, `2(e/2) ≤ e < p − 1`) and `false` on the other root (its exponent
`e/2 + (p−1)/2 < p − 1` has `2 · (e/2 + (p−1)/2) ≥ p − 1`), so the kept root is `g^{e/2}`;
the recorded bit is `0`, the recursive call returns `e/2 < 2^k`, and `2(e/2) + 0 = e`. If `e`
is odd, `g^e ∉ QR_p`, the loop divides by `g` (`g^e · g⁻¹ = g^{e−1}`, even exponent) and the
same argument gives `2((e−1)/2) + 1 = e`. -/
theorem dlBits_pow (hp3 : p % 4 = 3) {g : (ZMod p)ˣ} (hg : IsGenerator g) {k e : ℕ}
    (he : e < p - 1) (hk : e < 2 ^ k) : dlBits g k (g ^ e) = e := by
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp3
  obtain ⟨h2, hpos⟩ := two_mul_half (p := p) hp2
  haveI : NeZero (p - 1) := ⟨by omega⟩
  induction k generalizing e with
  | zero => simp at hk; subst hk; rfl
  | succ k ih =>
    unfold dlBits
    rw [dlLoop_succ]
    -- the perfect oracle keeps the root `g^{⌊e/2⌋}`
    have hkeep := dlb_keep hp3 hg he
    -- the recursive call returns `⌊e/2⌋`, and the recorded bit is the parity of `e`
    rw [hkeep, ← dlBits, ih (by omega) (by rw [pow_succ] at hk; omega)]
    by_cases hq : g ^ e ∈ QR p
    · rw [if_pos hq]
      have := Nat.two_mul_div_two_of_even ((pow_mem_QR_iff hp2 hg e).1 hq); omega
    · rw [if_neg hq]
      obtain ⟨j, hj⟩ := Nat.not_even_iff_odd.1 (fun h => hq ((pow_mem_QR_iff hp2 hg e).2 h))
      omega

/-! ### The majority test of p. 85 and the range reduction -/

/-- **The randomized majority test** replacing line 10 of Algorithm 84.2 [PS10, p. 85]: on
the root `y`, draw `ℓ` fresh `r_i ← Z_{p−1}` and coins for `A`, set `z_i = y · g^{r_i}`, and vote
"lower half" (`true`) for each `i` with `A(z_i) = half_{p−1}(r_i)`; decide by majority.

The text's counter `lo` is incremented when `(b_i = 0 ∧ r_i < p/2) ∨ (b_i = 1 ∧ r_i ≥ p/2)`,
i.e. on a *disagreement* `b_i ≠ half(r_i)`, and `b = 0` (upper half) is chosen when `lo > ℓ/2`:
voting on agreements and deciding "lower half" by majority is the same test. Its analysis on
p. 86 bounds `Pr[noinc | low]` by `1/2 − ε/2`, which is the complementary event of this
increment rule (source error 27; run-3 audit P8-3) — `uprob_trial_ge` states the correct
direction.

**Deviation:** ties go to "upper half" (`HardcoreBit.majority`; the text gives `b = 1` on a
tie `lo = ℓ/2`). -/
def majOracle (g : (ZMod p)ˣ) {ρ : Type*} [Fintype ρ] (A : (ZMod p)ˣ → ρ → Bool) (ℓ : ℕ) :
    (ZMod p)ˣ → (Fin ℓ → ZMod (p - 1) × ρ) → Bool :=
  fun y c => HardcoreBit.majority fun i =>
    decide (A (y * g ^ (c i).1.val) (c i).2 = halfBit (p - 1) (c i).1)

/-- Counting through the canonical representative: if every `v < m` with `P v` lies in `S`,
then `Pr_{r ← Z_m}[P r.val] ≤ |S|/m`. -/
private theorem dlb_uprob_val_le (m : ℕ) [NeZero m] (P : ℕ → Prop) (S : Finset ℕ)
    (h : ∀ v < m, P v → v ∈ S) : uprob (fun r : ZMod m => P r.val) ≤ (S.card : ℝ) / m := by
  classical
  rw [uprob_eq_card_filter, ZMod.card]
  gcongr
  refine Finset.card_le_card_of_injOn (fun r => r.val) (fun r hr => ?_) ?_
  · simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hr
    exact h _ (ZMod.val_lt r) hr
  · intro a _ b _ hab; exact ZMod.val_injective m hab

/-- The windows of `uprob_trial_ge` in `ℕ`: for `m = 2h`, an exponent `e < m` equal to `d`
or `h + d` with `d < h`, and `v < m` outside `[h − d, h) ∪ [m − d, m)`, the half-bit of
`(e + v) mod m` agrees with that of `v` exactly when `e` is in the lower half. -/
private theorem dlb_window {m h e d v : ℕ} (hm : m = 2 * h) (hd : d < h)
    (he : e = d ∨ e = h + d) (hv : v < m) (hS : v ∉ Ico (h - d) h ∪ Ico (m - d) m) :
    ((2 * ((e + v) % m) < m ↔ 2 * v < m) ↔ 2 * e < m) := by
  simp only [mem_union, mem_Ico, not_or, not_and, not_lt] at hS
  by_cases hlt : e + v < m
  · rw [Nat.mod_eq_of_lt hlt]; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega


/-- Multiplying a power: `g^e · g^{r.val} = expo g (e + r)` for `e < p − 1` and a generator. -/
private theorem dlb_pow_mul_pow_val {g : (ZMod p)ˣ} (hg : IsGenerator g) {e : ℕ} (he : e < p - 1)
    (r : ZMod (p - 1)) : g ^ e * g ^ r.val = expo g ((e : ZMod (p - 1)) + r) := by
  unfold expo
  rw [← pow_add, ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt he,
    show (e + r.val) % (p - 1) = (e + r.val) % orderOf g by rw [hg.orderOf_eq], pow_mod_orderOf]

/-- A predictor's success is at most one, so its advantage `ε` is at most `1/2`. -/
private theorem dlb_eps_le {g : (ZMod p)ˣ} {ρ : Type*} [Fintype ρ]
    (A : (ZMod p)ˣ → ρ → Bool) {ε : ℝ} (hA : 1 / 2 + ε ≤ predProb (expo g) (halfBit (p - 1)) A) :
    ε ≤ 1 / 2 := by
  have := uprob_le_one fun z : ZMod (p - 1) × ρ => A (expo g z.1) z.2 = halfBit (p - 1) z.1
  rw [← predProb_def] at this
  linarith

/-- **One trial of the majority test is correct with probability at least `1/2 + ε/2`**
(Lem-84.1.3, [PS10, p. 86, "`Pr[noinc | low(y_{k−1})] ≤ 1/2 − ε + 2(ε/4) = 1/2 − ε/2`"]): if
`A` predicts `half_{p−1}` from `g^x` with probability at least `1/2 + ε` over uniform `x`, and
the exponent `e` of the root lies in `[0, s)` or in `[(p−1)/2, (p−1)/2 + s)` with
`4s ≤ ε(p−1)`, then a trial on `g^e` votes `half_{p−1}(e)` with probability at least `1/2 + ε/2`.

**Proof sketch.** The exponent of `z = g^e · g^r` is `e + r` in `Z_{p−1}` and `r ↦ e + r` is a
bijection (`HardcoreBit.pushesUniform_add_right`), so `Pr_{r, c}[A(z, c) = half(e + r)] =
predProb (expo g) half A ≥ 1/2 + ε` (`uprob_comp_equiv`). For `e < s`, `half(e + r) ≠ half(r)`
only for `r ∈ [(p−1)/2 − e, (p−1)/2) ∪ [p − 1 − e, p − 1)`, at most `2s` values, probability
`≤ 2s/(p−1) ≤ ε/2` (`uprob_eq_card_filter`, `Finset.card_le_card`); for `e` in the upper
window, `e = (p−1)/2 + e'` and `half(e + r) ≠ ¬half(r)` only on `2e' ≤ 2s` values. The union
bound `uprob_or_le` (through `uprob_not`) gives
`Pr[vote = half(e)] ≥ 1/2 + ε − ε/2`. -/
theorem uprob_trial_ge {g : (ZMod p)ˣ} (hg : IsGenerator g) {ρ : Type*} [Fintype ρ]
    (A : (ZMod p)ˣ → ρ → Bool) {ε : ℝ} (hA : 1 / 2 + ε ≤ predProb (expo g) (halfBit (p - 1)) A)
    {s : ℕ} (hs : 4 * (s : ℝ) ≤ ε * ((p : ℝ) - 1)) {e : ℕ} (he' : e < p - 1)
    (he : e < s ∨ ((p - 1) / 2 ≤ e ∧ e < (p - 1) / 2 + s)) :
    1 / 2 + ε / 2 ≤ uprob fun c : ZMod (p - 1) × ρ =>
      decide (A (g ^ e * g ^ c.1.val) c.2 = halfBit (p - 1) c.1) = halfBit (p - 1) (e : ZMod (p - 1)) := by
  classical
  have hε2 := dlb_eps_le A hA
  have hp1 : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
    have := NeZero.ne (p - 1); exact_mod_cast Nat.pos_of_ne_zero this
  have hcast : ((p : ℝ) - 1) = ((p - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
  rw [hcast] at hs
  -- `s ≥ 1` (a window is nonempty), hence `p − 1 ≥ 8` and `p` is odd
  have hs1 : 1 ≤ s := by omega
  have hp8 : 8 * s ≤ p - 1 := by
    have : (8 * s : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by nlinarith
    exact_mod_cast this
  have hp2 : p ≠ 2 := by rintro rfl; omega
  obtain ⟨h2, -⟩ := two_mul_half (p := p) hp2
  set m := p - 1 with hm
  set h := (p - 1) / 2 with hh
  -- the predictor is uniform-coined; an empty coin type makes `hA` infeasible
  rcases isEmpty_or_nonempty ρ with hρ | hρ
  · exfalso
    have h0 : predProb (expo g) (halfBit (p - 1)) A = 0 := by
      rw [predProb_def, uprob_def, Fintype.card_eq_zero, Nat.cast_zero, div_zero]
    have : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    nlinarith
  -- the window parameter `d < s` with `e = d` or `e = h + d`
  obtain ⟨d, hds, hed⟩ : ∃ d, d < s ∧ (e = d ∨ e = h + d) := by
    rcases he with he | he
    · exact ⟨e, he, Or.inl rfl⟩
    · exact ⟨e - h, by omega, Or.inr (by omega)⟩
  have hdh : d < h := by omega
  -- the correct-prediction event, transported along `r ↦ e + r`
  let correct : ZMod m × ρ → Prop := fun c =>
    A (expo g ((e : ZMod m) + c.1)) c.2 = halfBit m ((e : ZMod m) + c.1)
  let good : ZMod m → Prop := fun r =>
    decide (halfBit m ((e : ZMod m) + r) = halfBit m r) = halfBit m (e : ZMod m)
  have hcorr : uprob correct = predProb (expo g) (halfBit m) A := by
    rw [predProb_def]
    exact uprob_comp_equiv ((Equiv.addLeft (e : ZMod m)).prodCongr (Equiv.refl ρ))
      (fun z : ZMod m × ρ => A (expo g z.1) z.2 = halfBit m z.1)
  -- the bad set has at most `2d ≤ 2s` elements
  have hbad : uprob (fun c : ZMod m × ρ => ¬ good c.1) ≤ ε / 2 := by
    rw [uprob_fst (fun r => ¬ good r)]
    let P : ℕ → Prop := fun v => ¬ ((2 * ((e + v) % m) < m ↔ 2 * v < m) ↔ 2 * e < m)
    have hpt : ∀ r : ZMod m, ¬ good r → P r.val := by
      intro r hr hiff
      apply hr
      simp only [good, halfBit, ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt he']
      rw [decide_eq_decide, decide_eq_decide]
      exact hiff
    refine (uprob_mono hpt).trans ((dlb_uprob_val_le m P (Ico (h - d) h ∪ Ico (m - d) m) ?_).trans ?_)
    · intro v hv hP
      by_contra hS
      exact hP (dlb_window (by omega) hdh hed hv hS)
    · have hc : (Ico (h - d) h ∪ Ico (m - d) m).card ≤ 2 * s := by
        refine (card_union_le _ _).trans ?_
        rw [Nat.card_Ico, Nat.card_Ico]; omega
      rw [div_le_iff₀ hp1]
      have : ((Ico (h - d) h ∪ Ico (m - d) m).card : ℝ) ≤ 2 * s := by exact_mod_cast hc
      nlinarith
  -- on `correct ∧ good` the vote is `half(e)`
  have hsub : ∀ c : ZMod m × ρ, correct c → good c.1 →
      decide (A (g ^ e * g ^ c.1.val) c.2 = halfBit m c.1) = halfBit m (e : ZMod m) := by
    intro c hc hg'
    rw [dlb_pow_mul_pow_val hg he', hc]
    exact hg'
  have hor : uprob correct ≤ uprob (fun c : ZMod m × ρ =>
      decide (A (g ^ e * g ^ c.1.val) c.2 = halfBit m c.1) = halfBit m (e : ZMod m)) +
      uprob (fun c : ZMod m × ρ => ¬ good c.1) := by
    refine (uprob_mono fun c hc => ?_).trans (uprob_or_le _ _)
    by_cases hg' : good c.1
    · exact Or.inl (hsub c hc hg')
    · exact Or.inr hg'
  rw [hcorr] at hor
  linarith

/-- **The majority test fails with probability at most `1/(ε² ℓ)`** (Alg-85.a, [PS10, p. 86,
"by setting the number of samples `ℓ = (1/ε)²`, then by the corollary of the Chernoff bound …
`b` will be correct with probability very close to `1`"]) on a root `g^e` whose exponent lies
in the windows of `uprob_trial_ge`.

**Deviation:** Chebyshev's inequality for pairwise independent trials
(`HardcoreBit.uprob_majority_fails_le`, [PS10, Appendix A, p. 189]) with the explicit bound
`1/(4 (ε/2)² ℓ)`, instead of the garbled [PS10, Lemma 189.8].

**Proof sketch.** The `ℓ` votes are functions of the coordinates `c i` of a uniform tuple,
hence pairwise independent (`HardcoreBit.pairwiseUniform_eval`,
`PairwiseUniform.pairwiseIndep`) with the "correct vote" probability `≥ 1/2 + ε/2` each
(`uprob_trial_ge` transported by `pushesUniform_eval`); if the majority is wrong then at most
half of the votes are correct (`two_mul_card_le_of_majority_ne`), whose probability is
`≤ 1/(4 (ε/2)² ℓ) = 1/(ε² ℓ)`. -/
theorem uprob_majOracle_ne_le {g : (ZMod p)ˣ} (hg : IsGenerator g) {ρ : Type*} [Fintype ρ]
    [Nonempty ρ] (A : (ZMod p)ˣ → ρ → Bool) {ε : ℝ} (hε : 0 < ε)
    (hA : 1 / 2 + ε ≤ predProb (expo g) (halfBit (p - 1)) A) {s : ℕ}
    (hs : 4 * (s : ℝ) ≤ ε * ((p : ℝ) - 1)) {ℓ : ℕ} (hℓ : 0 < ℓ) {e : ℕ} (he' : e < p - 1)
    (he : e < s ∨ ((p - 1) / 2 ≤ e ∧ e < (p - 1) / 2 + s)) :
    uprob (fun c : Fin ℓ → ZMod (p - 1) × ρ =>
      majOracle g A ℓ (g ^ e) c ≠ halfBit (p - 1) (e : ZMod (p - 1))) ≤ 1 / (ε ^ 2 * ℓ) := by
  classical
  -- the per-trial "correct vote" bit, a function of one coordinate
  let H : ZMod (p - 1) × ρ → Bool := fun z =>
    decide (decide (A (g ^ e * g ^ z.1.val) z.2 = halfBit (p - 1) z.1) = halfBit (p - 1) (e : ZMod (p - 1)))
  let X : Fin ℓ → (Fin ℓ → ZMod (p - 1) × ρ) → Bool := fun i c => H (c i)
  have hX : HardcoreBit.PairwiseIndep X :=
    HardcoreBit.PairwiseUniform.pairwiseIndep HardcoreBit.pairwiseUniform_eval (fun _ => H)
  have hp' : ∀ i, 1 / 2 + ε / 2 ≤ uprob (fun c => X i c = true) := by
    intro i
    rw [(HardcoreBit.pushesUniform_eval i).uprob_eq (fun z => H z = true)]
    simp only [H, decide_eq_true_eq]
    exact uprob_trial_ge hg A hA hs he' he
  have hcard : 0 < Fintype.card (Fin ℓ) := by rw [Fintype.card_fin]; exact hℓ
  have key := HardcoreBit.uprob_majority_fails_le hX (by positivity : (0 : ℝ) < ε / 2) hcard hp'
  rw [Fintype.card_fin] at key
  refine (uprob_mono fun c hc => ?_).trans (key.trans (le_of_eq ?_))
  · unfold majOracle at hc
    have := HardcoreBit.two_mul_card_le_of_majority_ne _ _ hc
    simpa [X, H] using this
  · ring

/-- **The range reduction** (Lem-84.1.4, [PS10, p. 85, "such an algorithm suffices to solve the
discrete log problem, since we can guess and map any instance into this range" — never
shown]): from a solver `B₀` for instances with exponent in `[0, s)`, the inverter that guesses
`t ← [0, T)`, runs `B₀` on `y · g^{−ts}` and returns `B₀(…) + ts`. -/
def shiftInverter (g : (ZMod p)ˣ) {ρ' : Type*} (B₀ : (ZMod p)ˣ → ρ' → ℕ) (s T : ℕ) :
    (ZMod p)ˣ → Fin T × ρ' → ZMod (p - 1) :=
  fun y c => ((B₀ (y * (g ^ (c.1.val * s))⁻¹) c.2 : ℕ) : ZMod (p - 1)) + ((c.1.val * s : ℕ) : ZMod (p - 1))

/-- The range reduction on a correct guess: if `t = ⌊x/s⌋` and `B₀` recovers `x mod s` from
`g^{x mod s}`, the shifted inverter outputs `x`. -/
private theorem dlb_shiftInverter_eq (g : (ZMod p)ˣ) {ρ' : Type*} (B₀ : (ZMod p)ˣ → ρ' → ℕ)
    {s T : ℕ} (x : ZMod (p - 1)) (t : Fin T) (c : ρ') (ht : t.val = x.val / s)
    (hB : B₀ (g ^ (x.val % s)) c = x.val % s) :
    shiftInverter g B₀ s T (expo g x) (t, c) = x := by
  unfold shiftInverter expo
  have hsplit : g ^ x.val * (g ^ (t.val * s))⁻¹ = g ^ (x.val % s) := by
    rw [ht, show g ^ x.val = g ^ (x.val / s * s) * g ^ (x.val % s) by
      rw [← pow_add, Nat.div_add_mod' x.val s]]
    rw [mul_comm (g ^ (x.val / s * s)) (g ^ (x.val % s)), mul_assoc, mul_inv_cancel, mul_one]
  simp only
  rw [hsplit, hB, ht, ← Nat.cast_add, Nat.mod_add_div' x.val s, ZMod.natCast_zmod_val]

/-- **The range reduction succeeds with probability at least `(1 − δ)/T`** (Lem-84.1.4): if
`B₀` recovers every exponent `e' < s` from `g^{e'}` with probability at least `1 − δ`, and
`T s ≥ p − 1`, then `shiftInverter g B₀ s T` inverts `expo g` with probability at least
`(1 − δ)/T`.

**Proof sketch.** For `y = g^e` (`e < p − 1`) the guess `t = ⌊e/s⌋ < T` has probability `1/T`
(`pushesUniform_fst`, `uprob_eq_one_div_card`); then `y · g^{−ts} = g^{e − ts}` with
`e − ts < s`, and on `B₀`'s success the output is `(e − ts) + ts = e` in `Z_{p−1}`
(`Nat.cast_sub`, `Nat.div_add_mod`). `uprob_prod` over `(e, t)` and `uprob_mono` with the
event `t = ⌊e/s⌋ ∧ B₀ succeeds` (`OneWay.uprob_and_le_mul`-style product of the two
independent factors, `h (e % s)`). -/
theorem invProb_shiftInverter_ge {g : (ZMod p)ˣ} (hg : IsGenerator g) {ρ' : Type*} [Fintype ρ']
    (B₀ : (ZMod p)ˣ → ρ' → ℕ) {s T : ℕ} (hs : 0 < s) (hT : p - 1 ≤ T * s) {δ : ℝ}
    (h : ∀ e' < s, 1 - δ ≤ uprob fun c : ρ' => B₀ (g ^ e') c = e') :
    (1 - δ) / T ≤ invProb (expo g) (shiftInverter g B₀ s T) := by
  classical
  rw [invProb_def]
  rcases Nat.eq_zero_or_pos T with hT0 | hT0
  · rw [hT0, Nat.cast_zero, div_zero]; exact uprob_nonneg _
  -- the event "correct guess and `B₀` succeeds" implies inversion
  let good : ZMod (p - 1) × (Fin T × ρ') → Prop := fun z =>
    z.2.1.val = z.1.val / s ∧ B₀ (g ^ (z.1.val % s)) z.2.2 = z.1.val % s
  refine le_trans ?_ (uprob_mono (p := good) (q := fun z : ZMod (p - 1) × (Fin T × ρ') =>
    expo g (shiftInverter g B₀ s T (expo g z.1) z.2) = expo g z.1) fun z hz => ?_)
  rotate_left
  · obtain ⟨x, t, c⟩ := z
    rw [dlb_shiftInverter_eq g B₀ x t c hz.1 hz.2]
  rw [uprob_prod]
  -- each section has probability at least `(1/T)(1 − δ)`
  have hsec : ∀ x : ZMod (p - 1), (1 - δ) / T ≤ uprob fun b : Fin T × ρ' => good (x, b) := by
    intro x
    have hq : x.val / s < T := by
      have := ZMod.val_lt x
      exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; omega)
    have h1 : uprob (fun b : Fin T × ρ' => good (x, b)) =
        uprob (fun t : Fin T => t = ⟨x.val / s, hq⟩) * uprob (fun c : ρ' => B₀ (g ^ (x.val % s)) c = x.val % s) := by
      rw [← HardcoreBit.uprob_prod_and]
      congr 1; funext b
      simp only [good, Fin.ext_iff]
    rw [h1, OneWay.uprob_eq_one_div_card, Fintype.card_fin, div_eq_mul_inv, one_div, mul_comm]
    gcongr
    exact h _ (Nat.mod_lt _ hs)
  calc (1 - δ) / T = uexp (fun _ : ZMod (p - 1) => (1 - δ) / (T : ℝ)) := (HardcoreBit.uexp_const _).symm
    _ ≤ _ := HardcoreBit.uexp_mono hsec

/-- **The inverter `B` of [PS10, Lemma 84.1]**: the range reduction applied to the loop of
Algorithm 84.2 driven by the majority test with `ℓ` trials per round and `k` rounds. -/
noncomputable def dlInverter (g : (ZMod p)ˣ) {ρ : Type*} [Fintype ρ] (A : (ZMod p)ˣ → ρ → Bool)
    (s T ℓ k : ℕ) : (ZMod p)ˣ → Fin T × (Fin k → Fin ℓ → ZMod (p - 1) × ρ) → ZMod (p - 1) :=
  shiftInverter g (dlLoop g (majOracle g A ℓ) k) s T

/-- The queries of Algorithm 84.2 along the *perfect path* (driven by `halfOracle`), which do
not depend on the coins. -/
private noncomputable def dlb_perf (g : (ZMod p)ˣ) (k : ℕ) (y : (ZMod p)ˣ) : Fin k → (ZMod p)ˣ :=
  dlQueries g (fun y (_ : Unit) => halfOracle g y) k y (fun _ => ())

omit [NeZero (p - 1)] in
/-- If a noisy oracle answers correctly at each of the perfect path's queries, the noisy path's
queries are the perfect path's (induction on the rounds, `dlQueries_zero`, `dlQueries_succ`). -/
private theorem dlb_dlQueries_eq_perf (g : (ZMod p)ˣ) {κ : Type*} (O : (ZMod p)ˣ → κ → Bool) :
    ∀ (k : ℕ) (y : (ZMod p)ˣ) (c : Fin k → κ),
      (∀ j, O (dlb_perf g k y j) (c j) = halfOracle g (dlb_perf g k y j)) →
        ∀ j, dlQueries g O k y c j = dlb_perf g k y j
  | 0, _, _, _, j => j.elim0
  | k + 1, y, c, h, j => by
    have h0 := h 0
    unfold dlb_perf at h0 ⊢
    rw [dlQueries_zero] at h0
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [dlQueries_zero, dlQueries_zero]
    · rw [dlQueries_succ, dlQueries_succ, h0]
      apply dlb_dlQueries_eq_perf g O k
      intro j'
      have hj := h j'.succ
      unfold dlb_perf at hj ⊢
      rw [dlQueries_succ] at hj
      exact hj

/-- Along the perfect path from `g^e` with `e < s ≤ (p−1)/2`, every query is `g^a` with `a` in
the windows of `uprob_majOracle_ne_le`: the query of round `j` is `±g^{⌊e/2^{j+1}⌋}`
(`dlb_dlRoot_pow`, `neg_pow_eq`, and `dlb_keep` for the path). -/
private theorem dlb_perf_window (hp3 : p % 4 = 3) {g : (ZMod p)ˣ} (hg : IsGenerator g) {s : ℕ}
    (hsh : s ≤ (p - 1) / 2) : ∀ (k e : ℕ), e < s → ∀ j : Fin k, ∃ a, a < p - 1 ∧
      (a < s ∨ ((p - 1) / 2 ≤ a ∧ a < (p - 1) / 2 + s)) ∧ dlb_perf g k (g ^ e) j = g ^ a
  | 0, _, _, j => j.elim0
  | k + 1, e, he, j => by
    have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp3
    obtain ⟨h2, hpos⟩ := two_mul_half (p := p) hp2
    unfold dlb_perf
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [dlQueries_zero]
      rcases dlb_dlRoot_pow hp3 hg e with h | h
      · exact ⟨e / 2, by omega, Or.inl (by omega), h⟩
      · exact ⟨e / 2 + (p - 1) / 2, by omega, Or.inr (by omega), by rw [h, neg_pow_eq hp2 hg]⟩
    · rw [dlQueries_succ, dlb_keep hp3 hg (by omega)]
      exact dlb_perf_window hp3 hg hsh k (e / 2) (by omega) j

/-- **The concrete core of [PS10, Lemma 84.1]**: for `p ≡ 3 (mod 4)` prime, a generator `g`
of `Z_p^*` and a predictor `A` of `half_{p−1}` from `g^x` with success at least `1/2 + ε`, the
inverter `dlInverter g A s T ℓ k` recovers the discrete logarithm of a uniform `g^x` with
probability at least `(1 − k/(ε² ℓ))/T`, for any window `0 < s` with `4s ≤ ε(p−1)`, `T s ≥ p − 1`
and `s ≤ 2^k` rounds. (With `s ≈ ε(p−1)/4`, `T ≈ 4/ε + 1`, `k = |p|` and `ℓ = 4|p|/ε²` this is
`≥ 3ε/20`.)

**Proof sketch.** `invProb_shiftInverter_ge` with `B₀ := dlLoop g (majOracle g A ℓ) k` and
`δ := k/(ε² ℓ)`: for `e' < s ≤ 2^k`, `dlBits g k (g^{e'}) = e'` (`dlBits_pow`), and
`dlLoop_eq_dlBits` reduces the failure of `B₀` to the failure of some round's majority vote on
its query (`uprob_exists_le` over the `k` rounds, `Fin.cons` bookkeeping). Along the correct
path the query of round `j` is `dlRoot` of `g^{e_j}` with `e_j = e'/2^j < s`, i.e. `g^{e_j/2}`
or `g^{e_j/2 + (p−1)/2}` (`sq_eq_pow_two_mul_iff`, `neg_pow_eq`), an instance of the windows of
`uprob_majOracle_ne_le`; the coins of round `j` are an independent uniform coordinate
(`pushesUniform_eval`), so each round fails with probability `≤ 1/(ε² ℓ)`. -/
theorem invProb_dlInverter_ge (hp3 : p % 4 = 3) {g : (ZMod p)ˣ} (hg : IsGenerator g)
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] (A : (ZMod p)ˣ → ρ → Bool) {ε : ℝ} (hε : 0 < ε)
    (hA : 1 / 2 + ε ≤ predProb (expo g) (halfBit (p - 1)) A) {s T ℓ k : ℕ} (hs : 0 < s)
    (hs4 : 4 * (s : ℝ) ≤ ε * ((p : ℝ) - 1)) (hT : p - 1 ≤ T * s) (hk : s ≤ 2 ^ k) (hℓ : 0 < ℓ) :
    (1 - k / (ε ^ 2 * ℓ)) / T ≤ invProb (expo g) (dlInverter g A s T ℓ k) := by
  classical
  have hp2 : p ≠ 2 := by rintro rfl; norm_num at hp3
  obtain ⟨h2, hpos⟩ := two_mul_half (p := p) hp2
  -- `ε ≤ 1/2` puts the window inside `[0, (p−1)/8]`
  have hε2 := dlb_eps_le A hA
  have hp8 : 8 * s ≤ p - 1 := by
    have hcast : ((p : ℝ) - 1) = ((p - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
    have hp1 : (0 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hcast] at hs4
    have : (8 * s : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by nlinarith
    exact_mod_cast this
  unfold dlInverter
  refine invProb_shiftInverter_ge hg _ hs hT fun e' he' => ?_
  set O := majOracle g A ℓ with hO
  have hbits : dlBits g k (g ^ e') = e' := dlBits_pow hp3 hg (by omega) (by omega)
  -- failure forces a wrong majority at some perfect-path query
  have hfail : ∀ c : Fin k → Fin ℓ → ZMod (p - 1) × ρ, ¬ dlLoop g O k (g ^ e') c = e' →
      ∃ j ∈ (univ : Finset (Fin k)), O (dlb_perf g k (g ^ e') j) (c j) ≠
        halfOracle g (dlb_perf g k (g ^ e') j) := by
    intro c hc
    by_contra hall
    push_neg at hall
    have hq := dlb_dlQueries_eq_perf g O k (g ^ e') c fun j => hall j (mem_univ j)
    apply hc
    refine (dlLoop_eq_dlBits g O k (g ^ e') c fun j => ?_).trans hbits
    rw [hq j]
    exact hall j (mem_univ j)
  -- each round fails with probability at most `1/(ε² ℓ)`
  have hround : ∀ j : Fin k, uprob (fun c : Fin k → Fin ℓ → ZMod (p - 1) × ρ =>
      O (dlb_perf g k (g ^ e') j) (c j) ≠ halfOracle g (dlb_perf g k (g ^ e') j)) ≤
        1 / (ε ^ 2 * ℓ) := by
    intro j
    obtain ⟨a, ha, haw, hqa⟩ := dlb_perf_window hp3 hg (by omega) k e' he' j
    rw [(HardcoreBit.pushesUniform_eval j).uprob_eq
      (fun c' => O (dlb_perf g k (g ^ e') j) c' ≠ halfOracle g (dlb_perf g k (g ^ e') j)), hqa,
      dlb_halfOracle_pow_eq hg ha]
    exact uprob_majOracle_ne_le hg A hε hA hs4 hℓ ha haw
  have hunion := (uprob_mono hfail).trans ((uprob_exists_le univ _).trans
    (sum_le_sum fun j _ => hround j))
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hunion
  have hnot := uprob_not (fun c : Fin k → Fin ℓ → ZMod (p - 1) × ρ => dlLoop g O k (g ^ e') c = e')
  have : (k : ℝ) * (1 / (ε ^ 2 * ℓ)) = k / (ε ^ 2 * ℓ) := by ring
  linarith

end Concrete

/-- **Good instances** (Lem-84.1.5, missing in the text): if the predictor's success, averaged
over the instances `(p, g)` drawn by the generator, is at least `1/2 + ε`, then a set of
instances of probability at least `ε/2` has per-instance success at least `1/2 + ε/2`
(`HardcoreBit.half_le_uprob_threshold` with `c = 1/2`). The reduction fixes `(p, g)` from its
input, so the concrete lemma is applied on this set. -/
theorem good_instances {ι : Type*} [Fintype ι] [Nonempty ι] (q : ι → ℝ) (hq : ∀ i, q i ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε) (h : 1 / 2 + ε ≤ uexp q) :
    ε / 2 ≤ uprob fun i => 1 / 2 + ε / 2 ≤ q i :=
  HardcoreBit.half_le_uprob_threshold q hq (by norm_num) hε h

/-! ## The asymptotic form: the full-group collection and Lemma 84.1 -/

/-- A **full-group instance** `⟨p, ⟨p − 1, g⟩⟩`: a valid index whose order is `p − 1` (so `g`
generates `Z_p^*`, the setting of [PS10, Lemma 84.1 and Algorithm 84.2]) with `p ≡ 3 (mod 4)`
(square roots by [PS10, Theorem 58.2]).

**Deviation:** `p ≡ 3 (mod 4)` (decision log, open question 3). -/
def FullGroupValid (i : List Bool) : Prop := ExpValid i ∧ dlM i = dlP i - 1 ∧ dlP i % 4 = 3

/-- Unfolding `FullGroupValid`: `i` is a full-group instance iff it is valid, `m = p − 1` and
`p ≡ 3 (mod 4)`. -/
theorem fullGroupValid_iff (i : List Bool) :
    FullGroupValid i ↔ ExpValid i ∧ dlM i = dlP i - 1 ∧ dlP i % 4 = 3 := Iff.rfl

/-- A full-group instance is a valid instance. -/
theorem FullGroupValid.expValid {i : List Bool} (h : FullGroupValid i) : ExpValid i := h.1

/-- **Full-group instance generators**: PPTs outputting primes `p ≡ 3 (mod 4)` of length `n`
with a generator of `Z_p^*` (the index set `{(p, g)}` of the collection of
[PS10, Lemma 84.1]). -/
abbrev FullGroupGen : Type 1 := ExpGroupGen FullGroupValid

/-- **The discrete-log assumption in `Z_p^*`** — the hypothesis of [PS10, Lemma 84.1] ("under
the DL assumption (52.2)"): every non-uniform PPT solves
`Pr[(p, g) ← Gen(1^n); x ← Z_{p−1} : A(1^n, ⟨⟨p, ⟨p − 1, g⟩⟩, g^x⟩) = x]` with negligible
probability.

**Deviation:** Assumption 52.2 is for prime-order groups; the lemma needs discrete-log
hardness for a uniform generator of the full group `Z_p^*` (source error 27), stated here
relative to a full-group instance generator. -/
def FullDLAssumption (G : FullGroupGen) : Prop := G.DLHard

/-- Unfolding: the full-group discrete-log assumption is the negligibility of every `dlProb`. -/
theorem fullDLAssumption_iff (G : FullGroupGen) :
    FullDLAssumption G ↔ ∀ A : NUPPT, Negligible fun n => G.dlProb A n :=
  ExpGroupGen.dlHard_iff G

/-- **The discrete-log collection in `Z_p^*`** [PS10, Lemma 84.1, "the exponentiation function
`f_{p,g}(x) = g^x mod p` from the discrete-log collection `DL`"]: domains `Z_{p−1}`,
`f_{p,g}(x) = g^x mod p`, the instance generator `G`. -/
noncomputable def fullDLCollection (H : ArithmeticFP) (G : FullGroupGen) : Collection :=
  expCollection H G fun _ h => h.expValid

/-- **The domain of the full-group collection is `Z_{p−1}`**: the published equivalence
`(fullDLCollection H G).D i ≃ ZMod (expOrd i)` (the identity), the interface to the domain
(`fullDLCollection_f`, `fullDLCollection_encD`, `fullDLCollection_decD`; see
`expCollection_domEquiv`). -/
def fullDLCollection_domEquiv (H : ArithmeticFP) (G : FullGroupGen) (i : List Bool) :
    (fullDLCollection H G).D i ≃ ZMod (expOrd i) :=
  expCollection_domEquiv H G (fun _ h => h.expValid) i

/-- **The domain equivalence carries the uniform distribution**: for `P` on `Z_{p−1}`,
`Pr_{x ← D i}[P (φ x)] = Pr_y[P y]` with `φ = fullDLCollection_domEquiv H G i` (`uprob_comp_equiv`),
the form in which uniform statements over the domain are read. -/
theorem fullDLCollection_domEquiv_uprob (H : ArithmeticFP) (G : FullGroupGen) (i : List Bool)
    (P : ZMod (expOrd i) → Prop) :
    uprob (fun x : (fullDLCollection H G).D i => P (fullDLCollection_domEquiv H G i x)) = uprob P :=
  uprob_comp_equiv _ P

/-- The function of the full-group collection is `expF`, read through the domain equivalence:
`(fullDLCollection H G).f i x = expF i (fullDLCollection_domEquiv H G i x)`. -/
theorem fullDLCollection_f (H : ArithmeticFP) (G : FullGroupGen) (i : List Bool)
    (x : (fullDLCollection H G).D i) :
    (fullDLCollection H G).f i x = expF i (fullDLCollection_domEquiv H G i x) :=
  expCollection_f H G (fun _ h => h.expValid) i x

/-- The encoder of the full-group collection is `expEnc`, read through the domain equivalence:
`(fullDLCollection H G).encD i x = expEnc i (fullDLCollection_domEquiv H G i x)`. -/
theorem fullDLCollection_encD (H : ArithmeticFP) (G : FullGroupGen) (i : List Bool)
    (x : (fullDLCollection H G).D i) :
    (fullDLCollection H G).encD i x = expEnc i (fullDLCollection_domEquiv H G i x) :=
  expCollection_encD H G (fun _ h => h.expValid) i x

/-- The decoder of the full-group collection is `expDec`, carried back along the domain
equivalence:
`(fullDLCollection H G).decD i w = (expDec i w).map (fullDLCollection_domEquiv H G i).symm`. -/
theorem fullDLCollection_decD (H : ArithmeticFP) (G : FullGroupGen) (i w : List Bool) :
    (fullDLCollection H G).decD i w = (expDec i w).map (fullDLCollection_domEquiv H G i).symm :=
  expCollection_decD H G (fun _ h => h.expValid) i w

/-- The index generator of the full-group collection is `expGen G`. -/
theorem fullDLCollection_gen (H : ArithmeticFP) (G : FullGroupGen) :
    (fullDLCollection H G).gen = expGen G :=
  expCollection_gen H G (fun _ h => h.expValid)

/-- **The coins of the full-group collection's generator are the instance generator's**: the
published equivalence `(fullDLCollection H G).gen.Coins n ≃ G.gen.Coins n`
(`expCollection_coinsEquiv`), the interface between the `HardCore` average and the averages of
`hbig` and `G.dlProb` over `G.gen`'s coins. -/
noncomputable def fullDLCollection_coinsEquiv (H : ArithmeticFP) (G : FullGroupGen) (n : ℕ) :
    (fullDLCollection H G).gen.Coins n ≃ G.gen.Coins n :=
  expCollection_coinsEquiv H G (fun _ h => h.expValid) n

/-- The coin equivalence carries the uniform distribution:
`Pr_r[P (φ r)] = Pr_{r'}[P r']` with `φ = fullDLCollection_coinsEquiv H G n`. -/
theorem fullDLCollection_coinsEquiv_uprob (H : ArithmeticFP) (G : FullGroupGen) (n : ℕ)
    (P : G.gen.Coins n → Prop) :
    uprob (fun r : (fullDLCollection H G).gen.Coins n => P (fullDLCollection_coinsEquiv H G n r)) =
      uprob P :=
  uprob_comp_equiv _ P

/-- The coin equivalence carries averages:
`E_r[F (φ r)] = E_{r'}[F r']` with `φ = fullDLCollection_coinsEquiv H G n`. -/
theorem fullDLCollection_coinsEquiv_uexp (H : ArithmeticFP) (G : FullGroupGen) (n : ℕ)
    (F : G.gen.Coins n → ℝ) :
    uexp (fun r : (fullDLCollection H G).gen.Coins n => F (fullDLCollection_coinsEquiv H G n r)) =
      uexp F :=
  HardcoreBit.uexp_comp_equiv _ F

/-- The index generated by the full-group collection from `n₀` on is the instance generator's
output on the coins read through `fullDLCollection_coinsEquiv`. -/
theorem fullDLCollection_index (H : ArithmeticFP) (G : FullGroupGen) (n : ℕ)
    (r : (fullDLCollection H G).gen.Coins n) (hn : G.n₀ ≤ n) :
    (fullDLCollection H G).index n r = G.gen.runAt n [] (fullDLCollection_coinsEquiv H G n r) :=
  expCollection_index H G _ n r hn

/-- The domain sampler of the full-group collection is `expSampler H`. -/
theorem fullDLCollection_sample (H : ArithmeticFP) (G : FullGroupGen) :
    (fullDLCollection H G).sample = expSampler H :=
  expCollection_sample H G (fun _ h => h.expValid)

/-- The evaluator of the full-group collection is `expEval`. -/
theorem fullDLCollection_eval (H : ArithmeticFP) (G : FullGroupGen) :
    (fullDLCollection H G).eval = expEval :=
  expCollection_eval H G (fun _ h => h.expValid)

/-- The full-group collection is one-way under the full-group discrete-log assumption
([PS10, Theorem 52.3] for `Z_p^*`): `expCollection_oneWay`. -/
theorem fullDLCollection_oneWay (H : ArithmeticFP) (G : FullGroupGen) (hDL : FullDLAssumption G) :
    (fullDLCollection H G).OneWay :=
  expCollection_oneWay H G (fun _ h => h.expValid) hDL

/-- **The predicate `half_{p−1}` on the collection**: `h_i(x) = [2x + 2 ≤ p]`, which is
`[2x < p − 1]` at every full-group index (`halfPred_eq`) and is computable from the numerals
of `p` and `x` at every string index (`halfStr_spec`). -/
noncomputable def halfPred (i : List Bool) (x : ZMod (expOrd i)) : Bool :=
  decide (2 * x.val + 2 ≤ dlP i)

/-- At a prime index `half_{p−1}(x) = [2x < p − 1]`, the predicate `halfBit (p − 1)` of the
concrete layer. -/
theorem halfPred_eq {i : List Bool} (h : ExpValid i) (x : ZMod (expOrd i)) :
    halfPred i x = decide (2 * x.val < dlP i - 1) := by
  have := ((expValid_iff i).1 h).1.two_le
  simp only [halfPred, decide_eq_decide]
  omega

/-- **The evaluator of `half_{p−1}`** on `⟨⟨p, ⟨m, g⟩⟩, x⟩`: `[2x + 2 ≤ p]` on the numerals
(Lem-84.1.0, [PS10, p. 84, "it is easy to compute `half_{p−1}()` given `x`"]). -/
def halfStr (z : List Bool) : List Bool :=
  [decide (2 * listToNat (pairSndD z) + 2 ≤ listToNat (pairFstD (pairFstD z)))]

/-- The evaluator computes `halfPred` on encoded elements at every index (the efficiency
clause of `Collection.HardCore`). -/
theorem halfStr_spec (i : List Bool) (x : ZMod (expOrd i)) :
    halfStr (pairEncode i (expEnc i x)) = [halfPred i x] := by
  rw [expEnc_eq]
  unfold halfPred
  rw [dlP_eq]
  simp only [halfStr, pairFstD_pairEncode, pairSndD_pairEncode,
    listToNat_natToList (val_lt_two_pow_dlW i x)]

/-- `halfStr` as a composite of bundle operations: `[¬ (⌊p/2⌋ ≤ x)]`, with `⌊p/2⌋` the quotient
of `divModStr ⟨p, ⟦2⟧_2⟩` and the comparison `leStr`. -/
private theorem dlb_halfStr_eq (z : List Bool) :
    halfStr z = [!((leStr (pairEncode (pairFstD (divModStr (pairEncode (pairFstD (pairFstD z))
      (natToList 2 2)))) (pairSndD z))).headD false)] := by
  have h2 : listToNat (natToList 2 2) = 2 := listToNat_natToList (by norm_num)
  rw [divModStr_pairEncode, pairFstD_pairEncode, h2, leStr_pairEncode,
    listToNat_natToList (lt_of_le_of_lt (Nat.div_le_self _ _) (listToNat_lt_two_pow _))]
  unfold halfStr
  simp only [List.headD_cons, List.cons.injEq, and_true]
  rw [← decide_not, decide_eq_decide]
  omega

/-- **`half_{p−1}` is polynomial-time computable** (Lem-84.1.0) given the arithmetic bundle.

**Proof sketch.** `2x + 2 ≤ p ⟺ ¬ (p / 2 ≤ x)`: `p / 2` is the quotient of `divModStr ⟨p, 1 0⟩`
(`H.divMod` with the constant numeral of `2`, `polyTimeComputable_const`), the comparison is
`H.le` on `⟨p / 2, x⟩` (`polyTimeComputable_pairFstD`, `_pairSndD`, `.pairEncode`), and the
negation of a one-bit string is `polyTimeComputable_ite` on `polyTimeComputable_pairEq` with
`[true]`. -/
theorem polyTimeComputable_halfStr (H : ArithmeticFP) : PolyTimeComputable halfStr := by
  have hp := polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
  have hdm := H.divMod.comp (hp.pairEncode (polyTimeComputable_const (natToList 2 2)))
  have hle := H.le.comp ((polyTimeComputable_pairFstD.comp hdm).pairEncode polyTimeComputable_pairSndD)
  have hb := polyTimeComputable_not (polyTimeComputable_headD.comp hle)
  refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp hb
  rw [dlb_halfStr_eq]
  simp only [Function.comp_apply]

/-- **Lemma 84.1** [PS10, Lemma 84.1]: under the discrete-log assumption in `Z_p^*` (and the
arithmetic hypotheses), `half_{p−1}` is a hard-core predicate for the exponentiation
`f_{p,g}(x) = g^x mod p` of the discrete-log collection: for every non-uniform PPT `A` there is
a negligible `ε` with `Pr[(p, g) ← Gen(1^n); x ← Z_{p−1} : A(1^n, ⟨⟨p, ⟨p−1, g⟩⟩, g^x⟩) =
half_{p−1}(x)] ≤ 1/2 + ε(n)` for all `n`.

**Deviation:** Lemma 84.1 vs Assumption 52.2: the assumption is for prime-order `G_q`, the lemma
and Algorithm 84.2 use `Z_p^*` (even order); `x ← Z_p` should be `x ← Z_{p−1}`;
"`ε = s(n)`" should be `1/s(n)`; the range reduction "as we will show later" is never shown;
the good-instance averaging over `(p, g)` is missing; the p. 86 analysis is stated for the
complementary event of its own increment rule (module docstring, run-3 audit P8-3). Also:
`p ≡ 3 (mod 4)`; `p` of full length `n` except on a set of the generator's coins of negligible
probability `δ n` (`hbig`, `ExpGroupGen.FullLengthExcept`); the collection form of
Definition 78.3 (`Collection.HardCore`: `A` receives `1^n` and the index).

Repair (run-3 audit P8-2): the hypothesis `hbig : G.FullLength` (full length on every coin
string, not known to be satisfiable) became `∃ δ, Negligible δ ∧ G.FullLengthExcept δ`; the
proof discards the short-prime coins, which contribute at most `δ n` to the good-instance set.

**Proof sketch.** *Easy:* `halfStr` with `polyTimeComputable_halfStr H` and `halfStr_spec`,
read through `fullDLCollection_encD`.
*Hard:* by contradiction with `not_negligible_iff` (through the quantifier form
`Ensemble.indist_iff_exists_negligible`-style of `HardCore`): suppose `A : NUPPT` has
`1/2 + n^{-c} ≤ E_r[Pr_{x, ρ}[A(1^n, ⟨i, f_i x⟩) = half_i x]]` for infinitely many `n ≥ n₀`.
Set `ε := n^{-c}/2`. By `good_instances` (over the generator's coins `r`, index `i = Gen(1^n; r)`)
a set of coins of probability `≥ ε` has per-instance success `≥ 1/2 + ε` (the collection's coins
read as `G.gen`'s through `fullDLCollection_coinsEquiv`, `fullDLCollection_index`,
`fullDLCollection_coinsEquiv_uexp`); removing the coins
with `p < 2^{n−1}` (probability `≤ δ n` by `hbig`, and `δ n ≤ ε/2` for large `n` since `δ` is
negligible) leaves a *good* set of probability `≥ ε/2` (`uprob_not`, `uprob_or_le`). At such an
index `i = ⟨p, ⟨p−1, g⟩⟩` (valid, `dlW i = n`, `p ≡ 3 (mod 4)`, `2^{n−1} ≤ p < 2^n` on the good
set and by `WellFormedIndex`), the domain is `Z_{p−1}` (`fullDLCollection_domEquiv` with
`fullDLCollection_domEquiv_uprob`, `expOrd_of_valid`), `f_i x` is the numeral of
`expo g_u x` with `g_u := expUnit` a generator (`orderOf_expUnit`, `IsGenerator` by
`orderOf_eq_card_of_forall_mem_zpowers`-converse `zpowers_eq_top_of_prime_card`-free counting:
`Nat.card_zpowers`; `fullDLCollection_f`), and `half_i x = halfBit (p−1) x` (`halfPred_eq`), so
`A`'s per-instance success is `predProb (expo g_u) (halfBit (p−1)) A_i` with
`A_i y ρ := A.distinguisherL n (pairEncode i (natToList n (y : ZMod p).val)) ρ`.
Apply `invProb_dlInverter_ge` with `ε := n^{-c}/2`, `s := ⌊(p−1)/(8n^c)⌋` (so `4s ≤ ε(p−1)`),
`T := ⌈(p−1)/s⌉` (so `Ts ≥ p − 1`), `k := n` (`s ≤ p − 1 < 2^n`) and `ℓ := 16 n^{2c+1}`
(so `k/(ε²ℓ) = 1/4`). For large `n` the good instances have `p − 1 ≥ 2^{n−1} − 1 ≥ 16 n^c`, so
`(p−1)/(8n^c) ≥ 2`, `s ≥ (p−1)/(16 n^c) ≥ 1` and `T ≤ K(n) := 16 n^c < 2^n`; the inverter then
succeeds with probability `≥ (3/4)/T ≥ 3/(4K(n))` on each good instance, with ideal coins.
The machine `B` realising `dlInverter` is a non-uniform PPT: advice `⟨A.advice n, ⟦8n^c⟧_n⟩`
(the `n`-bit numeral of `8n^c`: the bundle has no unary-to-binary conversion); coins
`n·n + n·ℓ·(n·n + A.coins)` (a `PolyExpr`, `c` being fixed): one block of `n·n` coins for `t`
and, for each of the `n·ℓ` trials, a block of `n·n` coins for `r_{j,i}` and `A.coins` coins for
`ρ_{j,i}`. On `⟨1^n, ⟨i, y⟩⟩` it reads `p`, `g` from `i`; computes `s` and `T` (`H.sub`,
`H.divMod`, `H.add`); outputs `0^n` unless `1 ≤ s` and `T < 2^n` (the analysis uses only the
good instances); samples `t := (sampleBelowL T (Nat.size T) n n ·).getD 0` and
`r_{j,i} := (sampleBelowL (p−1) (Nat.size (p−1)) n n ·).getD 0` (`H.le`, `H.size`,
`polyTimeComputable_iterateFind`); shifts `y · g^{−ts}` (`H.modExp`, `H.xgcd`); and runs the
`n` rounds of `dlLoop` (`Complexity.polyTimeComputable_iterate` with the state `⟨y_j, bits⟩`,
D11): quadratic residuosity by `H.modExp` (`y^{(p−1)/2} = 1`, Euler), the root `y^{(p+1)/4}` by
`H.modExp` (`sqrtMod3`, [PS10, Theorem 58.2]), the `ℓ` oracle calls `A.output` on the layout
`⟨⟨⟨1^n, ⟨i, z_{j,i}⟩⟩, A.advice n⟩, ρ_{j,i}⟩` (`polyTimeComputable_iterateEmit`,
`NUPPT.polyTimeComputable_layout`), the comparison with `half(r_{j,i})` (`halfStr`), the
majority (`polyTimeComputable_majority`), the negation `p − z` and the bit assembly; finally
`(bits + ts) mod (p−1)` as an `n`-bit numeral (`decodeFin n` reads it back,
`bitsToNat_natToBits`). Sampling: each of the `1 + nℓ` sampled coordinates is within `(1/2)^n`
of uniform (`statClose_sampleBelowL`, with `0 < T < 2^n` and `0 < p − 1 < 2^n`); the coins of
`A` are exact; `StatClose.prod` and `StatClose.abs_uprob_sub_le_prod` give a loss of at most
`(1 + 16 n^{2c+2})(1/2)^n` at every instance. Averaging over the good set (probability
`≥ ε/2`, `HardcoreBit.uprob_mul_le_uexp`):
`G.dlProb B n ≥ (ε/2)·3/(4K(n)) − (1 + 16 n^{2c+2})(1/2)^n`
`= 3/(256 n^{2c}) − (1 + 16 n^{2c+2})(1/2)^n`
for infinitely many `n`, an inverse polynomial, contradicting `hDL B` via `not_negligible_iff`. -/
theorem fullDLCollection_hardCore (H : ArithmeticFP) (G : FullGroupGen)
    (hbig : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.FullLengthExcept δ) (hDL : FullDLAssumption G) :
    (fullDLCollection H G).HardCore fun i x => halfPred i (fullDLCollection_domEquiv H G i x) := by
  sorry

end TCSlib.Cryptography.Candidates
