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

/-! ## The proof of Lemma 84.1: the inverter `B` as a machine, and the reduction

The private declarations below (prefix `dlb_`, fill unit dl-b) realise the inverter of
`fullDLCollection_hardCore`'s sketch. The string function `dlb_raw` (polynomial time,
`dlb_raw_poly`) runs the range reduction and `n` rounds of Algorithm 84.2, each with `ℓ` trials
of the majority test, on the numerals of the index (`ArithmeticFP` for every arithmetic
operation); `dlb_raw_sem` identifies it with `dlInverter` on decoded coins; `dlb_instance` bounds
its success at one good instance by `invProb_dlInverter_ge` minus the sampling loss; and
`dlb_reduction` averages over the good instances. -/

/-! ### Numeral arithmetic of the inverter machine -/

/-- Composition of polynomial-time maps in applied form. -/
private theorem dlb_ptc {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun z => g (f z) :=
  hg.comp hf

/-- The numeral `⟦1⟧_1`. -/
private def dlb_one : List Bool := natToList 1 1
/-- The numeral `⟦2⟧_2`. -/
private def dlb_two : List Bool := natToList 2 2
/-- The numeral `⟦4⟧_3`. -/
private def dlb_four : List Bool := natToList 3 4

private theorem dlb_listToNat_one : listToNat dlb_one = 1 := listToNat_natToList (by norm_num)
private theorem dlb_listToNat_two : listToNat dlb_two = 2 := listToNat_natToList (by norm_num)
private theorem dlb_listToNat_four : listToNat dlb_four = 4 := listToNat_natToList (by norm_num)

/-- Modular product `a · b mod p` (`mulStr`, then the remainder of `divModStr`). -/
private def dlb_mulMod (a b p : List Bool) : List Bool :=
  pairSndD (divModStr (pairEncode (mulStr (pairEncode a b)) p))

/-- Modular power `a^e mod p` (`modExpStr`). -/
private def dlb_powMod (a e p : List Bool) : List Bool := modExpStr (pairEncode a (pairEncode e p))

/-- Modular inverse `a⁻¹ mod p` (the second component of `xgcdStr`). -/
private def dlb_invMod (a p : List Bool) : List Bool := pairSndD (xgcdStr (pairEncode a p))

/-- Quotient `⌊a / b⌋` (the first component of `divModStr`). -/
private def dlb_quot (a b : List Bool) : List Bool := pairFstD (divModStr (pairEncode a b))

/-- Remainder `a mod b` (the second component of `divModStr`). -/
private def dlb_rem (a b : List Bool) : List Bool := pairSndD (divModStr (pairEncode a b))

section Poly
variable {fa fb fc : List Bool → List Bool}

private theorem dlb_mulMod_poly (H : ArithmeticFP) (ha : PolyTimeComputable fa) (hb : PolyTimeComputable fb)
    (hc : PolyTimeComputable fc) : PolyTimeComputable fun z => dlb_mulMod (fa z) (fb z) (fc z) :=
  dlb_ptc polyTimeComputable_pairSndD (dlb_ptc H.divMod ((dlb_ptc H.mul (ha.pairEncode hb)).pairEncode hc))

private theorem dlb_powMod_poly (H : ArithmeticFP) (ha : PolyTimeComputable fa) (hb : PolyTimeComputable fb)
    (hc : PolyTimeComputable fc) : PolyTimeComputable fun z => dlb_powMod (fa z) (fb z) (fc z) :=
  dlb_ptc H.modExp (ha.pairEncode (hb.pairEncode hc))

private theorem dlb_invMod_poly (H : ArithmeticFP) (ha : PolyTimeComputable fa) (hb : PolyTimeComputable fb) :
    PolyTimeComputable fun z => dlb_invMod (fa z) (fb z) :=
  dlb_ptc polyTimeComputable_pairSndD (dlb_ptc H.xgcd (ha.pairEncode hb))

private theorem dlb_quot_poly (H : ArithmeticFP) (ha : PolyTimeComputable fa) (hb : PolyTimeComputable fb) :
    PolyTimeComputable fun z => dlb_quot (fa z) (fb z) :=
  dlb_ptc polyTimeComputable_pairFstD (dlb_ptc H.divMod (ha.pairEncode hb))

private theorem dlb_rem_poly (H : ArithmeticFP) (ha : PolyTimeComputable fa) (hb : PolyTimeComputable fb) :
    PolyTimeComputable fun z => dlb_rem (fa z) (fb z) :=
  dlb_ptc polyTimeComputable_pairSndD (dlb_ptc H.divMod (ha.pairEncode hb))

end Poly

section Sem
variable {n a b P : ℕ}

private theorem dlb_mulMod_natToList (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hPn : P < 2 ^ n) :
    dlb_mulMod (natToList n a) (natToList n b) (natToList n P) = natToList n (a * b % P) := by
  unfold dlb_mulMod
  rw [mulStr_natToList n n a b ha hb, divModStr_pairEncode, pairSndD_pairEncode, length_natToList,
    listToNat_natToList (mul_lt_two_pow_add ha hb), listToNat_natToList hPn]

private theorem dlb_powMod_natToList (k : ℕ) (ha : a < 2 ^ n) (hb : b < 2 ^ k) (hPn : P < 2 ^ n) :
    dlb_powMod (natToList n a) (natToList k b) (natToList n P) = natToList n (a ^ b % P) := by
  unfold dlb_powMod
  rw [modExpStr_pairEncode, length_natToList, listToNat_natToList ha, listToNat_natToList hb,
    listToNat_natToList hPn]

private theorem dlb_invMod_natToList (ha : a < 2 ^ n) (hPn : P < 2 ^ n) :
    dlb_invMod (natToList n a) (natToList n P) = natToList n ((a : ZMod P)⁻¹).val := by
  unfold dlb_invMod
  rw [xgcdStr_pairEncode, pairSndD_pairEncode, length_natToList, listToNat_natToList ha,
    listToNat_natToList hPn]

private theorem dlb_quot_natToList (k : ℕ) (ha : a < 2 ^ n) (hb : b < 2 ^ k) :
    dlb_quot (natToList n a) (natToList k b) = natToList n (a / b) := by
  unfold dlb_quot
  rw [divModStr_pairEncode, pairFstD_pairEncode, length_natToList, listToNat_natToList ha,
    listToNat_natToList hb]

private theorem dlb_rem_natToList (k : ℕ) (ha : a < 2 ^ k) (hb : b < 2 ^ n) :
    dlb_rem (natToList k a) (natToList n b) = natToList n (a % b) := by
  unfold dlb_rem
  rw [divModStr_pairEncode, pairSndD_pairEncode, length_natToList, listToNat_natToList ha,
    listToNat_natToList hb]

end Sem


/-! ### Generic loop and list helpers -/

private theorem dlb_take_poly {fa fb : List Bool → List Bool} (ha : PolyTimeComputable fa)
    (hb : PolyTimeComputable fb) : PolyTimeComputable fun z => (fb z).take (fa z).length := by
  have h := dlb_ptc (polyTimeComputable_pairTakePoly .var) (ha.pairEncode hb)
  refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]

private theorem dlb_drop_poly {fa fb : List Bool → List Bool} (ha : PolyTimeComputable fa)
    (hb : PolyTimeComputable fb) : PolyTimeComputable fun z => (fb z).drop (fa z).length := by
  have h := dlb_ptc (polyTimeComputable_pairDropPoly .var) (ha.pairEncode hb)
  refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]

/-- A one-bit equality test of two polynomial-time maps (`polyTimeComputable_pairEq`). -/
private theorem dlb_eq_poly {fa fb : List Bool → List Bool} (ha : PolyTimeComputable fa)
    (hb : PolyTimeComputable fb) : PolyTimeComputable fun z => [decide (fa z = fb z)] := by
  have h := dlb_ptc polyTimeComputable_pairEq (ha.pairEncode hb)
  refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]

/-- `if c then f else g` with a decidable test whose bit is polynomial-time. -/
private theorem dlb_ite_poly {c : List Bool → Prop} [DecidablePred c] {f g : List Bool → List Bool}
    (hc : PolyTimeComputable fun z => [decide (c z)]) (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : PolyTimeComputable fun z => if c z then f z else g z := by
  have h := polyTimeComputable_ite hc hf hg
  refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
  simp only [decide_eq_true_eq]

/-- **Guarded state iteration for `|⟨x, start x⟩|` rounds** (the form of
`TCSlib.Cryptography.polyTimeComputable_stateIterate` of `Asymptotic/HardCoreLoops`, which is not
in this module's import closure): `Complexity.polyTimeComputable_iterate` on the guarded step
`StateLoop.gstep`, whose orbit bound is `StateLoop.length_gstep_iterate_le`. -/
private theorem dlb_stateIterate_poly {start step : List Bool → List Bool}
    (hstart : PolyTimeComputable start) (hstep : PolyTimeComputable step) (B : PolyExpr) :
    PolyTimeComputable fun x =>
      pairSndD ((StateLoop.gstep step B)^[(pairEncode x (start x)).length] (pairEncode x (start x))) := by
  have hF := polyTimeComputable_iterate (StateLoop.gstep_poly hstep B) .var (StateLoop.gstepBound B)
    (fun w i _ => StateLoop.length_gstep_iterate_le step B w i)
  refine (congrArg PolyTimeComputable (funext fun x => ?_)).mp
    (dlb_ptc polyTimeComputable_pairSndD (dlb_ptc hF (polyTimeComputable_id.pairEncode hstart)))
  simp only [PolyExpr.eval_var, id_eq]

/-! ### The fixed data of the inverter's loops -/

/-- The fixed data `⟨⟨u, ⟨i, α⟩⟩, ⟨⟨g⁻¹, ⟨e_H, e_R⟩⟩, ⟨u_S, ⟨u_A, u_ℓ⟩⟩⟩⟩` of the loops: `1^n`, the
index, the predictor's advice, the numerals of `g⁻¹ mod p`, `(p−1)/2` and `p/4 + 1`, and the
unary coin lengths of the domain sampler and of the predictor, and the unary trial count `1^ℓ`. -/
private def dlb_fix (u i α gI eH eR uS uA uL : List Bool) : List Bool :=
  pairEncode (pairEncode u (pairEncode i α))
    (pairEncode (pairEncode gI (pairEncode eH eR)) (pairEncode uS (pairEncode uA uL)))

private def dlb_fu (f : List Bool) : List Bool := pairFstD (pairFstD f)
private def dlb_fi (f : List Bool) : List Bool := pairFstD (pairSndD (pairFstD f))
private def dlb_fα (f : List Bool) : List Bool := pairSndD (pairSndD (pairFstD f))
private def dlb_fgI (f : List Bool) : List Bool := pairFstD (pairFstD (pairSndD f))
private def dlb_feH (f : List Bool) : List Bool := pairFstD (pairSndD (pairFstD (pairSndD f)))
private def dlb_feR (f : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (pairSndD f)))
private def dlb_fuS (f : List Bool) : List Bool := pairFstD (pairSndD (pairSndD f))
private def dlb_fuA (f : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (pairSndD f)))
private def dlb_fuL (f : List Bool) : List Bool := pairSndD (pairSndD (pairSndD (pairSndD f)))
private def dlb_fp (f : List Bool) : List Bool := pairFstD (dlb_fi f)
private def dlb_fg (f : List Bool) : List Bool := pairSndD (pairSndD (dlb_fi f))

private theorem dlb_fix_proj (u i α gI eH eR uS uA uL : List Bool) :
    dlb_fu (dlb_fix u i α gI eH eR uS uA uL) = u ∧ dlb_fi (dlb_fix u i α gI eH eR uS uA uL) = i ∧
    dlb_fα (dlb_fix u i α gI eH eR uS uA uL) = α ∧ dlb_fgI (dlb_fix u i α gI eH eR uS uA uL) = gI ∧
    dlb_feH (dlb_fix u i α gI eH eR uS uA uL) = eH ∧ dlb_feR (dlb_fix u i α gI eH eR uS uA uL) = eR ∧
    dlb_fuS (dlb_fix u i α gI eH eR uS uA uL) = uS ∧ dlb_fuA (dlb_fix u i α gI eH eR uS uA uL) = uA ∧
    dlb_fuL (dlb_fix u i α gI eH eR uS uA uL) = uL := by
  simp only [dlb_fix, dlb_fu, dlb_fi, dlb_fα, dlb_fgI, dlb_feH, dlb_feR, dlb_fuS, dlb_fuA, dlb_fuL,
    pairFstD_pairEncode, pairSndD_pairEncode, and_self]

private theorem dlb_fu_poly : PolyTimeComputable dlb_fu :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
private theorem dlb_fi_poly : PolyTimeComputable dlb_fi :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
private theorem dlb_fα_poly : PolyTimeComputable dlb_fα :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
private theorem dlb_fgI_poly : PolyTimeComputable dlb_fgI :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
private theorem dlb_feH_poly : PolyTimeComputable dlb_feH :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))
private theorem dlb_feR_poly : PolyTimeComputable dlb_feR :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))
private theorem dlb_fuS_poly : PolyTimeComputable dlb_fuS :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
private theorem dlb_fuA_poly : PolyTimeComputable dlb_fuA :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
private theorem dlb_fuL_poly : PolyTimeComputable dlb_fuL :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
private theorem dlb_fp_poly : PolyTimeComputable dlb_fp := polyTimeComputable_pairFstD.comp dlb_fi_poly
private theorem dlb_fg_poly : PolyTimeComputable dlb_fg :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp dlb_fi_poly)

/-! ### One trial of the majority test -/

section Trial
variable (S A : NUPPT)

/-- The sampled exponent's numeral: the domain sampler `S` on the index with the block `sB`. -/
private def dlb_wS (f sB : List Bool) : List Bool :=
  S.output (NUPPT.layout (dlb_fu f) (dlb_fi f) [] sB)

/-- The randomized query `z = root · g^r mod p`. -/
private def dlb_zz (f root sB : List Bool) : List Bool :=
  dlb_mulMod root (dlb_powMod (dlb_fg f) (dlb_wS S f sB) (dlb_fp f)) (dlb_fp f)

/-- The predictor's answer bit on `⟨1^n, ⟨i, z⟩⟩` with advice and the coin block `aB`. -/
private def dlb_aBit (f root sB aB : List Bool) : Bool :=
  decide (A.output (NUPPT.layout (dlb_fu f) (pairEncode (dlb_fi f) (dlb_zz S f root sB)) (dlb_fα f) aB)
    = [true])

/-- The vote of one trial: does the answer agree with `half_{p−1}(r)` (`halfStr`)? -/
private def dlb_vote (f root sB aB : List Bool) : Bool :=
  decide ([dlb_aBit S A f root sB aB] = halfStr (pairEncode (dlb_fi f) (dlb_wS S f sB)))

private theorem dlb_vote_poly (H : ArithmeticFP) {ff fr fs fa : List Bool → List Bool}
    (hf : PolyTimeComputable ff) (hr : PolyTimeComputable fr) (hs : PolyTimeComputable fs)
    (ha : PolyTimeComputable fa) :
    PolyTimeComputable fun z => [dlb_vote S A (ff z) (fr z) (fs z) (fa z)] := by
  have hu := dlb_ptc dlb_fu_poly hf
  have hi := dlb_ptc dlb_fi_poly hf
  have hw : PolyTimeComputable fun z => dlb_wS S (ff z) (fs z) :=
    dlb_ptc S.polyTimeComputable_output
      (NUPPT.polyTimeComputable_layout hu hi (polyTimeComputable_const []) hs)
  have hzz : PolyTimeComputable fun z => dlb_zz S (ff z) (fr z) (fs z) :=
    dlb_mulMod_poly H hr (dlb_powMod_poly H (dlb_ptc dlb_fg_poly hf) hw (dlb_ptc dlb_fp_poly hf))
      (dlb_ptc dlb_fp_poly hf)
  have hout := dlb_ptc A.polyTimeComputable_output
    (NUPPT.polyTimeComputable_layout hu (hi.pairEncode hzz) (dlb_ptc dlb_fα_poly hf) ha)
  have hab : PolyTimeComputable fun z => [dlb_aBit S A (ff z) (fr z) (fs z) (fa z)] :=
    dlb_eq_poly hout (polyTimeComputable_const [true])
  have hh := dlb_ptc (polyTimeComputable_halfStr H) (hi.pairEncode hw)
  exact dlb_eq_poly hab hh

end Trial

/-! ### The trial loop (one round of the majority test) -/

section Inner
variable (S A : NUPPT)

/-- Projections of a trial-loop word `⟨⟨⟨f, root⟩, cs₀⟩, ⟨cnt, ⟨cs, votes⟩⟩⟩`. -/
private def dlb_iF (W : List Bool) : List Bool := pairFstD (pairFstD (pairFstD W))
private def dlb_iRoot (W : List Bool) : List Bool := pairSndD (pairFstD (pairFstD W))
private def dlb_iCnt (W : List Bool) : List Bool := pairFstD (pairSndD W)
private def dlb_iCs (W : List Bool) : List Bool := pairFstD (pairSndD (pairSndD W))
private def dlb_iVotes (W : List Bool) : List Bool := pairSndD (pairSndD (pairSndD W))
/-- The sampler block of the next trial. -/
private def dlb_iSB (W : List Bool) : List Bool := (dlb_iCs W).take (dlb_fuS (dlb_iF W)).length
/-- The coins after the sampler block. -/
private def dlb_iCs1 (W : List Bool) : List Bool := (dlb_iCs W).drop (dlb_fuS (dlb_iF W)).length
/-- The predictor block of the next trial. -/
private def dlb_iAB (W : List Bool) : List Bool := (dlb_iCs1 W).take (dlb_fuA (dlb_iF W)).length
/-- The coins after the trial. -/
private def dlb_iRest (W : List Bool) : List Bool := (dlb_iCs1 W).drop (dlb_fuA (dlb_iF W)).length

/-- One trial: while the counter is nonempty, consume one block pair and prepend the vote. -/
private def dlb_iStep (W : List Bool) : List Bool :=
  if dlb_iCnt W = [] then pairSndD W
  else pairEncode (dlb_iCnt W).tail (pairEncode (dlb_iRest W)
    (dlb_vote S A (dlb_iF W) (dlb_iRoot W) (dlb_iSB W) (dlb_iAB W) :: dlb_iVotes W))

/-- The initial trial state `⟨1^ℓ, ⟨cs, []⟩⟩` from the loop input `⟨⟨f, root⟩, cs⟩`. -/
private def dlb_iStart (Y : List Bool) : List Bool :=
  pairEncode (dlb_fuL (pairFstD (pairFstD Y))) (pairEncode (pairSndD Y) [])

/-- The length bound of the trial loop's states. -/
private def dlb_iB : PolyExpr := .add (.mul (.const 3) .var) (.const 4)

/-- **The trial loop**: the final state `⟨cnt, ⟨cs, votes⟩⟩` after `|⟨Y, start⟩|` guarded rounds. -/
private def dlb_inner (Y : List Bool) : List Bool :=
  pairSndD ((StateLoop.gstep (dlb_iStep S A) dlb_iB)^[(pairEncode Y (dlb_iStart Y)).length]
    (pairEncode Y (dlb_iStart Y)))

private theorem dlb_iStep_poly (H : ArithmeticFP) : PolyTimeComputable (dlb_iStep S A) := by
  have hF : PolyTimeComputable dlb_iF :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  have hR : PolyTimeComputable dlb_iRoot :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  have hC : PolyTimeComputable dlb_iCnt := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hCs : PolyTimeComputable dlb_iCs :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hV : PolyTimeComputable dlb_iVotes :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hS : PolyTimeComputable dlb_iSB := dlb_take_poly (dlb_ptc dlb_fuS_poly hF) hCs
  have hCs1 : PolyTimeComputable dlb_iCs1 := dlb_drop_poly (dlb_ptc dlb_fuS_poly hF) hCs
  have hA : PolyTimeComputable dlb_iAB := dlb_take_poly (dlb_ptc dlb_fuA_poly hF) hCs1
  have hRest : PolyTimeComputable dlb_iRest := dlb_drop_poly (dlb_ptc dlb_fuA_poly hF) hCs1
  have hvote := dlb_vote_poly S A H hF hR hS hA
  have hnil := dlb_ptc polyTimeComputable_isNil hC
  have hnew := (dlb_ptc StateLoop.tail_poly hC).pairEncode (hRest.pairEncode (hvote.append hV))
  exact dlb_ite_poly hnil polyTimeComputable_pairSndD hnew

private theorem dlb_iStart_poly : PolyTimeComputable dlb_iStart :=
  (dlb_ptc dlb_fuL_poly (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)).pairEncode
    (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const []))

private theorem dlb_inner_poly (H : ArithmeticFP) : PolyTimeComputable (dlb_inner S A) :=
  dlb_stateIterate_poly dlb_iStart_poly (dlb_iStep_poly S A H) dlb_iB

end Inner

/-! ### The round loop (Algorithm 84.2 with the majority test) -/

section Outer
variable (S A : NUPPT)

/-- Projections of a round-loop word `⟨⟨f, s₀⟩, ⟨y, ⟨acc, ⟨cnt, cs⟩⟩⟩⟩`. -/
private def dlb_oF (W : List Bool) : List Bool := pairFstD (pairFstD W)
private def dlb_oY (W : List Bool) : List Bool := pairFstD (pairSndD W)
private def dlb_oAcc (W : List Bool) : List Bool := pairFstD (pairSndD (pairSndD W))
private def dlb_oCnt (W : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (pairSndD W)))
private def dlb_oCs (W : List Bool) : List Bool := pairSndD (pairSndD (pairSndD (pairSndD W)))
/-- `y^{(p−1)/2} mod p`, Euler's test of quadratic residuosity. -/
private def dlb_oEul (W : List Bool) : List Bool :=
  dlb_powMod (dlb_oY W) (dlb_feH (dlb_oF W)) (dlb_fp (dlb_oF W))
/-- The test `y ∈ QR_p` as `y^{(p−1)/2} mod p = 1` (two comparisons `leStr`). -/
private def dlb_oQr (W : List Bool) : Bool :=
  (leStr (pairEncode (dlb_oEul W) dlb_one)).headD false &&
    (leStr (pairEncode dlb_one (dlb_oEul W))).headD false
/-- The square `y` or `y · g⁻¹ mod p`. -/
private def dlb_oBase (W : List Bool) : List Bool :=
  if dlb_oQr W = true then dlb_oY W
  else dlb_mulMod (dlb_oY W) (dlb_fgI (dlb_oF W)) (dlb_fp (dlb_oF W))
/-- The root `base^{p/4+1} mod p` [PS10, Theorem 58.2]. -/
private def dlb_oRoot (W : List Bool) : List Bool :=
  dlb_powMod (dlb_oBase W) (dlb_feR (dlb_oF W)) (dlb_fp (dlb_oF W))
/-- The trial loop on this round's root and the remaining coins. -/
private def dlb_oFin (W : List Bool) : List Bool :=
  dlb_inner S A (pairEncode (pairEncode (dlb_oF W) (dlb_oRoot W)) (dlb_oCs W))
/-- The votes of the round. -/
private def dlb_oVotes (W : List Bool) : List Bool := pairSndD (pairSndD (dlb_oFin S A W))
/-- The majority of the votes (`polyTimeComputable_majority`). -/
private def dlb_oB (W : List Bool) : Bool :=
  decide ((dlb_oVotes S A W).length < 2 * (dlb_oVotes S A W).count true)
/-- The kept root: the root if the majority says "lower half", `p − root` otherwise. -/
private def dlb_oNext (W : List Bool) : List Bool :=
  if dlb_oB S A W = true then dlb_oRoot W
  else subStr (pairEncode (dlb_fp (dlb_oF W)) (dlb_oRoot W))

/-- One round: while the counter is nonempty, record the parity bit, run the majority test on
the root, keep it or its negative, and pass the remaining coins on. -/
private def dlb_oStep (W : List Bool) : List Bool :=
  if dlb_oCnt W = [] then pairSndD W
  else pairEncode (dlb_oNext S A W) (pairEncode ((!dlb_oQr W) :: dlb_oAcc W)
    (pairEncode (dlb_oCnt W).tail (pairFstD (pairSndD (dlb_oFin S A W)))))

/-- The length bound of the round loop's states. -/
private def dlb_oB' : PolyExpr := .add (.mul (.const 3) .var) (.const 8)

/-- **The round loop**: the final state `⟨y, ⟨acc, ⟨cnt, cs⟩⟩⟩` from the input `⟨f, s₀⟩`. -/
private def dlb_outer (X : List Bool) : List Bool :=
  pairSndD ((StateLoop.gstep (dlb_oStep S A) dlb_oB')^[(pairEncode X (pairSndD X)).length]
    (pairEncode X (pairSndD X)))

private theorem dlb_oF_poly : PolyTimeComputable dlb_oF :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
private theorem dlb_oY_poly : PolyTimeComputable dlb_oY :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
private theorem dlb_oAcc_poly : PolyTimeComputable dlb_oAcc :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
private theorem dlb_oCnt_poly : PolyTimeComputable dlb_oCnt := polyTimeComputable_pairFstD.comp
  (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
private theorem dlb_oCs_poly : PolyTimeComputable dlb_oCs := polyTimeComputable_pairSndD.comp
  (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

private theorem dlb_oQr_poly (H : ArithmeticFP) : PolyTimeComputable fun W => [dlb_oQr W] := by
  have hE : PolyTimeComputable dlb_oEul :=
    dlb_powMod_poly H dlb_oY_poly (dlb_ptc dlb_feH_poly dlb_oF_poly) (dlb_ptc dlb_fp_poly dlb_oF_poly)
  have hq1 := dlb_ptc polyTimeComputable_headD
    (dlb_ptc H.le (hE.pairEncode (polyTimeComputable_const dlb_one)))
  have hq2 := dlb_ptc polyTimeComputable_headD
    (dlb_ptc H.le ((polyTimeComputable_const dlb_one).pairEncode hE))
  exact polyTimeComputable_and hq1 hq2

private theorem dlb_oRoot_poly (H : ArithmeticFP) : PolyTimeComputable dlb_oRoot := by
  have hp := dlb_ptc dlb_fp_poly dlb_oF_poly
  have hQ : PolyTimeComputable fun W => [decide (dlb_oQr W = true)] := by
    refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp (dlb_oQr_poly H)
    simp only [Bool.decide_eq_true]
  have hBase : PolyTimeComputable dlb_oBase :=
    dlb_ite_poly (c := fun W => dlb_oQr W = true) hQ dlb_oY_poly
      (dlb_mulMod_poly H dlb_oY_poly (dlb_ptc dlb_fgI_poly dlb_oF_poly) hp)
  exact dlb_powMod_poly H hBase (dlb_ptc dlb_feR_poly dlb_oF_poly) hp

private theorem dlb_oFin_poly (H : ArithmeticFP) : PolyTimeComputable (dlb_oFin S A) := by
  have h := dlb_ptc (dlb_inner_poly S A H) ((dlb_oF_poly.pairEncode (dlb_oRoot_poly H)).pairEncode
    dlb_oCs_poly)
  unfold dlb_oFin
  exact h

private theorem dlb_oNext_poly (H : ArithmeticFP) : PolyTimeComputable (dlb_oNext S A) := by
  have hV : PolyTimeComputable fun W => pairSndD (pairSndD (dlb_oFin S A W)) :=
    dlb_ptc polyTimeComputable_pairSndD (dlb_ptc polyTimeComputable_pairSndD (dlb_oFin_poly S A H))
  have hB := dlb_ptc polyTimeComputable_majority hV
  have hB' : PolyTimeComputable fun W => [decide (dlb_oB S A W = true)] := by
    refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp hB
    simp only [dlb_oB, dlb_oVotes, Bool.decide_eq_true]
  exact dlb_ite_poly (c := fun W => dlb_oB S A W = true) hB' (dlb_oRoot_poly H)
    (dlb_ptc H.sub ((dlb_ptc dlb_fp_poly dlb_oF_poly).pairEncode (dlb_oRoot_poly H)))

private theorem dlb_oStep_poly (H : ArithmeticFP) : PolyTimeComputable (dlb_oStep S A) := by
  have hnil := dlb_ptc polyTimeComputable_isNil dlb_oCnt_poly
  have hnq := polyTimeComputable_not (dlb_oQr_poly H)
  have hcs := dlb_ptc polyTimeComputable_pairFstD
    (dlb_ptc polyTimeComputable_pairSndD (dlb_oFin_poly S A H))
  have hnew := (dlb_oNext_poly S A H).pairEncode ((hnq.append dlb_oAcc_poly).pairEncode
    ((dlb_ptc StateLoop.tail_poly dlb_oCnt_poly).pairEncode hcs))
  exact dlb_ite_poly hnil polyTimeComputable_pairSndD hnew

private theorem dlb_outer_poly (H : ArithmeticFP) : PolyTimeComputable (dlb_outer S A) :=
  dlb_stateIterate_poly polyTimeComputable_pairSndD (dlb_oStep_poly S A H) dlb_oB'

end Outer

/-! ### The inverter `B` as a string function -/

section Raw
variable (S A : NUPPT) (ℓP : PolyExpr)

/-- Projections of the raw input `⟨⟨⟨1^n, ⟨i, y⟩⟩, ⟨α_A, ⟨⟦8n^c⟧_n, 1^κ⟩⟩⟩, coins⟩`. -/
private def dlb_zi (z : List Bool) : List Bool := pairFstD (NUPPT.inArg z)
private def dlb_zy (z : List Bool) : List Bool := pairSndD (NUPPT.inArg z)
private def dlb_zα (z : List Bool) : List Bool := pairFstD (NUPPT.inAdvice z)
private def dlb_zD (z : List Bool) : List Bool := pairFstD (pairSndD (NUPPT.inAdvice z))
private def dlb_zκ (z : List Bool) : List Bool := pairSndD (pairSndD (NUPPT.inAdvice z))
private def dlb_zp (z : List Bool) : List Bool := pairFstD (dlb_zi z)
private def dlb_zg (z : List Bool) : List Bool := pairSndD (pairSndD (dlb_zi z))
/-- `p − 1`. -/
private def dlb_zpm1 (z : List Bool) : List Bool := subStr (pairEncode (dlb_zp z) dlb_one)
/-- The window `s = ⌊(p − 1)/(8n^c)⌋`. -/
private def dlb_zs (z : List Bool) : List Bool := dlb_quot (dlb_zpm1 z) (dlb_zD z)
/-- The guess `t`: the first `κ` coins. -/
private def dlb_zt (z : List Bool) : List Bool := (NUPPT.inCoins z).take (dlb_zκ z).length
/-- The shift `t · s`. -/
private def dlb_zts (z : List Bool) : List Bool := mulStr (pairEncode (dlb_zt z) (dlb_zs z))
/-- The shifted instance `y · (g^{ts})⁻¹ mod p`. -/
private def dlb_zy0 (z : List Bool) : List Bool :=
  dlb_mulMod (dlb_zy z) (dlb_invMod (dlb_powMod (dlb_zg z) (dlb_zts z) (dlb_zp z)) (dlb_zp z)) (dlb_zp z)
/-- The fixed data of the loops. -/
private def dlb_zfix (z : List Bool) : List Bool :=
  dlb_fix (NUPPT.inParam z) (dlb_zi z) (dlb_zα z) (dlb_invMod (dlb_zg z) (dlb_zp z))
    (dlb_quot (dlb_zpm1 z) dlb_two) (addStr (pairEncode (dlb_quot (dlb_zp z) dlb_four) dlb_one))
    (List.replicate (S.coins.eval (NUPPT.inParam z).length) true)
    (List.replicate (A.coins.eval (NUPPT.inParam z).length) true)
    (List.replicate (ℓP.eval (NUPPT.inParam z).length) true)
/-- The initial round state `⟨y₀, ⟨[], ⟨1^n, coins after the first n⟩⟩⟩`. -/
private def dlb_zs0 (z : List Bool) : List Bool :=
  pairEncode (dlb_zy0 z) (pairEncode [] (pairEncode (NUPPT.inParam z)
    ((NUPPT.inCoins z).drop (NUPPT.inParam z).length)))
/-- The bits recovered by the round loop (most significant first). -/
private def dlb_zacc (z : List Bool) : List Bool :=
  pairFstD (pairSndD (dlb_outer S A (pairEncode (dlb_zfix S A ℓP z) (dlb_zs0 z))))

/-- **The string function of the inverter `B`**: `(bits + ts) mod (p − 1)` as a numeral of the
width of `p − 1`. -/
private def dlb_raw (z : List Bool) : List Bool :=
  dlb_rem (addStr (pairEncode (dlb_zacc S A ℓP z) (dlb_zts z))) (dlb_zpm1 z)

private theorem dlb_zi_poly : PolyTimeComputable dlb_zi :=
  polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg
private theorem dlb_zy_poly : PolyTimeComputable dlb_zy :=
  polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg
private theorem dlb_zα_poly : PolyTimeComputable dlb_zα :=
  polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inAdvice
private theorem dlb_zD_poly : PolyTimeComputable dlb_zD :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inAdvice)
private theorem dlb_zκ_poly : PolyTimeComputable dlb_zκ :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inAdvice)
private theorem dlb_zp_poly : PolyTimeComputable dlb_zp := polyTimeComputable_pairFstD.comp dlb_zi_poly
private theorem dlb_zg_poly : PolyTimeComputable dlb_zg :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp dlb_zi_poly)
private theorem dlb_zpm1_poly (H : ArithmeticFP) : PolyTimeComputable dlb_zpm1 :=
  H.sub.comp (dlb_zp_poly.pairEncode (polyTimeComputable_const dlb_one))
private theorem dlb_zs_poly (H : ArithmeticFP) : PolyTimeComputable dlb_zs :=
  dlb_quot_poly H (dlb_zpm1_poly H) dlb_zD_poly
private theorem dlb_zt_poly : PolyTimeComputable dlb_zt :=
  dlb_take_poly dlb_zκ_poly NUPPT.polyTimeComputable_inCoins
private theorem dlb_zts_poly (H : ArithmeticFP) : PolyTimeComputable dlb_zts :=
  H.mul.comp (dlb_zt_poly.pairEncode (dlb_zs_poly H))
private theorem dlb_zy0_poly (H : ArithmeticFP) : PolyTimeComputable dlb_zy0 :=
  dlb_mulMod_poly H dlb_zy_poly (dlb_invMod_poly H (dlb_powMod_poly H dlb_zg_poly (dlb_zts_poly H)
    dlb_zp_poly) dlb_zp_poly) dlb_zp_poly

private theorem dlb_zfix_poly (H : ArithmeticFP) : PolyTimeComputable (dlb_zfix S A ℓP) := by
  have hu := NUPPT.polyTimeComputable_inParam
  have hun : ∀ P : PolyExpr,
      PolyTimeComputable fun z => List.replicate (P.eval (NUPPT.inParam z).length) true :=
    fun P => dlb_ptc (polyTimeComputable_unaryPoly P) hu
  have h := (hu.pairEncode (dlb_zi_poly.pairEncode dlb_zα_poly)).pairEncode
    (((dlb_invMod_poly H dlb_zg_poly dlb_zp_poly).pairEncode
      ((dlb_quot_poly H (dlb_zpm1_poly H) (polyTimeComputable_const dlb_two)).pairEncode
        (dlb_ptc H.add ((dlb_quot_poly H dlb_zp_poly (polyTimeComputable_const dlb_four)).pairEncode
          (polyTimeComputable_const dlb_one))))).pairEncode
      ((hun S.coins).pairEncode ((hun A.coins).pairEncode (hun ℓP))))
  refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
  simp only [dlb_zfix, dlb_fix]

private theorem dlb_zs0_poly (H : ArithmeticFP) : PolyTimeComputable dlb_zs0 := by
  have h := (dlb_zy0_poly H).pairEncode ((polyTimeComputable_const []).pairEncode
    (NUPPT.polyTimeComputable_inParam.pairEncode
      (dlb_drop_poly NUPPT.polyTimeComputable_inParam NUPPT.polyTimeComputable_inCoins)))
  refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
  simp only [dlb_zs0]

private theorem dlb_zacc_poly (H : ArithmeticFP) : PolyTimeComputable (dlb_zacc S A ℓP) := by
  have h := dlb_ptc polyTimeComputable_pairFstD (dlb_ptc polyTimeComputable_pairSndD
    (dlb_ptc (dlb_outer_poly S A H) ((dlb_zfix_poly S A ℓP H).pairEncode (dlb_zs0_poly H))))
  refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
  simp only [dlb_zacc]

private theorem dlb_raw_poly (H : ArithmeticFP) : PolyTimeComputable (dlb_raw S A ℓP) := by
  have h := dlb_rem_poly H (dlb_ptc H.add ((dlb_zacc_poly S A ℓP H).pairEncode (dlb_zts_poly H)))
    (dlb_zpm1_poly H)
  refine (congrArg PolyTimeComputable (funext fun z => ?_)).mp h
  simp only [dlb_raw]

end Raw

/-! ### The trial loop's closed form -/

section InnerSpec
variable (S A : NUPPT) (n : ℕ)

/-- The coin string of a list of trial blocks: each block is the sampler's coins, then the
predictor's. -/
private def dlb_blocksL (bs : List (S.Coins n × A.Coins n)) : List Bool :=
  (bs.map fun b => List.ofFn b.1 ++ List.ofFn b.2).flatten

private theorem dlb_blocksL_cons (b : S.Coins n × A.Coins n) (bs : List (S.Coins n × A.Coins n)) :
    dlb_blocksL S A n (b :: bs) = List.ofFn b.1 ++ List.ofFn b.2 ++ dlb_blocksL S A n bs := by
  simp only [dlb_blocksL, List.map_cons, List.flatten_cons]

/-- The orbit of a state loop is the iterate of the step with the retained input. -/
private theorem dlb_orbit_eq (start step : List Bool → List Bool) (x : List Bool) (i : ℕ) :
    StateLoop.orbit start step x i = (fun s => step (pairEncode x s))^[i] (start x) := by
  induction i with
  | zero => rw [StateLoop.orbit_zero, Function.iterate_zero_apply]
  | succ i ih => rw [StateLoop.orbit_succ, ih, Function.iterate_succ_apply']

variable {S A n} {f root : List Bool}

/-- One trial on a state whose counter is nonempty and whose coins begin with a block. -/
private theorem dlb_iStep_cons (hS : (dlb_fuS f).length = S.coinLen n)
    (hA : (dlb_fuA f).length = A.coinLen n) (cs : List Bool) (k : ℕ)
    (b : S.Coins n × A.Coins n) (rest votes : List Bool) :
    dlb_iStep S A (pairEncode (pairEncode (pairEncode f root) cs)
        (pairEncode (List.replicate (k + 1) true) (pairEncode (List.ofFn b.1 ++ List.ofFn b.2 ++ rest) votes))) =
      pairEncode (List.replicate k true) (pairEncode rest
        (dlb_vote S A f root (List.ofFn b.1) (List.ofFn b.2) :: votes)) := by
  have h1 : (List.ofFn b.1).length = S.coinLen n := List.length_ofFn
  have h2 : (List.ofFn b.2).length = A.coinLen n := List.length_ofFn
  simp only [dlb_iStep, dlb_iCnt, dlb_iF, dlb_iRoot, dlb_iCs, dlb_iVotes, dlb_iSB, dlb_iCs1, dlb_iAB,
    dlb_iRest, pairFstD_pairEncode, pairSndD_pairEncode, List.replicate_succ, reduceCtorEq,
    if_false, List.tail_cons, hS, hA, List.append_assoc]
  rw [List.take_left' h1, List.drop_left' h1, List.take_left' h2, List.drop_left' h2]

/-- A state with an empty counter is fixed by the trial step. -/
private theorem dlb_iStep_nil (Y st : List Bool) :
    dlb_iStep S A (pairEncode Y (pairEncode [] st)) = pairEncode [] st := by
  simp only [dlb_iStep, dlb_iCnt, pairFstD_pairEncode, pairSndD_pairEncode, if_true]

/-- **The trial loop, round by round**: after `i ≤ |bs|` trials on the blocks `bs`, the counter
has `|bs| − i` marks, the coins are the remaining blocks, and the votes of the first `i` blocks
are prepended (last first). -/
private theorem dlb_iStep_iterate (hS : (dlb_fuS f).length = S.coinLen n)
    (hA : (dlb_fuA f).length = A.coinLen n) (cs rest : List Bool) :
    ∀ (i : ℕ) (bs : List (S.Coins n × A.Coins n)) (votes : List Bool), i ≤ bs.length →
      (fun s => dlb_iStep S A (pairEncode (pairEncode (pairEncode f root) cs) s))^[i]
          (pairEncode (List.replicate bs.length true) (pairEncode (dlb_blocksL S A n bs ++ rest) votes)) =
        pairEncode (List.replicate (bs.length - i) true)
          (pairEncode (dlb_blocksL S A n (bs.drop i) ++ rest)
            (((bs.take i).map fun b => dlb_vote S A f root (List.ofFn b.1) (List.ofFn b.2)).reverse ++ votes))
  | 0, bs, votes, _ => by simp
  | i + 1, [], votes, h => by simp at h
  | i + 1, b :: bs, votes, h => by
    rw [Function.iterate_succ_apply, List.length_cons, dlb_blocksL_cons, List.append_assoc,
      dlb_iStep_cons hS hA, dlb_iStep_iterate hS hA cs rest i bs _ (by simp at h; omega)]
    simp

/-- A state with an empty counter is fixed by every iterate of the trial step. -/
private theorem dlb_iStep_iterate_nil (Y st : List Bool) (m : ℕ) :
    (fun s => dlb_iStep S A (pairEncode Y s))^[m] (pairEncode [] st) = pairEncode [] st := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, dlb_iStep_nil, ih]

private theorem dlb_length_blocksL_drop (i : ℕ) (bs : List (S.Coins n × A.Coins n)) :
    (dlb_blocksL S A n (bs.drop i)).length ≤ (dlb_blocksL S A n bs).length := by
  conv_rhs => rw [← List.take_append_drop i bs]
  simp only [dlb_blocksL, List.map_append, List.flatten_append, List.length_append]
  omega

private theorem dlb_length_fuL_le (f : List Bool) : (dlb_fuL f).length ≤ f.length := by
  unfold dlb_fuL
  exact (length_pairSndD_le _).trans ((length_pairSndD_le _).trans
    ((length_pairSndD_le _).trans (length_pairSndD_le _)))

/-- **The trial loop's result**: on `⟨⟨f, root⟩, blocks ++ rest⟩` with `1^{|blocks|}` as the trial
count of `f`, the loop ends with an empty counter, the coins `rest` and the votes of all blocks
(last first). -/
private theorem dlb_inner_eq (hS : (dlb_fuS f).length = S.coinLen n)
    (hA : (dlb_fuA f).length = A.coinLen n) (bs : List (S.Coins n × A.Coins n))
    (hL : dlb_fuL f = List.replicate bs.length true) (rest : List Bool) :
    dlb_inner S A (pairEncode (pairEncode f root) (dlb_blocksL S A n bs ++ rest)) =
      pairEncode [] (pairEncode rest
        ((bs.map fun b => dlb_vote S A f root (List.ofFn b.1) (List.ofFn b.2)).reverse)) := by
  set cs := dlb_blocksL S A n bs ++ rest with hcs
  set Y := pairEncode (pairEncode f root) cs with hY
  have hstart : dlb_iStart Y = pairEncode (List.replicate bs.length true) (pairEncode cs []) := by
    simp only [dlb_iStart, hY, pairFstD_pairEncode, pairSndD_pairEncode, hL]
  set σ := fun s => dlb_iStep S A (pairEncode Y s) with hσ
  set fin := pairEncode ([] : List Bool) (pairEncode rest
    ((bs.map fun b => dlb_vote S A f root (List.ofFn b.1) (List.ofFn b.2)).reverse)) with hfin
  -- the orbit: the closed form up to `|bs|` trials, then stable
  have hsmall : ∀ i ≤ bs.length, σ^[i] (dlb_iStart Y) =
      pairEncode (List.replicate (bs.length - i) true)
        (pairEncode (dlb_blocksL S A n (bs.drop i) ++ rest)
          (((bs.take i).map fun b => dlb_vote S A f root (List.ofFn b.1) (List.ofFn b.2)).reverse ++ [])) :=
    fun i hi => by rw [hstart]; exact dlb_iStep_iterate hS hA cs rest i bs [] hi
  have hlarge : ∀ i, bs.length ≤ i → σ^[i] (dlb_iStart Y) = fin := by
    intro i hi
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hi
    rw [add_comm, Function.iterate_add_apply, hsmall _ le_rfl]
    simp only [Nat.sub_self, List.replicate_zero, List.drop_length, List.take_length,
      List.append_nil]
    exact dlb_iStep_iterate_nil _ _ m
  -- the length bound along the orbit
  have hlenY : 4 * f.length + cs.length + 6 ≤ Y.length := by
    simp only [hY, length_pairEncode]; omega
  have hfL : bs.length ≤ f.length := by
    have := dlb_length_fuL_le f
    rw [hL, List.length_replicate] at this
    exact this
  have hb : ∀ i, (StateLoop.orbit dlb_iStart (dlb_iStep S A) Y i).length ≤ dlb_iB.eval Y.length := by
    intro i
    rw [dlb_orbit_eq]
    simp only [dlb_iB, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    rcases le_or_gt i bs.length with hi | hi
    · rw [hsmall i hi]
      have h1 := dlb_length_blocksL_drop (S := S) (A := A) (n := n) i bs
      have h2 : cs.length = (dlb_blocksL S A n bs).length + rest.length := by
        rw [hcs, List.length_append]
      simp only [length_pairEncode, List.length_replicate, List.length_append, List.length_reverse,
        List.length_map, List.length_take, List.length_nil]
      have : min i bs.length ≤ bs.length := min_le_right _ _
      omega
    · rw [hlarge i hi.le]
      simp only [hfin, length_pairEncode, List.length_nil, List.length_reverse, List.length_map]
      have h2 : rest.length ≤ cs.length := by rw [hcs, List.length_append]; omega
      omega
  have hN : bs.length ≤ (pairEncode Y (dlb_iStart Y)).length := by
    rw [hstart]; simp only [length_pairEncode, List.length_replicate]; omega
  unfold dlb_inner
  rw [StateLoop.gstep_iterate_eq dlb_iStart (dlb_iStep S A) dlb_iB Y _ (fun i _ => hb i) _ le_rfl,
    pairSndD_pairEncode, dlb_orbit_eq, hlarge _ hN]

end InnerSpec

/-! ### The round loop's closed form (strings) -/

section OuterSpec
variable (S A : NUPPT) (n ℓ : ℕ)

/-- The coin string of a list of rounds, each a list of trial blocks. -/
private def dlb_roundsList (rs : List (List (S.Coins n × A.Coins n))) : List Bool :=
  (rs.map (dlb_blocksL S A n)).flatten

/-- The coin string of the rounds: round `j` is the blocks of its `ℓ` trials. -/
private def dlb_roundsL {k : ℕ} (c : Fin k → Fin ℓ → S.Coins n × A.Coins n) : List Bool :=
  dlb_roundsList S A n (List.ofFn fun j => List.ofFn (c j))

private theorem dlb_roundsList_cons (r : List (S.Coins n × A.Coins n))
    (rs : List (List (S.Coins n × A.Coins n))) :
    dlb_roundsList S A n (r :: rs) = dlb_blocksL S A n r ++ dlb_roundsList S A n rs := by
  simp only [dlb_roundsList, List.map_cons, List.flatten_cons]

/-- Euler's test on a numeral, from the fixed data. -/
private def dlb_qrF (f y : List Bool) : Bool :=
  (leStr (pairEncode (dlb_powMod y (dlb_feH f) (dlb_fp f)) dlb_one)).headD false &&
    (leStr (pairEncode dlb_one (dlb_powMod y (dlb_feH f) (dlb_fp f)))).headD false

/-- The root of a numeral, from the fixed data. -/
private def dlb_rootF (f y : List Bool) : List Bool :=
  dlb_powMod (if dlb_qrF f y = true then y else dlb_mulMod y (dlb_fgI f) (dlb_fp f)) (dlb_feR f)
    (dlb_fp f)

variable {S A n ℓ} {f : List Bool}

private theorem dlb_oQr_eq (s0 y st : List Bool) :
    dlb_oQr (pairEncode (pairEncode f s0) (pairEncode y st)) = dlb_qrF f y := by
  simp only [dlb_oQr, dlb_oEul, dlb_qrF, dlb_oY, dlb_oF, pairFstD_pairEncode, pairSndD_pairEncode]

private theorem dlb_oRoot_eq (s0 y st : List Bool) :
    dlb_oRoot (pairEncode (pairEncode f s0) (pairEncode y st)) = dlb_rootF f y := by
  simp only [dlb_oRoot, dlb_oBase, dlb_rootF, dlb_oQr_eq, dlb_oY, dlb_oF, pairFstD_pairEncode,
    pairSndD_pairEncode]

/-- One round on a state whose counter is nonempty and whose coins begin with `ℓ` blocks. -/
private theorem dlb_oStep_cons (hS : (dlb_fuS f).length = S.coinLen n)
    (hA : (dlb_fuA f).length = A.coinLen n) (bs : List (S.Coins n × A.Coins n))
    (hL : dlb_fuL f = List.replicate bs.length true) (s0 y acc rest : List Bool) (m : ℕ) :
    dlb_oStep S A (pairEncode (pairEncode f s0) (pairEncode y (pairEncode acc
        (pairEncode (List.replicate (m + 1) true) (dlb_blocksL S A n bs ++ rest))))) =
      pairEncode
        (if decide ((bs.map fun b => dlb_vote S A f (dlb_rootF f y) (List.ofFn b.1) (List.ofFn b.2)).length <
            2 * (bs.map fun b => dlb_vote S A f (dlb_rootF f y) (List.ofFn b.1) (List.ofFn b.2)).count true)
          then dlb_rootF f y else subStr (pairEncode (dlb_fp f) (dlb_rootF f y)))
        (pairEncode ((!dlb_qrF f y) :: acc) (pairEncode (List.replicate m true) rest)) := by
  have hfin : dlb_oFin S A (pairEncode (pairEncode f s0) (pairEncode y (pairEncode acc
      (pairEncode (List.replicate (m + 1) true) (dlb_blocksL S A n bs ++ rest))))) =
      pairEncode [] (pairEncode rest
        ((bs.map fun b => dlb_vote S A f (dlb_rootF f y) (List.ofFn b.1) (List.ofFn b.2)).reverse)) := by
    unfold dlb_oFin
    rw [dlb_oRoot_eq]
    simp only [dlb_oF, dlb_oCs, pairFstD_pairEncode, pairSndD_pairEncode]
    exact dlb_inner_eq hS hA bs hL rest
  unfold dlb_oStep dlb_oNext dlb_oB dlb_oVotes
  rw [hfin, dlb_oRoot_eq, dlb_oQr_eq]
  simp only [dlb_oCnt, dlb_oAcc, dlb_oF, pairFstD_pairEncode, pairSndD_pairEncode,
    List.replicate_succ, reduceCtorEq, if_false, List.tail_cons, List.length_reverse,
    List.count_reverse]

/-- A round state with an empty counter is fixed by the round step. -/
private theorem dlb_oStep_nil (X y acc cs : List Bool) :
    dlb_oStep S A (pairEncode X (pairEncode y (pairEncode acc (pairEncode [] cs)))) =
      pairEncode y (pairEncode acc (pairEncode [] cs)) := by
  simp only [dlb_oStep, dlb_oCnt, pairFstD_pairEncode, pairSndD_pairEncode, if_true]

private theorem dlb_oStep_iterate_nil (X y acc cs : List Bool) (m : ℕ) :
    (fun s => dlb_oStep S A (pairEncode X s))^[m] (pairEncode y (pairEncode acc (pairEncode [] cs))) =
      pairEncode y (pairEncode acc (pairEncode [] cs)) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, dlb_oStep_nil, ih]

/-- **The round loop's shape**: after `i ≤ |rs₀|` rounds from `⟨y, ⟨[], ⟨1^{|rs₀|}, rounds ++ rest⟩⟩⟩`
the state is `⟨⟦v⟧_n, ⟨acc, ⟨1^{|rs|}, rounds' ++ rest⟩⟩⟩` with `|acc| = i`, `|rs| = |rs₀| − i` and
`rs` a suffix-sized list of full rounds (used for the length bound of the guarded loop). -/
private theorem dlb_oStep_shape (hS : (dlb_fuS f).length = S.coinLen n)
    (hA : (dlb_fuA f).length = A.coinLen n) (hL : dlb_fuL f = List.replicate ℓ true)
    (hp : (dlb_fp f).length = n) (s0 rest : List Bool) (rs₀ : List (List (S.Coins n × A.Coins n))) (s : List Bool) :
    ∀ i ≤ rs₀.length, (∃ v acc rs, rs.length = rs₀.length - i ∧ acc.length = i ∧
        (∀ r ∈ rs, r.length = ℓ) ∧ (dlb_roundsList S A n rs).length ≤ (dlb_roundsList S A n rs₀).length ∧
        s = pairEncode (natToList n v) (pairEncode acc (pairEncode (List.replicate rs.length true)
          (dlb_roundsList S A n rs ++ rest)))) →
      i < rs₀.length →
      ∃ v acc rs, rs.length = rs₀.length - (i + 1) ∧ acc.length = i + 1 ∧
        (∀ r ∈ rs, r.length = ℓ) ∧ (dlb_roundsList S A n rs).length ≤ (dlb_roundsList S A n rs₀).length ∧
        dlb_oStep S A (pairEncode (pairEncode f s0) s) =
          pairEncode (natToList n v) (pairEncode acc (pairEncode (List.replicate rs.length true)
            (dlb_roundsList S A n rs ++ rest))) := by
  intro i _ ⟨v, acc, rs, hlen, hacc, hrs, hle, hs⟩ hi
  obtain ⟨r, rs', rfl⟩ : ∃ r rs', rs = r :: rs' := by
    cases rs with
    | nil => simp at hlen; omega
    | cons r rs' => exact ⟨r, rs', rfl⟩
  have hr : r.length = ℓ := hrs r (by simp)
  rw [hs, List.length_cons, dlb_roundsList_cons, List.append_assoc,
    dlb_oStep_cons hS hA r (by rw [hr, hL]) s0 _ acc _ rs'.length]
  have hroot : ∃ w, dlb_rootF f (natToList n v) = natToList n w := by
    unfold dlb_rootF dlb_powMod
    rw [modExpStr_pairEncode, hp]
    exact ⟨_, rfl⟩
  obtain ⟨w, hw⟩ := hroot
  have hnext : ∀ c : Prop, [Decidable c] → ∃ w', (if c then dlb_rootF f (natToList n v)
      else subStr (pairEncode (dlb_fp f) (dlb_rootF f (natToList n v)))) = natToList n w' := by
    intro c _
    split_ifs
    · exact ⟨w, hw⟩
    · exact ⟨_, by rw [subStr_pairEncode, hp]⟩
  obtain ⟨w', hw'⟩ := hnext (decide ((r.map fun b => dlb_vote S A f (dlb_rootF f (natToList n v))
    (List.ofFn b.1) (List.ofFn b.2)).length < 2 * (r.map fun b => dlb_vote S A f
    (dlb_rootF f (natToList n v)) (List.ofFn b.1) (List.ofFn b.2)).count true) = true)
  have hlen' : rs'.length = rs₀.length - (i + 1) := by
    rw [List.length_cons] at hlen; omega
  refine ⟨w', (!dlb_qrF f (natToList n v)) :: acc, rs', hlen', by rw [List.length_cons, hacc],
    fun r' hr' => hrs r' (List.mem_cons_of_mem _ hr'), ?_, by rw [hw']⟩
  refine le_trans ?_ hle
  rw [dlb_roundsList_cons, List.length_append]
  omega

/-- **The round loop's result** (strings): from `⟨⟦v₀⟧_n, ⟨[], ⟨1^{|rs₀|}, rounds ++ rest⟩⟩⟩` the loop
returns the state after exactly `|rs₀|` round steps. -/
private theorem dlb_outer_eq (hS : (dlb_fuS f).length = S.coinLen n)
    (hA : (dlb_fuA f).length = A.coinLen n) (hL : dlb_fuL f = List.replicate ℓ true)
    (hp : (dlb_fp f).length = n) (v₀ : ℕ) (rest : List Bool)
    (rs₀ : List (List (S.Coins n × A.Coins n))) (hrs₀ : ∀ r ∈ rs₀, r.length = ℓ) :
    dlb_outer S A (pairEncode f (pairEncode (natToList n v₀) (pairEncode [] (pairEncode
        (List.replicate rs₀.length true) (dlb_roundsList S A n rs₀ ++ rest))))) =
      (fun s => dlb_oStep S A (pairEncode (pairEncode f (pairEncode (natToList n v₀) (pairEncode []
          (pairEncode (List.replicate rs₀.length true) (dlb_roundsList S A n rs₀ ++ rest))))) s))^[rs₀.length]
        (pairEncode (natToList n v₀) (pairEncode [] (pairEncode (List.replicate rs₀.length true)
          (dlb_roundsList S A n rs₀ ++ rest)))) := by
  set s0 := pairEncode (natToList n v₀) (pairEncode [] (pairEncode (List.replicate rs₀.length true)
    (dlb_roundsList S A n rs₀ ++ rest))) with hs0
  set X := pairEncode f s0 with hX
  set σ := fun s => dlb_oStep S A (pairEncode X s) with hσ
  have hinv : ∀ i ≤ rs₀.length, ∃ v acc rs, rs.length = rs₀.length - i ∧ acc.length = i ∧
      (∀ r ∈ rs, r.length = ℓ) ∧ (dlb_roundsList S A n rs).length ≤ (dlb_roundsList S A n rs₀).length ∧
      σ^[i] s0 = pairEncode (natToList n v) (pairEncode acc (pairEncode (List.replicate rs.length true)
        (dlb_roundsList S A n rs ++ rest))) := by
    intro i hi
    induction i with
    | zero => exact ⟨v₀, [], rs₀, by simp, rfl, hrs₀, le_rfl, rfl⟩
    | succ i ih =>
      obtain ⟨v, acc, rs, h1, h2, h3, h4, h5⟩ := ih (by omega)
      rw [Function.iterate_succ_apply', h5]
      exact dlb_oStep_shape hS hA hL hp s0 rest rs₀ _ i (by omega) ⟨v, acc, rs, h1, h2, h3, h4, rfl⟩
        (by omega)
  have hstable : ∀ i, rs₀.length ≤ i → σ^[i] s0 = σ^[rs₀.length] s0 := by
    intro i hi
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hi
    obtain ⟨v, acc, rs, h1, -, -, -, h5⟩ := hinv rs₀.length le_rfl
    have hrs : rs = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [add_comm, Function.iterate_add_apply, h5, hrs]
    exact dlb_oStep_iterate_nil X _ _ _ m
  have hlen0 : s0.length = 2 * n + 2 + 2 + 2 * rs₀.length + 2 +
      (dlb_roundsList S A n rs₀ ++ rest).length := by
    simp only [hs0, length_pairEncode, length_natToList, List.length_nil, List.length_replicate]
    omega
  have hbnd : ∀ i ≤ rs₀.length, (σ^[i] s0).length ≤ s0.length := by
    intro i hi
    obtain ⟨v, acc, rs, h1, h2, -, h4, h5⟩ := hinv i hi
    rw [h5, hlen0]
    simp only [length_pairEncode, length_natToList, List.length_replicate, List.length_append]
    simp only [List.length_append] at hlen0
    omega
  have hb : ∀ i, (StateLoop.orbit pairSndD (dlb_oStep S A) X i).length ≤ dlb_oB'.eval X.length := by
    intro i
    rw [dlb_orbit_eq, ← hσ]
    simp only [dlb_oB', PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    have hX' : s0.length ≤ X.length := by
      have := length_pairEncode f s0; rw [← hX] at this; omega
    have hpX : pairSndD X = s0 := by rw [hX, pairSndD_pairEncode]
    rw [hpX]
    rcases le_or_gt i rs₀.length with hi | hi
    · have := hbnd i hi; omega
    · rw [hstable i hi.le]; have := hbnd _ le_rfl; omega
  have hN : rs₀.length ≤ (pairEncode X (pairSndD X)).length := by
    have h1 := length_pairEncode X (pairSndD X)
    have h2 : pairSndD X = s0 := by rw [hX, pairSndD_pairEncode]
    rw [h2] at h1; rw [h2, h1, hlen0]; omega
  unfold dlb_outer
  have h2 : pairSndD X = s0 := by rw [hX, pairSndD_pairEncode]
  rw [StateLoop.gstep_iterate_eq pairSndD (dlb_oStep S A) dlb_oB' X _ (fun i _ => hb i) _ le_rfl,
    pairSndD_pairEncode, dlb_orbit_eq, ← hσ]
  rw [h2] at hN ⊢
  exact hstable _ hN

end OuterSpec

/-! ### The round step on numerals of units -/

section RoundSem
variable {n p : ℕ} [hp : Fact p.Prime] {f : List Bool}

private theorem dlb_val_lt (hpn : p < 2 ^ n) (u : (ZMod p)ˣ) : (u : ZMod p).val < 2 ^ n :=
  (ZMod.val_lt _).trans hpn

/-- Euler's test computes quadratic residuosity: `qrF f ⟦u⟧ = [u ∈ QR_p]` for an odd prime `p`
(`ZMod.euler_criterion_units`, `val_units_pow`). -/
private theorem dlb_qrF_eq (hp2 : p ≠ 2) (hpn : p < 2 ^ n) (hfp : dlb_fp f = natToList n p)
    (hfeH : dlb_feH f = natToList n ((p - 1) / 2)) (u : (ZMod p)ˣ) :
    dlb_qrF f (natToList n (u : ZMod p).val) = decide (u ∈ QR p) := by
  have h2 := hp.out.two_le
  have hhalf : p / 2 = (p - 1) / 2 := by
    obtain ⟨k, hk⟩ := hp.out.eq_two_or_odd'.resolve_left hp2
    omega
  haveI : Fact (1 < p) := ⟨by omega⟩
  unfold dlb_qrF
  rw [hfp, hfeH, dlb_powMod_natToList n (dlb_val_lt hpn u) (by omega) hpn, leStr_pairEncode,
    leStr_pairEncode, listToNat_natToList (lt_of_lt_of_le (Nat.mod_lt _ (by omega)) hpn.le),
    dlb_listToNat_one]
  simp only [List.headD_cons]
  rw [← val_units_pow]
  have key : ((u ^ ((p - 1) / 2) : (ZMod p)ˣ) : ZMod p).val = 1 ↔ u ^ ((p - 1) / 2) = 1 := by
    rw [Units.ext_iff, Units.val_one]
    constructor
    · intro h; apply ZMod.val_injective p; rw [h, ZMod.val_one]
    · intro h; rw [h, ZMod.val_one]
  have hiff : u ∈ QR p ↔ ((u ^ ((p - 1) / 2) : (ZMod p)ˣ) : ZMod p).val = 1 := by
    rw [mem_QR_iff, ZMod.euler_criterion_units, hhalf, key]
  rw [← Bool.decide_and]
  refine decide_eq_decide.2 ?_
  rw [hiff]
  constructor
  · intro h; omega
  · intro h; omega

/-- The root step computes `dlRoot`: `rootF f ⟦u⟧ = ⟦dlRoot g u⟧` (`dlb_qrF_eq`; `mulMod` is the
product of units, `powMod` their power, `val_units_pow`). -/
private theorem dlb_rootF_eq (hp2 : p ≠ 2) (hpn : p < 2 ^ n) (hfp : dlb_fp f = natToList n p)
    (hfeH : dlb_feH f = natToList n ((p - 1) / 2)) (hfeR : dlb_feR f = natToList (n + 1) (p / 4 + 1))
    (g : (ZMod p)ˣ) (hfgI : dlb_fgI f = natToList n ((g⁻¹ : (ZMod p)ˣ) : ZMod p).val) (u : (ZMod p)ˣ) :
    dlb_rootF f (natToList n (u : ZMod p).val) = natToList n ((dlRoot g u : (ZMod p)ˣ) : ZMod p).val := by
  have hp0 : p ≠ 0 := hp.out.ne_zero
  haveI : NeZero p := ⟨hp0⟩
  have hb : ∀ v : (ZMod p)ˣ, dlb_powMod (natToList n (v : ZMod p).val) (dlb_feR f) (dlb_fp f) =
      natToList n ((v ^ (p / 4 + 1) : (ZMod p)ˣ) : ZMod p).val := by
    intro v
    have hk : p / 4 + 1 < 2 ^ (n + 1) := by
      have : p < 2 ^ (n + 1) := hpn.trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
      omega
    rw [hfeR, hfp, dlb_powMod_natToList (n + 1) (dlb_val_lt hpn v) hk hpn, val_units_pow]
  unfold dlb_rootF dlRoot
  rw [dlb_qrF_eq hp2 hpn hfp hfeH u]
  by_cases hq : u ∈ QR p
  · rw [decide_eq_true hq, if_pos rfl, if_pos hq]
    exact hb u
  · rw [decide_eq_false hq, if_neg Bool.false_ne_true, if_neg hq]
    rw [hfgI, hfp, dlb_mulMod_natToList (dlb_val_lt hpn u) (dlb_val_lt hpn _) hpn]
    have hm : (u : ZMod p).val * ((g⁻¹ : (ZMod p)ˣ) : ZMod p).val % p =
        ((u * g⁻¹ : (ZMod p)ˣ) : ZMod p).val := by
      rw [Units.val_mul, ZMod.val_mul]
    rw [hm, ← hfp]
    exact hb _

end RoundSem

/-! ### Bits and counts -/

private theorem dlb_foldl_bits (l : List Bool) (a : ℕ) :
    l.foldl (fun a c => 2 * a + if c then 1 else 0) a =
      a * 2 ^ l.length + l.foldl (fun a c => 2 * a + if c then 1 else 0) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, ih (2 * 0 + _)]
    ring

/-- Prepending a bit to a numeral (most significant first): `⟦b :: l⟧ = b·2^{|l|} + ⟦l⟧`. -/
private theorem dlb_listToNat_cons (b : Bool) (l : List Bool) :
    listToNat (b :: l) = (if b then 1 else 0) * 2 ^ l.length + listToNat l := by
  rw [listToNat_eq, listToNat_eq, List.foldl_cons, dlb_foldl_bits]
  simp

/-- The number of `true`s in `List.ofFn v` is the number of indices where `v` is `true`. -/
private theorem dlb_count_ofFn {M : ℕ} (v : Fin M → Bool) :
    (List.ofFn v).count true = #(univ.filter fun j : Fin M => v j = true) := by
  rw [Finset.card_filter]
  induction M with
  | zero => simp
  | succ M ih =>
    rw [List.ofFn_succ, List.count_cons, ih (fun j => v j.succ), Fin.sum_univ_succ]
    cases v 0 <;> simp [add_comm]

/-- **The majority of an odd number of votes is the strict majority**: for `|κ|` odd,
`majority v = [|κ| < 2·#{v = true}]`, read off `HardcoreBit.two_mul_card_le_of_majority_ne`
(ties cannot occur). -/
private theorem dlb_majority_eq_of_odd {κ : Type*} [Fintype κ] (v : κ → Bool)
    (hodd : Fintype.card κ % 2 = 1) :
    HardcoreBit.majority v = decide (Fintype.card κ < 2 * #(univ.filter fun j => v j = true)) := by
  classical
  have hsplit := filter_card_add_filter_neg_card_eq_card (s := univ) (fun j => v j = true)
  have hneg : (univ.filter fun j => ¬ v j = true) = univ.filter fun j => v j = false := by
    ext j; simp
  rw [hneg, card_univ] at hsplit
  cases hm : HardcoreBit.majority v
  · have := HardcoreBit.two_mul_card_le_of_majority_ne v true (by rw [hm]; decide)
    symm; rw [decide_eq_false_iff_not]; omega
  · have := HardcoreBit.two_mul_card_le_of_majority_ne v false (by rw [hm]; decide)
    symm; rw [decide_eq_true_eq]; omega

/-! ### One trial on a decoded block -/

section VoteSem
variable (H : ArithmeticFP) (G : FullGroupGen) (A : NUPPT)

/-- The predictor of the concrete layer at the index `i`: `A_i y ρ = A(1^n, ⟨i, ⟦y⟧_n⟩; ρ)`. -/
private def dlb_Ai (n : ℕ) (i : List Bool) (p : ℕ) (y : (ZMod p)ˣ) (ρ : A.Coins n) : Bool :=
  A.distinguisherL n (pairEncode i (natToList n (y : ZMod p).val)) ρ

/-- **One trial computes the vote of `majOracle`**: on a sampler block that decodes to `x₀`
(so the sampled numeral is `⟦e⟧_n` with `e = φ x₀`, `encD_decD`), the machine's vote is
`[A_i(r · g^e) = half_{p−1}(e)]`. -/
private theorem dlb_vote_eq {n p gN : ℕ} [Fact p.Prime] {i f : List Bool} (hpn : p < 2 ^ n)
    (hfu : dlb_fu f = List.replicate n true) (hfi : dlb_fi f = i) (hfα : dlb_fα f = A.advice n)
    (hiP : pairFstD i = natToList n p) (hiG : pairSndD (pairSndD i) = natToList n gN)
    (hW : dlW i = n) (e : expOrd i = p - 1) (g : (ZMod p)ˣ) (hg : (g : ZMod p).val = gN)
    (s : (fullDLCollection H G).sample.Coins n) (ρ : A.Coins n) (x₀ : (fullDLCollection H G).D i)
    (hdec : (fullDLCollection H G).decD i ((fullDLCollection H G).sample.runAt n i s) = some x₀)
    (r : (ZMod p)ˣ) :
    dlb_vote (fullDLCollection H G).sample A f (natToList n (r : ZMod p).val) (List.ofFn s)
        (List.ofFn ρ) =
      decide (dlb_Ai A n i p (r * g ^ (ZMod.ringEquivCongr e (fullDLCollection_domEquiv H G i x₀)).val) ρ =
        halfBit (p - 1) (ZMod.ringEquivCongr e (fullDLCollection_domEquiv H G i x₀))) := by
  have hp1 := (Fact.out : p.Prime).two_le
  haveI : NeZero p := ⟨by omega⟩
  haveI : NeZero (p - 1) := ⟨by omega⟩
  set v := (fullDLCollection_domEquiv H G i x₀).val with hv
  have hve : (ZMod.ringEquivCongr e (fullDLCollection_domEquiv H G i x₀)).val = v :=
    ZMod.ringEquivCongr_val e _
  have hvlt : v < p - 1 := by
    have := ZMod.val_lt (ZMod.ringEquivCongr e (fullDLCollection_domEquiv H G i x₀))
    rwa [hve] at this
  have hw : (fullDLCollection H G).sample.runAt n i s = natToList n v := by
    rw [← (fullDLCollection H G).encD_decD i _ x₀ hdec, fullDLCollection_encD, expEnc_eq, hW]
  have hwS : dlb_wS (fullDLCollection H G).sample f (List.ofFn s) = natToList n v := by
    unfold dlb_wS
    rw [hfu, hfi, ← hw, NUPPT.Uniform.runAt_eq (fullDLCollection H G).sample_uniform,
      NUPPT.layout_eq, NUPPT.advInput_eq]
  have hzz : dlb_zz (fullDLCollection H G).sample f (natToList n (r : ZMod p).val) (List.ofFn s) =
      natToList n ((r * g ^ v : (ZMod p)ˣ) : ZMod p).val := by
    unfold dlb_zz dlb_fg dlb_fp
    rw [hwS, hfi, hiG, hiP, dlb_powMod_natToList n (hg ▸ dlb_val_lt hpn g) (by omega) hpn,
      dlb_mulMod_natToList (dlb_val_lt hpn r) ((Nat.mod_lt _ (by omega)).trans hpn) hpn,
      Units.val_mul, ZMod.val_mul, val_units_pow, hg]
  have hab : dlb_aBit (fullDLCollection H G).sample A f (natToList n (r : ZMod p).val) (List.ofFn s)
      (List.ofFn ρ) = dlb_Ai A n i p (r * g ^ v) ρ := by
    unfold dlb_aBit dlb_Ai
    rw [hzz, hfu, hfi, hfα, NUPPT.distinguisherL_eq, NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout]
  have hh : halfStr (pairEncode (dlb_fi f) (dlb_wS (fullDLCollection H G).sample f (List.ofFn s))) =
      [decide (2 * v + 2 ≤ p)] := by
    rw [hwS, hfi]
    unfold halfStr
    rw [pairSndD_pairEncode, pairFstD_pairEncode, hiP, listToNat_natToList (by omega),
      listToNat_natToList hpn]
  unfold dlb_vote
  rw [hab, hh, hve]
  unfold halfBit
  rw [hve]
  have : decide (2 * v + 2 ≤ p) = decide (2 * v < p - 1) := decide_eq_decide.2 (by omega)
  rw [this]
  simp only [List.cons.injEq, and_true]

end VoteSem

/-! ### The round loop on numerals of units -/

section LoopSem
variable (H : ArithmeticFP) (G : FullGroupGen) (A : NUPPT)

/-- The exponent decoded from a sampler block, in `Z_{p−1}` (`0` if the block does not decode). -/
private noncomputable def dlb_dec (n : ℕ) (i : List Bool) {p : ℕ} (e : expOrd i = p - 1)
    (s : (fullDLCollection H G).sample.Coins n) : ZMod (p - 1) :=
  (((fullDLCollection H G).decD i ((fullDLCollection H G).sample.runAt n i s)).map
    fun x => ZMod.ringEquivCongr e (fullDLCollection_domEquiv H G i x)).getD 0

/-- Every sampler block of a trial vector decodes. -/
private def dlb_Decodes (n : ℕ) (i : List Bool) {ℓ : ℕ}
    (bs : Fin ℓ → (fullDLCollection H G).sample.Coins n × A.Coins n) : Prop :=
  ∀ k, ((fullDLCollection H G).decD i ((fullDLCollection H G).sample.runAt n i (bs k).1)).isSome

/-- The ideal coins of a round: the decoded exponents with the predictor's coins. -/
private noncomputable def dlb_idealRound (n : ℕ) (i : List Bool) {p ℓ : ℕ} (e : expOrd i = p - 1)
    (bs : Fin ℓ → (fullDLCollection H G).sample.Coins n × A.Coins n) :
    Fin ℓ → ZMod (p - 1) × A.Coins n :=
  fun k => (dlb_dec H G n i e (bs k).1, (bs k).2)

variable {H G A} {n p gN ℓ : ℕ} [hp : Fact p.Prime] {i f : List Bool} {e : expOrd i = p - 1}
  {g : (ZMod p)ˣ}

private theorem dlb_vote_dec (hpn : p < 2 ^ n)
    (hfu : dlb_fu f = List.replicate n true) (hfi : dlb_fi f = i) (hfα : dlb_fα f = A.advice n)
    (hiP : pairFstD i = natToList n p) (hiG : pairSndD (pairSndD i) = natToList n gN)
    (hW : dlW i = n) (hg : (g : ZMod p).val = gN)
    (b : (fullDLCollection H G).sample.Coins n × A.Coins n)
    (hb : ((fullDLCollection H G).decD i ((fullDLCollection H G).sample.runAt n i b.1)).isSome)
    (r : (ZMod p)ˣ) :
    dlb_vote (fullDLCollection H G).sample A f (natToList n (r : ZMod p).val) (List.ofFn b.1)
        (List.ofFn b.2) =
      decide (dlb_Ai A n i p (r * g ^ (dlb_dec H G n i e b.1).val) b.2 =
        halfBit (p - 1) (dlb_dec H G n i e b.1)) := by
  obtain ⟨x₀, hx₀⟩ := Option.isSome_iff_exists.1 hb
  have hd : dlb_dec H G n i e b.1 = ZMod.ringEquivCongr e (fullDLCollection_domEquiv H G i x₀) := by
    unfold dlb_dec; rw [hx₀]; rfl
  rw [hd]
  exact dlb_vote_eq H G A hpn hfu hfi hfα hiP hiG hW e g hg b.1 b.2 x₀ hx₀ r

/-- **One round of the machine is one round of `dlLoop`** with the majority test on the decoded
coins: the kept root is `±dlRoot g y` as `majOracle` decides, and the recorded bit is the
parity bit `[y ∉ QR_p]` (`dlb_oStep_cons`, `dlb_qrF_eq`, `dlb_rootF_eq`, `dlb_vote_dec`,
`dlb_majority_eq_of_odd` for the odd trial count). -/
private theorem dlb_oStep_round (hp2 : p ≠ 2) (hpn : p < 2 ^ n) (hodd : ℓ % 2 = 1)
    (hfu : dlb_fu f = List.replicate n true) (hfi : dlb_fi f = i) (hfα : dlb_fα f = A.advice n)
    (hiP : pairFstD i = natToList n p) (hiG : pairSndD (pairSndD i) = natToList n gN)
    (hW : dlW i = n) (hg : (g : ZMod p).val = gN)
    (hS : (dlb_fuS f).length = (fullDLCollection H G).sample.coinLen n)
    (hA : (dlb_fuA f).length = A.coinLen n) (hL : dlb_fuL f = List.replicate ℓ true)
    (hfeH : dlb_feH f = natToList n ((p - 1) / 2)) (hfeR : dlb_feR f = natToList (n + 1) (p / 4 + 1))
    (hfgI : dlb_fgI f = natToList n ((g⁻¹ : (ZMod p)ˣ) : ZMod p).val)
    (bs : Fin ℓ → (fullDLCollection H G).sample.Coins n × A.Coins n)
    (hdec : dlb_Decodes H G A n i bs) (s0 acc rest : List Bool) (m : ℕ) (y : (ZMod p)ˣ) :
    dlb_oStep (fullDLCollection H G).sample A (pairEncode (pairEncode f s0)
        (pairEncode (natToList n (y : ZMod p).val) (pairEncode acc (pairEncode
          (List.replicate (m + 1) true) (dlb_blocksL _ A n (List.ofFn bs) ++ rest))))) =
      pairEncode (natToList n (((if majOracle g (dlb_Ai A n i p) ℓ (dlRoot g y)
          (dlb_idealRound H G A n i e bs) then dlRoot g y else -dlRoot g y : (ZMod p)ˣ) : ZMod p).val))
        (pairEncode ((!decide (y ∈ QR p)) :: acc) (pairEncode (List.replicate m true) rest)) := by
  have hp0 := hp.out.two_le
  haveI : NeZero p := ⟨by omega⟩
  have hfp : dlb_fp f = natToList n p := by unfold dlb_fp; rw [hfi, hiP]
  rw [dlb_oStep_cons hS hA (List.ofFn bs) (by rw [List.length_ofFn, hL]) s0 _ acc rest m,
    dlb_qrF_eq hp2 hpn hfp hfeH y, dlb_rootF_eq hp2 hpn hfp hfeH hfeR g hfgI y]
  -- the votes are those of `majOracle`
  have hvotes : ((List.ofFn bs).map fun b => dlb_vote (fullDLCollection H G).sample A f
      (natToList n ((dlRoot g y : (ZMod p)ˣ) : ZMod p).val) (List.ofFn b.1) (List.ofFn b.2)) =
      List.ofFn fun k => decide (dlb_Ai A n i p (dlRoot g y * g ^ (dlb_idealRound H G A n i e bs k).1.val)
        (dlb_idealRound H G A n i e bs k).2 = halfBit (p - 1) (dlb_idealRound H G A n i e bs k).1) := by
    rw [List.map_ofFn]
    congr 1
    funext k
    exact dlb_vote_dec hpn hfu hfi hfα hiP hiG hW hg (bs k) (hdec k) _
  have hmaj : decide (((List.ofFn bs).map fun b => dlb_vote (fullDLCollection H G).sample A f
      (natToList n ((dlRoot g y : (ZMod p)ˣ) : ZMod p).val) (List.ofFn b.1) (List.ofFn b.2)).length <
      2 * ((List.ofFn bs).map fun b => dlb_vote (fullDLCollection H G).sample A f
      (natToList n ((dlRoot g y : (ZMod p)ˣ) : ZMod p).val) (List.ofFn b.1) (List.ofFn b.2)).count true) =
      majOracle g (dlb_Ai A n i p) ℓ (dlRoot g y) (dlb_idealRound H G A n i e bs) := by
    rw [hvotes, List.length_ofFn, dlb_count_ofFn]
    unfold majOracle
    rw [dlb_majority_eq_of_odd _ (by rw [Fintype.card_fin]; exact hodd), Fintype.card_fin]
  rw [hmaj]
  congr 1
  split_ifs with hb
  · rfl
  · rw [hfp, subStr_pairEncode, length_natToList, listToNat_natToList hpn,
      listToNat_natToList (dlb_val_lt hpn _), Units.val_neg, ZMod.val_neg_of_ne_zero]

private theorem dlb_roundsL_succ {S A : NUPPT} {n ℓ k : ℕ} (c : Fin (k + 1) → Fin ℓ → S.Coins n × A.Coins n) :
    dlb_roundsL S A n ℓ c = dlb_blocksL S A n (List.ofFn (c 0)) ++ dlb_roundsL S A n ℓ (fun j => c j.succ) := by
  simp only [dlb_roundsL, List.ofFn_succ, dlb_roundsList_cons]

/-- **The machine's rounds are the rounds of `dlLoop`**: after `k` rounds on `k` round blocks
whose sampler blocks all decode, the bits read `dlLoop g (majOracle g A_i ℓ) k y c·2^{|acc|} + ⟦acc⟧`
(induction on `k`, `dlb_oStep_round`, `dlLoop_succ`, `dlb_listToNat_cons`). -/
private theorem dlb_loop_sem (hp2 : p ≠ 2) (hpn : p < 2 ^ n) (hodd : ℓ % 2 = 1)
    (hfu : dlb_fu f = List.replicate n true) (hfi : dlb_fi f = i) (hfα : dlb_fα f = A.advice n)
    (hiP : pairFstD i = natToList n p) (hiG : pairSndD (pairSndD i) = natToList n gN)
    (hW : dlW i = n) (hg : (g : ZMod p).val = gN)
    (hS : (dlb_fuS f).length = (fullDLCollection H G).sample.coinLen n)
    (hA : (dlb_fuA f).length = A.coinLen n) (hL : dlb_fuL f = List.replicate ℓ true)
    (hfeH : dlb_feH f = natToList n ((p - 1) / 2)) (hfeR : dlb_feR f = natToList (n + 1) (p / 4 + 1))
    (hfgI : dlb_fgI f = natToList n ((g⁻¹ : (ZMod p)ˣ) : ZMod p).val) (s0 rest : List Bool) :
    ∀ (k : ℕ) (y : (ZMod p)ˣ) (acc : List Bool)
      (c : Fin k → Fin ℓ → (fullDLCollection H G).sample.Coins n × A.Coins n),
      (∀ j, dlb_Decodes H G A n i (c j)) →
      ∃ yv acc', (fun s => dlb_oStep (fullDLCollection H G).sample A (pairEncode (pairEncode f s0) s))^[k]
          (pairEncode (natToList n (y : ZMod p).val) (pairEncode acc (pairEncode (List.replicate k true)
            (dlb_roundsL _ A n ℓ c ++ rest)))) = pairEncode (natToList n yv) (pairEncode acc' (pairEncode [] rest)) ∧
        listToNat acc' = dlLoop g (majOracle g (dlb_Ai A n i p) ℓ) k y
          (fun j => dlb_idealRound H G A n i e (c j)) * 2 ^ acc.length + listToNat acc
  | 0, y, acc, c, _ => ⟨(y : ZMod p).val, acc, by simp [dlb_roundsL, dlb_roundsList], by simp [dlLoop]⟩
  | k + 1, y, acc, c, hdec => by
    rw [Function.iterate_succ_apply, dlb_roundsL_succ, List.append_assoc,
      dlb_oStep_round (e := e) hp2 hpn hodd hfu hfi hfα hiP hiG hW hg hS hA hL hfeH hfeR hfgI (c 0) (hdec 0)
        s0 acc _ k y]
    obtain ⟨yv, acc', h1, h2⟩ := dlb_loop_sem hp2 hpn hodd hfu hfi hfα hiP hiG hW hg hS hA hL hfeH hfeR
      hfgI s0 rest k _ ((!decide (y ∈ QR p)) :: acc) (fun j => c j.succ) (fun j => hdec j.succ)
    refine ⟨yv, acc', h1, ?_⟩
    rw [h2, dlLoop_succ, dlb_listToNat_cons, List.length_cons, pow_succ]
    by_cases hq : y ∈ QR p
    · simp only [hq, decide_true, Bool.not_true, Bool.false_eq_true, if_false, if_true]
      ring
    · simp only [hq, decide_false, Bool.not_false, if_true, if_false]
      ring

end LoopSem

/-! ### The inverter on a well-formed input -/

section RawSem
variable {H : ArithmeticFP} {G : FullGroupGen} {A : NUPPT} {ℓP : PolyExpr}
  {n p gN ℓ κ D : ℕ} [hp : Fact p.Prime] {i : List Bool} {e : expOrd i = p - 1} {g : (ZMod p)ˣ}

/-- **The inverter's string function computes `dlInverter`** on the input
`⟨⟨⟨1^n, ⟨i, ⟦y⟧_n⟩⟩, ⟨α_A, ⟨⟦D⟧_n, 1^κ⟩⟩⟩, ⟦t-block⟧ ++ rounds⟩` at a well-formed full-group index
whose sampler blocks all decode: the output is the `n`-bit numeral of
`shiftInverter g (dlLoop g (majOracle g A_i ℓ) n) ⌊(p−1)/D⌋ 2^κ y (t, c)` with `t` the first `κ`
coins and `c` the decoded rounds. -/
private theorem dlb_raw_sem (hp2 : p ≠ 2) (hpn : p < 2 ^ n) (hodd : ℓ % 2 = 1) (hℓ : ℓP.eval n = ℓ)
    (hκ : κ ≤ n) (hD : D < 2 ^ n)
    (hiP : pairFstD i = natToList n p) (hiG : pairSndD (pairSndD i) = natToList n gN)
    (hW : dlW i = n) (hg : (g : ZMod p).val = gN) (y : (ZMod p)ˣ) (tb : Fin n → Bool)
    (c : Fin n → Fin ℓ → (fullDLCollection H G).sample.Coins n × A.Coins n)
    (hdec : ∀ j, dlb_Decodes H G A n i (c j)) :
    dlb_raw (fullDLCollection H G).sample A ℓP (NUPPT.layout (List.replicate n true)
        (pairEncode i (natToList n (y : ZMod p).val))
        (pairEncode (A.advice n) (pairEncode (natToList n D) (List.replicate κ true)))
        (List.ofFn tb ++ dlb_roundsL _ A n ℓ c)) =
      natToList n (shiftInverter g (dlLoop g (majOracle g (dlb_Ai A n i p) ℓ) n) ((p - 1) / D) (2 ^ κ) y
        (⟨listToNat ((List.ofFn tb).take κ), by
            have := listToNat_lt_two_pow ((List.ofFn tb).take κ)
            rwa [List.length_take, List.length_ofFn, min_eq_left hκ] at this⟩,
          fun j => dlb_idealRound H G A n i e (c j))).val := by
  have hp0 := hp.out.two_le
  haveI : NeZero p := ⟨by omega⟩
  haveI : NeZero (p - 1) := ⟨by omega⟩
  set z := NUPPT.layout (List.replicate n true) (pairEncode i (natToList n (y : ZMod p).val))
    (pairEncode (A.advice n) (pairEncode (natToList n D) (List.replicate κ true)))
    (List.ofFn tb ++ dlb_roundsL (fullDLCollection H G).sample A n ℓ c) with hz
  set tv := listToNat ((List.ofFn tb).take κ) with htv
  have htlt : tv < 2 ^ κ := by
    have := listToNat_lt_two_pow ((List.ofFn tb).take κ)
    rwa [List.length_take, List.length_ofFn, min_eq_left hκ] at this
  set sv := (p - 1) / D with hsv
  have hslt : sv < 2 ^ n := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  have hpm1lt : p - 1 < 2 ^ n := by omega
  -- the projections of the raw input
  have hu : NUPPT.inParam z = List.replicate n true := NUPPT.inParam_layout _ _ _ _
  have hzi : dlb_zi z = i := by unfold dlb_zi; rw [NUPPT.inArg_layout, pairFstD_pairEncode]
  have hzy : dlb_zy z = natToList n (y : ZMod p).val := by
    unfold dlb_zy; rw [NUPPT.inArg_layout, pairSndD_pairEncode]
  have hzα : dlb_zα z = A.advice n := by unfold dlb_zα; rw [NUPPT.inAdvice_layout, pairFstD_pairEncode]
  have hzD : dlb_zD z = natToList n D := by
    unfold dlb_zD; rw [NUPPT.inAdvice_layout, pairSndD_pairEncode, pairFstD_pairEncode]
  have hzκ : dlb_zκ z = List.replicate κ true := by
    unfold dlb_zκ; rw [NUPPT.inAdvice_layout, pairSndD_pairEncode, pairSndD_pairEncode]
  have hzc : NUPPT.inCoins z = List.ofFn tb ++ dlb_roundsL (fullDLCollection H G).sample A n ℓ c := NUPPT.inCoins_layout _ _ _ _
  have hzp : dlb_zp z = natToList n p := by unfold dlb_zp; rw [hzi, hiP]
  have hzg : dlb_zg z = natToList n gN := by unfold dlb_zg; rw [hzi, hiG]
  have hzpm1 : dlb_zpm1 z = natToList n (p - 1) := by
    unfold dlb_zpm1
    rw [hzp, subStr_pairEncode, length_natToList, listToNat_natToList hpn, dlb_listToNat_one]
  have hzs : dlb_zs z = natToList n sv := by
    unfold dlb_zs; rw [hzpm1, hzD, dlb_quot_natToList n hpm1lt hD]
  have hzt : dlb_zt z = (List.ofFn tb).take κ := by
    unfold dlb_zt
    rw [hzc, hzκ, List.length_replicate, List.take_append_of_le_length (by rw [List.length_ofFn]; exact hκ)]
  have hzts : dlb_zts z = natToList (κ + n) (tv * sv) := by
    unfold dlb_zts
    rw [hzt, hzs, mulStr_pairEncode, List.length_take, List.length_ofFn, min_eq_left hκ, length_natToList,
      listToNat_natToList hslt]
  have hgv : ((g : (ZMod p)ˣ) : ZMod p) = (gN : ZMod p) := by rw [← hg, ZMod.natCast_zmod_val]
  have hgts : dlb_powMod (dlb_zg z) (dlb_zts z) (dlb_zp z) =
      natToList n ((g ^ (tv * sv) : (ZMod p)ˣ) : ZMod p).val := by
    rw [hzg, hzts, hzp, dlb_powMod_natToList (κ + n) (hg ▸ dlb_val_lt hpn g)
      (by rw [pow_add]; exact Nat.mul_lt_mul'' htlt hslt) hpn, val_units_pow, hg]
  have hinv : ∀ u : (ZMod p)ˣ, dlb_invMod (natToList n (u : ZMod p).val) (natToList n p) =
      natToList n ((u⁻¹ : (ZMod p)ˣ) : ZMod p).val := by
    intro u
    rw [dlb_invMod_natToList (dlb_val_lt hpn u) hpn, ZMod.natCast_zmod_val, Units.val_inv_eq_inv_val]
  have hzy0 : dlb_zy0 z = natToList n ((y * (g ^ (tv * sv))⁻¹ : (ZMod p)ˣ) : ZMod p).val := by
    unfold dlb_zy0
    rw [hgts, hzp, hinv, hzy, dlb_mulMod_natToList (dlb_val_lt hpn y) (dlb_val_lt hpn _) hpn,
      Units.val_mul, ZMod.val_mul]
  -- the fixed data
  set f := dlb_zfix (fullDLCollection H G).sample A ℓP z with hf
  have hfix := dlb_fix_proj (NUPPT.inParam z) (dlb_zi z) (dlb_zα z) (dlb_invMod (dlb_zg z) (dlb_zp z))
    (dlb_quot (dlb_zpm1 z) dlb_two) (addStr (pairEncode (dlb_quot (dlb_zp z) dlb_four) dlb_one))
    (List.replicate ((fullDLCollection H G).sample.coins.eval (NUPPT.inParam z).length) true)
    (List.replicate (A.coins.eval (NUPPT.inParam z).length) true)
    (List.replicate (ℓP.eval (NUPPT.inParam z).length) true)
  rw [← dlb_zfix] at hfix
  obtain ⟨hfu, hfi, hfα, hfgI, hfeH, hfeR, hfuS, hfuA, hfuL⟩ := hfix
  rw [hu] at hfu hfuS hfuA hfuL
  rw [hzi] at hfi
  rw [hzα] at hfα
  rw [List.length_replicate] at hfuS hfuA hfuL
  have hfgI' : dlb_fgI f = natToList n ((g⁻¹ : (ZMod p)ˣ) : ZMod p).val := by
    rw [hfgI, hzg, hzp, ← hg, hinv]
  have hfeH' : dlb_feH f = natToList n ((p - 1) / 2) := by
    rw [hfeH, hzpm1, dlb_two, dlb_quot_natToList 2 hpm1lt (by norm_num)]
  have hfeR' : dlb_feR f = natToList (n + 1) (p / 4 + 1) := by
    rw [hfeR, hzp, dlb_four, dlb_quot_natToList 3 hpn (by norm_num), addStr_pairEncode,
      length_natToList, dlb_one, length_natToList, listToNat_natToList (by norm_num : 1 < 2 ^ 1),
      listToNat_natToList (lt_of_le_of_lt (Nat.div_le_self _ _) hpn)]
  have hfp : (dlb_fp f).length = n := by unfold dlb_fp; rw [hfi, hiP, length_natToList]
  have hS : (dlb_fuS f).length = (fullDLCollection H G).sample.coinLen n := by rw [hfuS, List.length_replicate, NUPPT.coinLen_eq]
  have hA : (dlb_fuA f).length = A.coinLen n := by rw [hfuA, List.length_replicate, NUPPT.coinLen_eq]
  have hL : dlb_fuL f = List.replicate ℓ true := by rw [hfuL, hℓ]
  -- the round loop
  have hs0 : dlb_zs0 z = pairEncode (natToList n ((y * (g ^ (tv * sv))⁻¹ : (ZMod p)ˣ) : ZMod p).val)
      (pairEncode [] (pairEncode (List.replicate (List.ofFn fun j => List.ofFn (c j)).length true)
        (dlb_roundsList (fullDLCollection H G).sample A n (List.ofFn fun j => List.ofFn (c j)) ++ []))) := by
    unfold dlb_zs0
    rw [hzy0, hu, hzc, List.length_replicate, List.drop_left' (List.length_ofFn), List.length_ofFn,
      List.append_nil]
    rfl
  have hacc : dlb_zacc (fullDLCollection H G).sample A ℓP z = pairFstD (pairSndD ((fun s => dlb_oStep (fullDLCollection H G).sample A (pairEncode
      (pairEncode f (dlb_zs0 z)) s))^[n] (dlb_zs0 z))) := by
    unfold dlb_zacc
    rw [← hf]
    conv_lhs => rw [hs0]
    rw [dlb_outer_eq hS hA hL hfp _ [] _ (fun r hr => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hr; exact List.length_ofFn), ← hs0, List.length_ofFn]
  obtain ⟨yv, acc', h1, h2⟩ := dlb_loop_sem (e := e) hp2 hpn hodd hfu hfi hfα hiP hiG hW hg hS hA hL
    hfeH' hfeR' hfgI' (dlb_zs0 z) [] n _ [] c hdec
  have hs0' : dlb_zs0 z = pairEncode (natToList n ((y * (g ^ (tv * sv))⁻¹ : (ZMod p)ˣ) : ZMod p).val)
      (pairEncode [] (pairEncode (List.replicate n true) (dlb_roundsL (fullDLCollection H G).sample A n ℓ c ++ []))) := by
    rw [hs0, List.length_ofFn]; rfl
  rw [← hs0'] at h1
  rw [h1, pairSndD_pairEncode, pairFstD_pairEncode] at hacc
  -- the output
  have hraw : dlb_raw (fullDLCollection H G).sample A ℓP z = dlb_rem (addStr (pairEncode (dlb_zacc (fullDLCollection H G).sample A ℓP z) (dlb_zts z)))
      (dlb_zpm1 z) := rfl
  have hb := listToNat_add_lt_two_pow acc' (natToList (κ + n) (tv * sv))
  have htsv : tv * sv < 2 ^ (κ + n) := by rw [pow_add]; exact Nat.mul_lt_mul'' htlt hslt
  rw [listToNat_natToList htsv, length_natToList] at hb
  rw [hraw, hacc, hzts, hzpm1, addStr_pairEncode, length_natToList, listToNat_natToList htsv,
    dlb_rem_natToList _ hb hpm1lt]
  refine congrArg (natToList n) ?_
  have h0 : listToNat ([] : List Bool) = 0 := by rw [listToNat_eq]; rfl
  rw [h2, h0, List.length_nil, pow_zero, mul_one, add_zero]
  unfold shiftInverter
  rw [← Nat.cast_add, ZMod.val_natCast]

end RawSem

/-! ### The inverter's coins -/

section Coins
variable (S A : NUPPT) (n ℓ : ℕ)

/-- The decomposition of a coin string of length `n + n·ℓ·(|S| + |A|)` into the `t`-block and the
round blocks (`List.ofFn_add`, `List.ofFn_mul` layouts). -/
private def dlb_split {N : ℕ} (h : N = n + n * (ℓ * (S.coinLen n + A.coinLen n))) (r : Fin N → Bool) :
    (Fin n → Bool) × (Fin n → Fin ℓ → S.Coins n × A.Coins n) :=
  let r' : Fin (n + n * (ℓ * (S.coinLen n + A.coinLen n))) → Bool := fun q => r (Fin.cast h.symm q)
  (fun a => r' (a.castLE (Nat.le_add_right _ _)),
   fun j k =>
    let blk : Fin (S.coinLen n + A.coinLen n) → Bool := fun m =>
      r' (Fin.natAdd n ⟨(j : ℕ) * (ℓ * (S.coinLen n + A.coinLen n)) +
        ((k : ℕ) * (S.coinLen n + A.coinLen n) + m), by
          have hk := k.2; have hm := m.2; have hj := j.2
          calc (j : ℕ) * (ℓ * (S.coinLen n + A.coinLen n)) + ((k : ℕ) * (S.coinLen n + A.coinLen n) + m)
              < (j : ℕ) * (ℓ * (S.coinLen n + A.coinLen n)) + ((k : ℕ) + 1) * (S.coinLen n + A.coinLen n) := by
                rw [add_mul, one_mul]; omega
            _ ≤ (j : ℕ) * (ℓ * (S.coinLen n + A.coinLen n)) + ℓ * (S.coinLen n + A.coinLen n) := by
                gcongr; omega
            _ = ((j : ℕ) + 1) * (ℓ * (S.coinLen n + A.coinLen n)) := by ring
            _ ≤ n * (ℓ * (S.coinLen n + A.coinLen n)) := by gcongr; omega⟩)
    (fun a => blk (a.castLE (Nat.le_add_right _ _)), fun b => blk (b.natAdd _)))

private theorem dlb_ofFn_split {N : ℕ} (h : N = n + n * (ℓ * (S.coinLen n + A.coinLen n)))
    (r : Fin N → Bool) :
    List.ofFn r = List.ofFn (dlb_split S A n ℓ h r).1 ++ dlb_roundsL S A n ℓ (dlb_split S A n ℓ h r).2 := by
  subst h
  rw [List.ofFn_add, List.ofFn_mul]
  congr 1
  simp only [dlb_roundsL, dlb_roundsList, List.map_ofFn]
  congr 1
  refine List.ofFn_inj.2 (funext fun j => ?_)
  simp only [Function.comp_apply, dlb_blocksL]
  rw [List.ofFn_mul]
  congr 1
  rw [List.map_ofFn]
  refine List.ofFn_inj.2 (funext fun k => ?_)
  simp only [Function.comp_apply]
  rw [List.ofFn_add]
  rfl

private theorem dlb_split_bijective {N : ℕ} (h : N = n + n * (ℓ * (S.coinLen n + A.coinLen n))) :
    Function.Bijective (dlb_split S A n ℓ h) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨fun r r' hr => ?_, ?_⟩
  · apply List.ofFn_injective
    rw [dlb_ofFn_split S A n ℓ h r, dlb_ofFn_split S A n ℓ h r', hr]
  · simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, h]
    rw [← pow_add, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring

end Coins

/-! ### The inverter `B` as a non-uniform PPT -/

section Machine
variable (H : ArithmeticFP) (G : FullGroupGen) (A : NUPPT) (c : ℕ)

/-- The number of trials per round, `ℓ = 16 n^{2c+1} + 1` (odd, so that majorities have no ties). -/
private def dlb_ℓP : PolyExpr := .add (.mul (.const 16) (.pow .var (2 * c + 1))) (.const 1)

/-- The coins of `B`: `n` for the guess, and `n · ℓ` trial blocks of sampler and predictor coins. -/
private noncomputable def dlb_coinsP : PolyExpr :=
  .add .var (.mul .var (.mul (dlb_ℓP c) (.add (fullDLCollection H G).sample.coins A.coins)))

/-- The advice of `B`: `⟨A.advice n, ⟨⟦8n^c⟧_n, 1^κ⟩⟩` with `κ = Nat.size (16 n^c)`. -/
private def dlb_advice (n : ℕ) : List Bool :=
  pairEncode (A.advice n) (pairEncode (natToList n (8 * n ^ c)) (List.replicate (Nat.size (16 * n ^ c)) true))

/-- The advice-length polynomial of `B`. -/
private def dlb_advP : PolyExpr :=
  .add (.mul (.const 2) A.adv) (.add (.mul (.const 2) .var) (.add (.const 4) (.mul (.const 16) (.pow .var c))))

private theorem dlb_advice_length (n : ℕ) : (dlb_advice A c n).length ≤ (dlb_advP A c).eval n := by
  have h1 := A.advice_length n
  have h2 : Nat.size (16 * n ^ c) ≤ 16 * n ^ c := Nat.size_le.2 (Nat.lt_two_pow_self)
  simp only [dlb_advice, dlb_advP, length_pairEncode, length_natToList, List.length_replicate,
    PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var, PolyExpr.eval_pow]
  omega

/-- **The inverter `B`** of [PS10, Lemma 84.1] as a non-uniform PPT (`NUPPT.ofPolyTime` of
`dlb_raw`). -/
private noncomputable def dlb_B : NUPPT :=
  NUPPT.ofPolyTime (dlb_raw_poly (fullDLCollection H G).sample A (dlb_ℓP c) H) (dlb_coinsP H G A c)
    (dlb_advP A c) (dlb_advice A c) (dlb_advice_length A c)

private theorem dlb_B_runAt (n : ℕ) (w : List Bool) (r : (dlb_B H G A c).Coins n) :
    (dlb_B H G A c).runAt n w r = dlb_raw (fullDLCollection H G).sample A (dlb_ℓP c)
      (NUPPT.layout (List.replicate n true) w (dlb_advice A c n) (List.ofFn r)) := by
  rw [NUPPT.runAt_eq]
  unfold dlb_B
  rw [NUPPT.runAtL_ofPolyTime, NUPPT.layout_eq, NUPPT.advInput_eq]

private theorem dlb_B_coinLen (n : ℕ) : (dlb_B H G A c).coinLen n =
    n + n * ((dlb_ℓP c).eval n * ((fullDLCollection H G).sample.coinLen n + A.coinLen n)) := by
  rw [NUPPT.coinLen_eq, NUPPT.coinLen_eq, NUPPT.coinLen_eq]
  unfold dlb_B
  rw [NUPPT.coins_ofPolyTime]
  simp only [dlb_coinsP, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_var]

end Machine

/-! ### Closeness of independent coordinates; the guess -/

/-- **Independent coordinates add their distances**: if `X` is `δ`-close to `Y`, the tuple of
`N` independent copies is `Nδ`-close (`StatClose.prod` and `Fin.consEquiv`, induction on `N`). -/
private theorem dlb_statClose_pi {σ τ γ : Type*} [Fintype σ] [Fintype τ] {X : σ → γ} {Y : τ → γ}
    {δ : ℝ} (h : StatClose X Y δ) :
    ∀ N : ℕ, StatClose (fun s : Fin N → σ => fun j => X (s j)) (fun t : Fin N → τ => fun j => Y (t j))
      (N * δ)
  | 0 => by
    rw [statClose_iff]
    intro T
    have hc : ∀ (s : Fin 0 → σ) (t : Fin 0 → τ), (fun j => X (s j)) = fun j => Y (t j) :=
      fun _ _ => funext fun j => j.elim0
    have h1 : (fun s : Fin 0 → σ => T fun j => X (s j)) = fun _ => T fun j => Y (Fin.elim0 j) := by
      funext s; rw [hc s Fin.elim0]
    have h2 : (fun t : Fin 0 → τ => T fun j => Y (t j)) = fun _ => T fun j => Y (Fin.elim0 j) := by
      funext t; congr 2; funext j; exact j.elim0
    rw [h1, h2, Nat.cast_zero, zero_mul]
    by_cases hP : T fun j => Y (Fin.elim0 j)
    · simp only [hP]; rw [uprob_true, uprob_true, sub_self, abs_zero]
    · simp only [hP]; rw [uprob_false, uprob_false, sub_self, abs_zero]
  | N + 1 => by
    have hp := (h.prod (dlb_statClose_pi h N)).map (fun z => (Fin.cons z.1 z.2 : Fin (N + 1) → γ))
    have hp' := (hp.comp_equiv_left (Fin.consEquiv fun _ => σ).symm).comp_equiv_right
      (Fin.consEquiv fun _ => τ).symm
    have hX : (fun s : Fin (N + 1) → σ => (Fin.cons ((fun z : σ × (Fin N → σ) => (X z.1, fun j => X (z.2 j)))
        ((Fin.consEquiv fun _ => σ).symm s)).1 ((fun z : σ × (Fin N → σ) => (X z.1, fun j => X (z.2 j)))
        ((Fin.consEquiv fun _ => σ).symm s)).2 : Fin (N + 1) → γ)) = fun s => fun j => X (s j) := by
      funext s j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [Fin.consEquiv, Fin.tail]
    have hY : (fun t : Fin (N + 1) → τ => (Fin.cons ((fun z : τ × (Fin N → τ) => (Y z.1, fun j => Y (z.2 j)))
        ((Fin.consEquiv fun _ => τ).symm t)).1 ((fun z : τ × (Fin N → τ) => (Y z.1, fun j => Y (z.2 j)))
        ((Fin.consEquiv fun _ => τ).symm t)).2 : Fin (N + 1) → γ)) = fun t => fun j => Y (t j) := by
      funext t j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [Fin.consEquiv, Fin.tail]
    rw [hX, hY] at hp'
    exact hp'.mono (by push_cast; ring_nf; rfl)

/-- Splitting an `n`-bit string at `κ ≤ n`: its first `κ` and its last `n − κ` bits. -/
private def dlb_cut {n κ : ℕ} (hκ : κ ≤ n) : (Fin n → Bool) ≃ (Fin κ → Bool) × (Fin (n - κ) → Bool) where
  toFun tb := (fun a => tb ⟨a, lt_of_lt_of_le a.2 hκ⟩, fun b => tb ⟨κ + b, by omega⟩)
  invFun u := fun q => if h : q.val < κ then u.1 ⟨q, h⟩ else u.2 ⟨q - κ, by omega⟩
  left_inv tb := by
    funext q
    by_cases h : q.val < κ
    · simp [h]
    · simp only [h, dite_false]
      congr 1; ext; simp; omega
  right_inv u := by
    ext a
    · simp [a.2]
    · simp

/-- The guess read from the first `κ` coins is uniform on `[0, 2^κ)`: the cut pushes uniform to
uniform, and its first part is read by `bitsEquiv`. -/
private theorem dlb_guess_pushesUniform {n κ : ℕ} (hκ : κ ≤ n) :
    HardcoreBit.PushesUniform fun tb : Fin n → Bool => (⟨listToNat ((List.ofFn tb).take κ), by
        have := listToNat_lt_two_pow ((List.ofFn tb).take κ)
        rwa [List.length_take, List.length_ofFn, min_eq_left hκ] at this⟩ : Fin (2 ^ κ)) := by
  have heq : (fun tb : Fin n → Bool => (⟨listToNat ((List.ofFn tb).take κ), by
        have := listToNat_lt_two_pow ((List.ofFn tb).take κ)
        rwa [List.length_take, List.length_ofFn, min_eq_left hκ] at this⟩ : Fin (2 ^ κ))) =
      fun tb => bitsEquiv κ (dlb_cut hκ tb).1 := by
    funext tb
    apply Fin.ext
    rw [bitsEquiv_val, bitsToNat_eq_listToNat, Fin.val_mk]
    congr 1
    apply List.ext_get
    · simp [min_eq_left hκ]
    · intro m h1 h2
      simp [dlb_cut]
  rw [heq]
  exact ((HardcoreBit.pushesUniform_equiv (dlb_cut hκ)).comp HardcoreBit.pushesUniform_fst).comp
    (HardcoreBit.pushesUniform_equiv (bitsEquiv κ))

/-! ### A full-group instance -/

section Instance
variable (H : ArithmeticFP) (G : FullGroupGen) (A : NUPPT)

/-- The generator of a valid index is a generator of `Z_p^*` when `m = p − 1` (`orderOf_expUnit`,
`Nat.card_zpowers`, `Subgroup.eq_top_of_card_eq`). -/
private theorem dlb_isGenerator {i : List Bool} (hv : FullGroupValid i) [Fact (dlP i).Prime] :
    IsGenerator (expUnit ((fullGroupValid_iff i).1 hv).1) := by
  obtain ⟨hx, hm, -⟩ := (fullGroupValid_iff i).1 hv
  intro x
  have htop : Subgroup.zpowers (expUnit hx) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, orderOf_expUnit, hm, Nat.card_eq_fintype_card, ZMod.card_units]
  rw [htop]; exact Subgroup.mem_top x

/-- The residue of `g^y` at a valid index: `(g^y).val = dlG i ^ y.val mod p`. -/
private theorem dlb_expo_val {i : List Bool} (hx : ExpValid i) [Fact (dlP i).Prime]
    [NeZero (dlP i - 1)] (y : ZMod (dlP i - 1)) :
    ((expo (expUnit hx) y : (ZMod (dlP i))ˣ) : ZMod (dlP i)).val = dlG i ^ y.val % dlP i := by
  have hgp : dlG i < dlP i := ((expValid_iff i).1 hx).2.2.2.2.1
  unfold expo
  rw [val_units_pow, coe_expUnit, ZMod.val_natCast, Nat.mod_eq_of_lt hgp]

/-- The equation `expOrd i = p − 1` at a full-group index. -/
private theorem dlb_expOrd_eq {i : List Bool} (hv : FullGroupValid i) : expOrd i = dlP i - 1 := by
  rw [expOrd_of_valid ((fullGroupValid_iff i).1 hv).1, ((fullGroupValid_iff i).1 hv).2.1]

/-- **The predictor's success at a full-group index is a `predProb`** of the concrete layer:
`Pr_{x, ρ}[A(1^n, ⟨i, f_i x⟩; ρ) = h_i(x)] = predProb (expo g) half_{p−1} A_i`, along the domain
equivalence and `ZMod.ringEquivCongr` (`fullDLCollection_f`, `expF_eq`, `halfPred_eq`). -/
private theorem dlb_pred_eq {n : ℕ} {i : List Bool} (hv : FullGroupValid i) (hW : dlW i = n)
    [Fact (dlP i).Prime] [NeZero (dlP i - 1)] :
    uprob (fun z : (fullDLCollection H G).D i × A.Coins n =>
        A.distinguisherL n (pairEncode i ((fullDLCollection H G).f i z.1)) z.2 =
          halfPred i (fullDLCollection_domEquiv H G i z.1)) =
      predProb (expo (expUnit ((fullGroupValid_iff i).1 hv).1)) (halfBit (dlP i - 1)) (dlb_Ai A n i (dlP i)) := by
  have hx := ((fullGroupValid_iff i).1 hv).1
  set ψ := ZMod.ringEquivCongr (dlb_expOrd_eq hv) with hψ
  rw [predProb_def, ← uprob_comp_equiv (((fullDLCollection_domEquiv H G i).trans ψ.toEquiv).prodCongr
    (Equiv.refl (A.Coins n)))]
  congr 1
  funext z
  have hval : (ψ (fullDLCollection_domEquiv H G i z.1)).val = (fullDLCollection_domEquiv H G i z.1).val :=
    ZMod.ringEquivCongr_val _ _
  simp only [Equiv.prodCongr_apply, Equiv.trans_apply, RingEquiv.toEquiv_eq_coe, Prod.map_fst,
    Prod.map_snd, Equiv.refl_apply, RingEquiv.coe_toEquiv]
  rw [fullDLCollection_f, expF_eq, halfPred_eq hx, dlb_Ai, dlb_expo_val hx, hval, hW]
  unfold halfBit
  rw [hval]

/-- **The inverter at one good instance**: at a well-formed full-group index where the predictor
has advantage `ε`, with window parameters as in `invProb_dlInverter_ge` and the domain sampler
`δ`-close to uniform, `B` solves discrete log with probability at least
`(1 − n/(ε²ℓ))/2^κ − n·ℓ·δ` (the concrete bound, minus the sampling loss of the `n·ℓ` sampled
exponents, `StatClose.abs_uprob_sub_le_prod`). -/
private theorem dlb_instance (c : ℕ) {n : ℕ} {i : List Bool} (hwf : WellFormedIndex n i)
    (hv : FullGroupValid i) [Fact (dlP i).Prime] [NeZero (dlP i - 1)] {δS : ℝ}
    (hSC : StatClose (fun s : (fullDLCollection H G).sample.Coins n =>
        (fullDLCollection H G).decD i ((fullDLCollection H G).sample.runAt n i s))
      (fun x : (fullDLCollection H G).D i => some x) δS)
    (hκ : Nat.size (16 * n ^ c) ≤ n) (hD : 8 * n ^ c < 2 ^ n) {ε : ℝ} (hε : 0 < ε)
    (hA : 1 / 2 + ε ≤ uprob (fun z : (fullDLCollection H G).D i × A.Coins n =>
        A.distinguisherL n (pairEncode i ((fullDLCollection H G).f i z.1)) z.2 =
          halfPred i (fullDLCollection_domEquiv H G i z.1)))
    (hs : 0 < (dlP i - 1) / (8 * n ^ c))
    (hs4 : 4 * (((dlP i - 1) / (8 * n ^ c) : ℕ) : ℝ) ≤ ε * ((dlP i : ℝ) - 1))
    (hT : dlP i - 1 ≤ 2 ^ Nat.size (16 * n ^ c) * ((dlP i - 1) / (8 * n ^ c)))
    (hk : (dlP i - 1) / (8 * n ^ c) ≤ 2 ^ n) :
    (1 - n / (ε ^ 2 * (dlb_ℓP c).eval n)) / ((2 ^ Nat.size (16 * n ^ c) : ℕ) : ℝ) -
        n * ((dlb_ℓP c).eval n * δS) ≤
      uprob fun z : ZMod (expOrd i) × (dlb_B H G A c).Coins n =>
        ∃ x : Fin n → Bool, decodeFin n ((dlb_B H G A c).runAt n (pairEncode i (expF i z.1)) z.2) = some x ∧
          bitsToNat x = z.1.val := by
  obtain ⟨hx, hm, hp3⟩ := (fullGroupValid_iff i).1 hv
  have hp2 : dlP i ≠ 2 := by intro h; rw [h] at hp3; norm_num at hp3
  have hg := dlb_isGenerator hv
  set g := expUnit hx with hgdef
  have e := dlb_expOrd_eq hv
  set ℓ := (dlb_ℓP c).eval n with hℓ
  set κ := Nat.size (16 * n ^ c) with hκdef
  set sv := (dlP i - 1) / (8 * n ^ c) with hsv
  have hodd : ℓ % 2 = 1 := by
    simp only [hℓ, dlb_ℓP, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_pow,
      PolyExpr.eval_var]; omega
  have hℓ0 : 0 < ℓ := by omega
  have hpred : 1 / 2 + ε ≤ predProb (expo g) (halfBit (dlP i - 1)) (dlb_Ai A n i (dlP i)) :=
    hA.trans_eq (dlb_pred_eq H G A hv hwf.dlW_eq)
  have hinv := invProb_dlInverter_ge hp3 hg (dlb_Ai A n i (dlP i)) hε hpred hs hs4 hT hk hℓ0
  -- the index's numerals
  obtain ⟨a, b, cc, hi, ha, hb, hc⟩ := (wellFormedIndex_iff n i).1 hwf
  have hW : dlW i = n := hwf.dlW_eq
  have hiP : pairFstD i = natToList n (dlP i) := by
    rw [dlP_eq, hi, pairFstD_pairEncode, ← ha, natToList_length_listToNat]
  have hiG : pairSndD (pairSndD i) = natToList n (dlG i) := by
    rw [dlG_eq, hi, pairSndD_pairEncode, pairSndD_pairEncode, ← hc, natToList_length_listToNat]
  have hpn : dlP i < 2 ^ n := hW ▸ dlP_lt_two_pow i
  have hgv : (g : ZMod (dlP i)).val = dlG i := by
    rw [hgdef, coe_expUnit, ZMod.val_natCast, Nat.mod_eq_of_lt ((expValid_iff i).1 hx).2.2.2.2.1]
  set ψ := ZMod.ringEquivCongr e with hψ
  have hψv : ∀ x : ZMod (expOrd i), (ψ x).val = x.val := fun x => ZMod.ringEquivCongr_val e x
  have hyF : ∀ x : ZMod (expOrd i), expF i x = natToList n ((expo g (ψ x) : (ZMod (dlP i))ˣ) : ZMod (dlP i)).val := by
    intro x; rw [expF_eq, hW, dlb_expo_val hx, hψv]
  -- the coins of `B`
  have hN := dlb_B_coinLen H G A c n
  rw [← hℓ] at hN
  set S := (fullDLCollection H G).sample with hS
  set eD := Equiv.ofBijective _ (dlb_split_bijective S A n ℓ hN) with heD
  have hofFn : ∀ (tb : Fin n → Bool) (bl : Fin n → Fin ℓ → S.Coins n × A.Coins n),
      List.ofFn (eD.symm (tb, bl)) = List.ofFn tb ++ dlb_roundsL S A n ℓ bl := by
    intro tb bl
    have h1 := dlb_ofFn_split S A n ℓ hN (eD.symm (tb, bl))
    have h2 : dlb_split S A n ℓ hN (eD.symm (tb, bl)) = (tb, bl) := eD.apply_symm_apply (tb, bl)
    rw [h2] at h1
    exact h1
  -- the sample space `rounds × (x, t-block)`
  let eR : (Fin n → Fin ℓ → S.Coins n × A.Coins n) × (ZMod (expOrd i) × (Fin n → Bool)) ≃
      ZMod (expOrd i) × (dlb_B H G A c).Coins n :=
    { toFun := fun z => (z.2.1, eD.symm (z.2.2, z.1))
      invFun := fun w => ((eD w.2).2, (w.1, (eD w.2).1))
      left_inv := fun z => by simp
      right_inv := fun w => by simp }
  -- the success event of the ideal inverter, read on the decoded coins
  let D := dlInverter g (dlb_Ai A n i (dlP i)) sv (2 ^ κ) ℓ n
  let tv : (Fin n → Bool) → Fin (2 ^ κ) := fun tb => ⟨listToNat ((List.ofFn tb).take κ), by
    have := listToNat_lt_two_pow ((List.ofFn tb).take κ)
    rwa [List.length_take, List.length_ofFn, min_eq_left hκ] at this⟩
  let P : (Fin n → Fin ℓ → Option ((fullDLCollection H G).D i) × A.Coins n) →
      ZMod (expOrd i) × (Fin n → Bool) → Prop := fun o w =>
    (∀ j k, ((o j k).1).isSome) ∧
      D (expo g (ψ w.1)) (tv w.2, fun j k => ((((o j k).1).map fun x => ψ (fullDLCollection_domEquiv H G i x)).getD 0,
        (o j k).2)) = ψ w.1
  let Xm : (Fin n → Fin ℓ → S.Coins n × A.Coins n) → (Fin n → Fin ℓ → Option ((fullDLCollection H G).D i) × A.Coins n) :=
    fun bl j k => ((fullDLCollection H G).decD i (S.runAt n i (bl j k).1), (bl j k).2)
  have hstep1 : uprob (fun z : (Fin n → Fin ℓ → S.Coins n × A.Coins n) × (ZMod (expOrd i) × (Fin n → Bool)) =>
      P (Xm z.1) z.2) ≤
      uprob fun z : ZMod (expOrd i) × (dlb_B H G A c).Coins n =>
        ∃ x : Fin n → Bool, decodeFin n ((dlb_B H G A c).runAt n (pairEncode i (expF i z.1)) z.2) = some x ∧
          bitsToNat x = z.1.val := by
    rw [← uprob_comp_equiv eR]
    refine uprob_mono fun z hz => ?_
    obtain ⟨bl, x, tb⟩ := z
    obtain ⟨hdec, hsucc⟩ := hz
    have hrun : (dlb_B H G A c).runAt n (pairEncode i (expF i x)) (eD.symm (tb, bl)) =
        natToList n x.val := by
      rw [dlb_B_runAt, hofFn, hyF]
      unfold dlb_advice
      rw [dlb_raw_sem (e := e) hp2 hpn hodd hℓ.symm hκ hD hiP hiG hW hgv _ tb bl (fun j k => hdec j k)]
      have : shiftInverter g (dlLoop g (majOracle g (dlb_Ai A n i (dlP i)) ℓ) n) sv (2 ^ κ) (expo g (ψ x))
          (tv tb, fun j => dlb_idealRound H G A n i e (bl j)) = ψ x := hsucc
      rw [this, hψv]
    refine ⟨natToBits n x.val, ?_, ?_⟩
    · show decodeFin n ((dlb_B H G A c).runAt n (pairEncode i (expF i x)) (eD.symm (tb, bl))) = _
      rw [hrun, natToList_eq, decodeFin_ofFn]
    · have hxlt : x.val < 2 ^ n := by
        have := ZMod.val_lt x
        have h2 := expOrd_le_two_pow i
        rw [hW] at h2; omega
      exact bitsToNat_natToBits hxlt
  -- the sampled exponents are close to uniform
  have hX1 := hSC.prod (StatClose.refl (fun ρ : A.Coins n => ρ))
  have hXn := dlb_statClose_pi (dlb_statClose_pi hX1 ℓ) n
  have hclose := hXn.abs_uprob_sub_le_prod P
  -- the ideal experiment is the inversion experiment of the concrete inverter
  let Φ : (Fin n → Fin ℓ → (fullDLCollection H G).D i × A.Coins n) × (ZMod (expOrd i) × (Fin n → Bool)) →
      ZMod (dlP i - 1) × (Fin (2 ^ κ) × (Fin n → Fin ℓ → ZMod (dlP i - 1) × A.Coins n)) :=
    fun z => (ψ z.2.1, (tv z.2.2, fun j k => (ψ (fullDLCollection_domEquiv H G i (z.1 j k).1), (z.1 j k).2)))
  have hΦ : HardcoreBit.PushesUniform Φ := by
    let ec : (Fin n → Fin ℓ → (fullDLCollection H G).D i × A.Coins n) ≃
        (Fin n → Fin ℓ → ZMod (dlP i - 1) × A.Coins n) :=
      Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ =>
        Equiv.prodCongr ((fullDLCollection_domEquiv H G i).trans ψ.toEquiv) (Equiv.refl _)
    have h1 := (HardcoreBit.pushesUniform_equiv ec).prodMap
      ((HardcoreBit.pushesUniform_equiv ψ.toEquiv).prodMap (dlb_guess_pushesUniform hκ))
    let er : (Fin n → Fin ℓ → ZMod (dlP i - 1) × A.Coins n) × (ZMod (dlP i - 1) × Fin (2 ^ κ)) ≃
        ZMod (dlP i - 1) × (Fin (2 ^ κ) × (Fin n → Fin ℓ → ZMod (dlP i - 1) × A.Coins n)) :=
      { toFun := fun w => (w.2.1, (w.2.2, w.1)), invFun := fun w => (w.2.2, (w.1, w.2.1)),
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    exact h1.comp (HardcoreBit.pushesUniform_equiv er)
  have hideal : uprob (fun z : (Fin n → Fin ℓ → (fullDLCollection H G).D i × A.Coins n) ×
      (ZMod (expOrd i) × (Fin n → Bool)) => P (fun j k => (some (z.1 j k).1, (z.1 j k).2)) z.2) =
      invProb (expo g) D := by
    rw [invProb_def, ← hΦ.uprob_eq]
    congr 1
    funext z
    apply propext
    simp only [P, Φ, Option.isSome_some, implies_true, true_and, Option.map_some, Option.getD_some]
    exact ⟨fun h => by rw [h], fun h => expo_injective hg h⟩
  rw [hideal] at hclose
  have := (abs_le.1 hclose).1
  simp only [add_zero] at this
  push_cast at hinv ⊢
  linarith

end Instance


/-! ### Parameters for large `n` -/

/-- `2^{Nat.size m} ≤ 2m` for `m ≥ 1`. -/
private theorem dlb_two_pow_size_le {m : ℕ} (hm : 0 < m) : 2 ^ Nat.size m ≤ 2 * m := by
  have h := Nat.size_pos.2 hm
  have h1 : 2 ^ (Nat.size m - 1) ≤ m := by
    by_contra hlt
    push_neg at hlt
    have := Nat.size_le.2 hlt
    omega
  calc 2 ^ Nat.size m = 2 * 2 ^ (Nat.size m - 1) := by
        rw [← pow_succ']; congr 1; omega
    _ ≤ 2 * m := by omega

/-- **The window parameters** of the reduction: for `P = p − 1 ≥ 16 n^c`, `s = ⌊P/(8n^c)⌋` and
`T = 2^{Nat.size (16 n^c)} > 16 n^c` satisfy `s ≥ 1`, `4s ≤ P/(2n^c)` and `P ≤ T s`. -/
private theorem dlb_window_params (c n P : ℕ) (hn : 0 < n) (h2D : 16 * n ^ c ≤ P) :
    0 < P / (8 * n ^ c) ∧ 4 * ((P / (8 * n ^ c) : ℕ) : ℝ) ≤ 1 / (2 * (n : ℝ) ^ c) * (P : ℝ) ∧
      P ≤ 2 ^ Nat.size (16 * n ^ c) * (P / (8 * n ^ c)) := by
  have hnc : 0 < n ^ c := pow_pos hn c
  have hD : 0 < 8 * n ^ c := by omega
  have hs2 : 2 ≤ P / (8 * n ^ c) := (Nat.le_div_iff_mul_le hD).2 (by omega)
  refine ⟨by omega, ?_, ?_⟩
  · have hmul : P / (8 * n ^ c) * (8 * n ^ c) ≤ P := Nat.div_mul_le_self _ _
    have hmulR : ((P / (8 * n ^ c) : ℕ) : ℝ) * (8 * (n : ℝ) ^ c) ≤ P := by exact_mod_cast hmul
    have hncR : (0 : ℝ) < (n : ℝ) ^ c := by positivity
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    nlinarith
  · have hlt : P < (P / (8 * n ^ c) + 1) * (8 * n ^ c) := by
      rw [add_mul, one_mul]; exact Nat.lt_div_mul_add hD
    have hT : 16 * n ^ c < 2 ^ Nat.size (16 * n ^ c) := Nat.lt_size_self _
    have : (P / (8 * n ^ c) + 1) * (8 * n ^ c) ≤ 16 * n ^ c * (P / (8 * n ^ c)) := by
      nlinarith
    calc P ≤ 16 * n ^ c * (P / (8 * n ^ c)) := by omega
      _ ≤ 2 ^ Nat.size (16 * n ^ c) * (P / (8 * n ^ c)) := Nat.mul_le_mul_right _ hT.le

/-- Polynomials are eventually below `2^n`: `n^d < 2^n` from some point on
(`negligible_two_pow_neg`). -/
private theorem dlb_eventually_pow_lt (d : ℕ) : ∃ N, ∀ n ≥ N, n ^ d < 2 ^ n := by
  obtain ⟨N, hN⟩ := (negligible_iff _).1 negligible_two_pow_neg d
  refine ⟨max N 1, fun n hn => ?_⟩
  have h := hN n (le_of_max_le_left hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hpos : (0 : ℝ) < (n : ℝ) ^ d := by positivity
  have h1 : (2⁻¹ : ℝ) ^ n < 1 / (n : ℝ) ^ d := by
    have h2 := h
    rwa [abs_of_pos (by positivity : (0 : ℝ) < (2⁻¹ : ℝ) ^ n)] at h2
  rw [inv_pow, ← one_div, one_div_lt_one_div (by positivity) hpos] at h1
  exact_mod_cast h1

/-- The concrete success bound at the reduction's parameters: with `ε = 1/(2X)`,
`ℓ = 16nX² + 1` and `T ≤ 32X`, `(1 − n/(ε²ℓ))/T ≥ 3/(128X)`. -/
private theorem dlb_arith_success {X n ℓ T : ℝ} (hX : 1 ≤ X) (hn : 1 ≤ n)
    (hℓ : ℓ = 16 * n * X ^ 2 + 1) (hT : 0 < T) (hT32 : T ≤ 32 * X) :
    3 / (128 * X) ≤ (1 - n / ((1 / (2 * X)) ^ 2 * ℓ)) / T := by
  have hX0 : 0 < X := by linarith
  have hℓ0 : 0 < ℓ := by rw [hℓ]; positivity
  have h1 : n / ((1 / (2 * X)) ^ 2 * ℓ) = 4 * n * X ^ 2 / ℓ := by
    field_simp; norm_num
  have h2 : 4 * n * X ^ 2 / ℓ ≤ 1 / 4 := by
    rw [div_le_iff₀ hℓ0, hℓ]; nlinarith
  rw [h1]
  have h3 : 3 / 4 ≤ 1 - 4 * n * X ^ 2 / ℓ := by linarith
  calc 3 / (128 * X) = (3 / 4) / (32 * X) := by field_simp; ring
    _ ≤ (1 - 4 * n * X ^ 2 / ℓ) / (32 * X) := by gcongr
    _ ≤ (1 - 4 * n * X ^ 2 / ℓ) / T := by
        apply div_le_div_of_nonneg_left (by linarith) hT hT32

/-- The sampling loss at the reduction's parameters: with `δ ≤ 1/(X⁴n³)` and `n ≥ 6000`,
`n·(16nX² + 1)·δ ≤ 3/(1024X²)`. -/
private theorem dlb_arith_loss {X n δ : ℝ} (hX : 1 ≤ X) (hn : 6000 ≤ n) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / (X ^ 4 * n ^ 3)) : n * ((16 * n * X ^ 2 + 1) * δ) ≤ 3 / (1024 * X ^ 2) := by
  have hX0 : 0 < X := by linarith
  have hn0 : 0 < n := by linarith
  have hX2 : 1 ≤ X ^ 2 := one_le_pow₀ hX
  have hnX : 1 ≤ n * X ^ 2 := by nlinarith
  have hk : n * (16 * n * X ^ 2 + 1) ≤ 17 * n ^ 2 * X ^ 2 := by nlinarith
  have hδ' : δ * (X ^ 4 * n ^ 3) ≤ 1 := by
    rwa [le_div_iff₀ (by positivity)] at hδ
  calc n * ((16 * n * X ^ 2 + 1) * δ) = (n * (16 * n * X ^ 2 + 1)) * δ := by ring
    _ ≤ 17 * n ^ 2 * X ^ 2 * δ := by gcongr
    _ ≤ 3 / (1024 * X ^ 2) := by
        rw [le_div_iff₀ (by positivity)]
        have : 17 * n ^ 2 * X ^ 2 * δ * (1024 * X ^ 2) = (17 * 1024 / n) * (δ * (X ^ 4 * n ^ 3)) := by
          field_simp
        rw [this]
        have h17 : 17 * 1024 / n ≤ 3 := by rw [div_le_iff₀ hn0]; linarith
        calc 17 * 1024 / n * (δ * (X ^ 4 * n ^ 3)) ≤ 3 * 1 := by
              apply mul_le_mul h17 hδ' (by positivity) (by norm_num)
          _ = 3 := by ring

/-- The final arithmetic of the reduction: for `X ≥ 1` and a loss `0 ≤ L ≤ 3/(1024X²)`,
`(ε/2)·(3/(128X) − L) ≥ 3/(1024X²)` with `ε = 1/(2X)`. -/
private theorem dlb_arith_final {X L : ℝ} (hX : 1 ≤ X) (hL0 : 0 ≤ L) (hL : L ≤ 3 / (1024 * X ^ 2)) :
    3 / (1024 * X ^ 2) ≤ 1 / (2 * X) / 2 * (3 / (128 * X) - L) := by
  have hX0 : 0 < X := by linarith
  have h1 : 1 / (2 * X) / 2 ≤ 1 := by rw [div_div, div_le_one (by positivity)]; linarith
  have h2 : 1 / (2 * X) / 2 * L ≤ L := mul_le_of_le_one_left hL0 h1
  have heq : 1 / (2 * X) / 2 * (3 / (128 * X)) = 3 / (512 * X ^ 2) := by field_simp; ring
  have h3 : 3 / (512 * X ^ 2) = 2 * (3 / (1024 * X ^ 2)) := by field_simp; ring
  rw [mul_sub, heq, h3]
  linarith

/-! ### The reduction -/

/-- The predictor's average success at parameter `n` (the quantity bounded by `HardCore`). -/
private noncomputable def dlb_succ (H : ArithmeticFP) (G : FullGroupGen) (A : NUPPT) (n : ℕ) : ℝ :=
  uexp fun r : (fullDLCollection H G).gen.Coins n =>
    uprob fun z : (fullDLCollection H G).D ((fullDLCollection H G).index n r) × A.Coins n =>
      A.distinguisherL n (pairEncode ((fullDLCollection H G).index n r)
        ((fullDLCollection H G).f ((fullDLCollection H G).index n r) z.1)) z.2 =
        halfPred ((fullDLCollection H G).index n r)
          (fullDLCollection_domEquiv H G ((fullDLCollection H G).index n r) z.1)

/-- **The reduction** [PS10, Lemma 84.1]: for every predictor `A` and exponent `c`, the inverter
`B = dlb_B H G A c` solves discrete log with probability at least `3/(1024 n^{2c})` at every large
`n` where `A` has advantage `n^{−c}`. -/
private theorem dlb_reduction (H : ArithmeticFP) (G : FullGroupGen)
    (hbig : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.FullLengthExcept δ) (hDL : FullDLAssumption G)
    (A : NUPPT) (c : ℕ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 / 2 + 1 / (n : ℝ) ^ c ≤ dlb_succ H G A n →
      3 / (1024 * (n : ℝ) ^ (2 * c)) ≤ G.dlProb (dlb_B H G A c) n := by
  obtain ⟨δ, hδ, hfl⟩ := hbig
  obtain ⟨δS, hδS, hSC⟩ := (fullDLCollection_oneWay H G hDL).sampleClose
  obtain ⟨Nδ, hNδ⟩ := (negligible_iff δ).1 hδ (c + 1)
  obtain ⟨NS, hNS⟩ := (negligible_iff δS).1 hδS (4 * c + 3)
  rw [Collection.sampleClose_iff] at hSC
  obtain ⟨Np, hNp⟩ := dlb_eventually_pow_lt (c + 6)
  refine ⟨max (max (max G.n₀ Nδ) (max NS Np)) 6000, fun n hn hsucc => ?_⟩
  have hn0 : G.n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hn
  have hnδ : Nδ ≤ n := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))) hn
  have hnS : NS ≤ n := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hn
  have hnp : Np ≤ n := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_left _ _))) hn
  have hn6 : 6000 ≤ n := le_trans (le_max_right _ _) hn
  -- the integer conditions of large `n`
  have hpow : n ^ (c + 6) < 2 ^ n := hNp n hnp
  have hnc : 1 ≤ n ^ c := Nat.one_le_pow _ _ (by omega)
  have hn6c : 4096 * n ^ c ≤ n ^ (c + 6) := by
    rw [pow_add]
    have : 4096 ≤ n ^ 6 := le_trans (by norm_num) (Nat.pow_le_pow_left (by omega : 4 ≤ n) 6)
    nlinarith
  have h16 : 16 * n ^ c < 2 ^ n := by omega
  have hκ : Nat.size (16 * n ^ c) ≤ n := Nat.size_le.2 h16
  have hD : 8 * n ^ c < 2 ^ n := by omega
  have hhalf : 16 * n ^ c + 1 ≤ 2 ^ (n - 1) := by
    have : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  -- the real quantities
  set X := (n : ℝ) ^ c with hXdef
  have hX1 : 1 ≤ X := by rw [hXdef]; exact one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ n))
  have hX0 : 0 < X := by linarith
  have hnR : (6000 : ℝ) ≤ n := by exact_mod_cast hn6
  set ε' := 1 / (2 * X) with hε'
  have hε'0 : 0 < ε' := by positivity
  have hδn : δ n ≤ ε' / 2 := by
    have h := hNδ n hnδ
    have h1 := (abs_lt.1 h).2
    rw [pow_succ, ← hXdef] at h1
    refine le_trans h1.le ?_
    rw [hε', div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  set ℓ := (dlb_ℓP c).eval n with hℓdef
  have hℓR : (ℓ : ℝ) = 16 * n * X ^ 2 + 1 := by
    rw [hℓdef]
    simp only [dlb_ℓP, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_pow,
      PolyExpr.eval_var]
    push_cast
    rw [hXdef, pow_succ, pow_mul]; ring
  have hδS0 : 0 ≤ δS n := (hSC n (fun _ => false)).nonneg
  have hSn : (n : ℝ) * (ℓ * δS n) ≤ 3 / (1024 * X ^ 2) := by
    rw [hℓR]
    refine dlb_arith_loss hX1 hnR hδS0 ?_
    have h := (abs_lt.1 (hNS n hnS)).2
    refine h.le.trans (le_of_eq ?_)
    rw [hXdef, ← pow_mul, ← pow_add]; ring_nf
  -- the predictor's success, averaged over the instance generator's coins
  let Sf : List Bool → ℝ := fun i => uprob fun z : (fullDLCollection H G).D i × A.Coins n =>
    A.distinguisherL n (pairEncode i ((fullDLCollection H G).f i z.1)) z.2 =
      halfPred i (fullDLCollection_domEquiv H G i z.1)
  have hq : dlb_succ H G A n = uexp fun r' : G.gen.Coins n => Sf (G.gen.runAt n [] r') := by
    show uexp (fun r => Sf ((fullDLCollection H G).index n r)) = _
    calc uexp (fun r => Sf ((fullDLCollection H G).index n r)) =
        uexp (fun r => (fun r' : G.gen.Coins n => Sf (G.gen.runAt n [] r'))
          (fullDLCollection_coinsEquiv H G n r)) := by
          refine congrArg uexp (funext fun r => ?_)
          rw [fullDLCollection_index H G n r hn0]
      _ = _ := fullDLCollection_coinsEquiv_uexp H G n (fun r' => Sf (G.gen.runAt n [] r'))
  -- the good instances: success `≥ 1/2 + ε'` and a full-length prime
  have hgi := good_instances (fun r' : G.gen.Coins n => Sf (G.gen.runAt n [] r'))
    (fun r' => uprob_le_one _) (ε := 2 * ε') (by positivity) (by
      rw [← hq]; refine le_trans (le_of_eq ?_) hsucc; rw [hε', hXdef]; field_simp)
  have hshort := (ExpGroupGen.fullLengthExcept_iff G δ).1 hfl n hn0
  let Good : G.gen.Coins n → Prop := fun r' =>
    1 / 2 + ε' ≤ Sf (G.gen.runAt n [] r') ∧ ¬ dlP (G.gen.runAt n [] r') < 2 ^ (n - 1)
  have hgood : ε' / 2 ≤ uprob Good := by
    have h1 : uprob (fun r' : G.gen.Coins n => 1 / 2 + 2 * ε' / 2 ≤ Sf (G.gen.runAt n [] r')) ≤
        uprob Good + uprob (fun r' : G.gen.Coins n => dlP (G.gen.runAt n [] r') < 2 ^ (n - 1)) := by
      refine (uprob_mono fun r' hr' => ?_).trans (uprob_or_le _ _)
      by_cases hs : dlP (G.gen.runAt n [] r') < 2 ^ (n - 1)
      · exact Or.inr hs
      · exact Or.inl ⟨by rw [show 2 * ε' / 2 = ε' by ring] at hr'; exact hr', hs⟩
    have : 2 * ε' / 2 = ε' := by ring
    rw [this] at hgi h1
    linarith
  -- at each good instance, `B` succeeds with probability `≥ 3/(128X) − nℓδ`
  set b := 3 / (128 * X) - n * (ℓ * δS n) with hb
  have hinst : ∀ r', Good r' → b ≤ uprob fun z : ZMod (expOrd (G.gen.runAt n [] r')) ×
      (dlb_B H G A c).Coins n => ∃ x : Fin n → Bool,
        decodeFin n ((dlb_B H G A c).runAt n (pairEncode (G.gen.runAt n [] r') (expF _ z.1)) z.2) = some x ∧
          bitsToNat x = z.1.val := by
    intro r' ⟨hgq, hlong⟩
    have hv : FullGroupValid (G.gen.runAt n [] r') := G.valid n r' hn0
    have hwf := G.wellFormed n r' hn0
    haveI : Fact (dlP (G.gen.runAt n [] r')).Prime :=
      ⟨((expValid_iff _).1 ((fullGroupValid_iff _).1 hv).1).1⟩
    have hp1 := (Fact.out : (dlP (G.gen.runAt n [] r')).Prime).two_le
    haveI : NeZero (dlP (G.gen.runAt n [] r') - 1) := ⟨by omega⟩
    have hP : 16 * n ^ c ≤ dlP (G.gen.runAt n [] r') - 1 := by push_neg at hlong; omega
    obtain ⟨hs, hs4, hT⟩ := dlb_window_params c n (dlP (G.gen.runAt n [] r') - 1) (by omega) hP
    have hpn : dlP (G.gen.runAt n [] r') < 2 ^ n := by
      have := dlP_lt_two_pow (G.gen.runAt n [] r'); rwa [hwf.dlW_eq] at this
    have hk : (dlP (G.gen.runAt n [] r') - 1) / (8 * n ^ c) ≤ 2 ^ n :=
      (Nat.div_le_self _ _).trans (by omega)
    have hcast : ((dlP (G.gen.runAt n [] r') - 1 : ℕ) : ℝ) = (dlP (G.gen.runAt n [] r') : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hcast, ← hXdef, ← hε'] at hs4
    -- the domain sampler at this instance
    have hSCi : StatClose (fun s : (fullDLCollection H G).sample.Coins n =>
        (fullDLCollection H G).decD (G.gen.runAt n [] r')
          ((fullDLCollection H G).sample.runAt n (G.gen.runAt n [] r') s))
        (fun x : (fullDLCollection H G).D (G.gen.runAt n [] r') => some x) (δS n) := by
      have key : ∀ i', (fullDLCollection H G).index n ((fullDLCollection_coinsEquiv H G n).symm r') = i' →
          StatClose (fun s : (fullDLCollection H G).sample.Coins n =>
            (fullDLCollection H G).decD i' ((fullDLCollection H G).sample.runAt n i' s))
            (fun x : (fullDLCollection H G).D i' => some x) (δS n) := by
        rintro i' rfl
        exact hSC n _
      exact key _ (by rw [fullDLCollection_index H G n _ hn0, Equiv.apply_symm_apply])
    have h := dlb_instance H G A c hwf hv hSCi hκ hD hε'0 hgq hs hs4 hT hk
    refine le_trans ?_ h
    have hT0 : (0 : ℝ) < ((2 ^ Nat.size (16 * n ^ c) : ℕ) : ℝ) := by positivity
    have hT32 : ((2 ^ Nat.size (16 * n ^ c) : ℕ) : ℝ) ≤ 32 * X := by
      have := dlb_two_pow_size_le (by omega : 0 < 16 * n ^ c)
      have h' : ((2 ^ Nat.size (16 * n ^ c) : ℕ) : ℝ) ≤ ((2 * (16 * n ^ c) : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at h' ⊢; rw [hXdef]; linarith
    have := dlb_arith_success hX1 (by linarith : (1 : ℝ) ≤ n) hℓR hT0 hT32
    rw [hb]
    linarith
  -- averaging over the good set
  have hW0 : ∀ r' : G.gen.Coins n, 0 ≤ uprob fun z : ZMod (expOrd (G.gen.runAt n [] r')) ×
      (dlb_B H G A c).Coins n => ∃ x : Fin n → Bool,
        decodeFin n ((dlb_B H G A c).runAt n (pairEncode (G.gen.runAt n [] r') (expF _ z.1)) z.2) = some x ∧
          bitsToNat x = z.1.val := fun r' => uprob_nonneg _
  have havg := HardcoreBit.uprob_mul_le_uexp hW0 hinst
  have hb0 : 0 ≤ b := by
    rw [hb]
    have : 3 / (1024 * X ^ 2) ≤ 3 / (128 * X) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    linarith
  have hmass : ε' / 2 * b ≤ uprob Good * b := mul_le_mul_of_nonneg_right hgood hb0
  have hfinal : 3 / (1024 * (n : ℝ) ^ (2 * c)) ≤ ε' / 2 * b := by
    have hX2 : (n : ℝ) ^ (2 * c) = X ^ 2 := by rw [hXdef, ← pow_mul, mul_comm]
    rw [hb, hε', hX2]
    exact dlb_arith_final hX1 (by positivity) hSn
  exact le_trans hfinal (le_trans hmass (havg.trans (le_of_eq (ExpGroupGen.dlProb_eq G _ n).symm)))

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
  rw [Collection.hardCore_iff]
  refine ⟨⟨halfStr, polyTimeComputable_halfStr H, fun i x => by
    rw [fullDLCollection_encD, halfStr_spec]⟩, fun A => ?_⟩
  refine ⟨fun n => max (dlb_succ H G A n - 1 / 2) 0, ?_, fun n => ?_⟩
  · by_contra hne
    obtain ⟨c, hc⟩ := not_negligible_iff.1 hne
    obtain ⟨N, hN⟩ := dlb_reduction H G hbig hDL A c
    obtain ⟨n₁, hn₁⟩ := (negligible_iff _).1 ((fullDLAssumption_iff G).1 hDL (dlb_B H G A c)) (2 * c + 11)
    obtain ⟨n, hn, hcn⟩ := hc (max (max N n₁) 2)
    have hnN : N ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
    have hX : (0 : ℝ) < (n : ℝ) ^ c := by positivity
    have hsucc : 1 / 2 + 1 / (n : ℝ) ^ c ≤ dlb_succ H G A n := by
      rw [abs_of_nonneg (le_max_right _ _)] at hcn
      rcases le_total (dlb_succ H G A n - 1 / 2) 0 with h | h
      · rw [max_eq_right h] at hcn
        exact absurd hcn (not_le.2 (by positivity))
      · rw [max_eq_left h] at hcn
        linarith
    have hlow := hN n hnN hsucc
    have hup := hn₁ n hn1
    rw [abs_of_nonneg (ExpGroupGen.dlProb_nonneg G _ n)] at hup
    have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have h11 : (1024 : ℝ) < (n : ℝ) ^ 11 := by
      calc (1024 : ℝ) < 2 ^ 11 := by norm_num
        _ ≤ (n : ℝ) ^ 11 := pow_le_pow_left₀ (by norm_num) hn2R 11
    have hkey : 1 / (n : ℝ) ^ (2 * c + 11) < 3 / (1024 * (n : ℝ) ^ (2 * c)) := by
      rw [pow_add, div_lt_div_iff₀ (by positivity) (by positivity)]
      have : (0 : ℝ) < (n : ℝ) ^ (2 * c) := by positivity
      nlinarith
    linarith
  · change dlb_succ H G A n ≤ 1 / 2 + max (dlb_succ H G A n - 1 / 2) 0
    linarith [le_max_left (dlb_succ H G A n - 1 / 2) 0]

end TCSlib.Cryptography.Candidates
