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
  sorry

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
  sorry

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
  sorry

/-- **The range reduction** (Lem-84.1.4, [PS10, p. 85, "such an algorithm suffices to solve the
discrete log problem, since we can guess and map any instance into this range" — never
shown]): from a solver `B₀` for instances with exponent in `[0, s)`, the inverter that guesses
`t ← [0, T)`, runs `B₀` on `y · g^{−ts}` and returns `B₀(…) + ts`. -/
def shiftInverter (g : (ZMod p)ˣ) {ρ' : Type*} (B₀ : (ZMod p)ˣ → ρ' → ℕ) (s T : ℕ) :
    (ZMod p)ˣ → Fin T × ρ' → ZMod (p - 1) :=
  fun y c => ((B₀ (y * (g ^ (c.1.val * s))⁻¹) c.2 : ℕ) : ZMod (p - 1)) + ((c.1.val * s : ℕ) : ZMod (p - 1))

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
  sorry

/-- **The inverter `B` of [PS10, Lemma 84.1]**: the range reduction applied to the loop of
Algorithm 84.2 driven by the majority test with `ℓ` trials per round and `k` rounds. -/
noncomputable def dlInverter (g : (ZMod p)ˣ) {ρ : Type*} [Fintype ρ] (A : (ZMod p)ˣ → ρ → Bool)
    (s T ℓ k : ℕ) : (ZMod p)ˣ → Fin T × (Fin k → Fin ℓ → ZMod (p - 1) × ρ) → ZMod (p - 1) :=
  shiftInverter g (dlLoop g (majOracle g A ℓ) k) s T

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
  sorry

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

/-- **The discrete-log collection in `Z_p^*`** [PS10, Lemma 84.1, "the exponentiation function
`f_{p,g}(x) = g^x mod p` from the discrete-log collection `DL`"]: domains `Z_{p−1}`,
`f_{p,g}(x) = g^x mod p`, the instance generator `G`. -/
noncomputable def fullDLCollection (H : ArithmeticFP) (G : FullGroupGen) : Collection :=
  expCollection H G fun _ h => h.expValid

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
  have := h.1.two_le
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
  simp only [halfStr, halfPred, expEnc, dlP, pairFstD_pairEncode, pairSndD_pairEncode,
    listToNat_natToList (val_lt_two_pow_dlW i x)]

/-- **`half_{p−1}` is polynomial-time computable** (Lem-84.1.0) given the arithmetic bundle.

**Proof sketch.** `2x + 2 ≤ p ⟺ ¬ (p / 2 ≤ x)`: `p / 2` is the quotient of `divModStr ⟨p, 1 0⟩`
(`H.divMod` with the constant numeral of `2`, `polyTimeComputable_const`), the comparison is
`H.le` on `⟨p / 2, x⟩` (`polyTimeComputable_pairFstD`, `_pairSndD`, `.pairEncode`), and the
negation of a one-bit string is `polyTimeComputable_ite` on `polyTimeComputable_pairEq` with
`[true]`. -/
theorem polyTimeComputable_halfStr (H : ArithmeticFP) : PolyTimeComputable halfStr := by
  sorry

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

**Proof sketch.** *Easy:* `halfStr` with `polyTimeComputable_halfStr H` and `halfStr_spec`.
*Hard:* by contradiction with `not_negligible_iff` (through the quantifier form
`Ensemble.indist_iff_exists_negligible`-style of `HardCore`): suppose `A : NUPPT` has
`1/2 + n^{-c} ≤ E_r[Pr_{x, ρ}[A(1^n, ⟨i, f_i x⟩) = half_i x]]` for infinitely many `n ≥ n₀`.
Set `ε := n^{-c}/2`. By `good_instances` (over the generator's coins `r`, index `i = Gen(1^n; r)`)
a set of coins of probability `≥ ε` has per-instance success `≥ 1/2 + ε`; removing the coins
with `p < 2^{n−1}` (probability `≤ δ n` by `hbig`, and `δ n ≤ ε/2` for large `n` since `δ` is
negligible) leaves a *good* set of probability `≥ ε/2` (`uprob_not`, `uprob_or_le`). At such an
index `i = ⟨p, ⟨p−1, g⟩⟩` (valid, `dlW i = n`, `p ≡ 3 (mod 4)`, `2^{n−1} ≤ p < 2^n` on the good
set and by `WellFormedIndex`), the domain is `Z_{p−1}` (`expOrd_of_valid`), `f_i x` is the numeral of
`expo g_u x` with `g_u := expUnit` a generator (`orderOf_expUnit`, `IsGenerator` by
`orderOf_eq_card_of_forall_mem_zpowers`-converse `zpowers_eq_top_of_prime_card`-free counting:
`Nat.card_zpowers`), and `half_i x = halfBit (p−1) x` (`halfPred_eq`), so `A`'s per-instance
success is `predProb (expo g_u) (halfBit (p−1)) A_i` with `A_i y ρ := A.distinguisherL n ⟨i, encD y⟩ ρ`.
Apply `invProb_dlInverter_ge` with `s := ⌊ε(p−1)/4⌋ ≥ 1` (as `p − 1 ≥ 2^{n−1} − 1 ≥ 8n^c` for
large `n`), `T := ⌈(p−1)/s⌉ ≤ 8n^c + 1`, `k := n`, `ℓ := 4n · (2n^c)² = 16 n^{2c+1}`: the inverter
succeeds on the good instances with probability `≥ (3/4)/T ≥ 3/(4(8n^c + 1))`, hence overall
`≥ (ε/2) · 3/(4(8n^c + 1))` (`OneWay.uprob_mul_le_uexp`-style averaging over the good set). The
machine `B` realising `dlInverter` is a non-uniform PPT: advice `⟨A.advice n, 1^{n}⟩`, coins
`T·n + n·ℓ·(2n + A.coins)` (all `PolyExpr`), on `⟨1^n, ⟨i, y⟩⟩` it reads `p`, `g` from `i`,
computes `s` and `T` from `1^n` and `p` (`H.divMod`, `H.mul`), samples `t` and the `r_{j,i}` by
rejection (`sampleBelowL` with `H.le`; the statistical term `n·ℓ·(1/2)^n + (1/2)^n` by
`statClose_rejectionSample`/`StatClose.prod`, `StatClose.abs_uprob_sub_le_prod`), shifts
`y · g^{−ts}` (`H.modExp`, `H.xgcd` for the inverse), and runs the `n` rounds of `dlLoop`
(`Complexity.polyTimeComputable_iterate` with the state `⟨y_j, bits⟩`, D11): quadratic
residuosity by `H.modExp` (`y^{(p−1)/2} = 1`, Euler), the root `y^{(p+1)/4}` by `H.modExp`
(`sqrtMod3`, [PS10, Theorem 58.2]), the `ℓ` oracle calls `A.output` on the layout
`⟨⟨⟨1^n, ⟨i, z_i⟩⟩, A.advice n⟩, ρ_i⟩` (`polyTimeComputable_iterateEmit`, `NUPPT.polyTimeComputable_layout`),
the comparison with `half(r_i)` (`halfStr`), the majority (`polyTimeComputable_majority`), the
negation `p − z` and the bit assembly; finally `(bits + ts) mod (p−1)` as an `n`-bit numeral
(`decodeFin n` reads it back, `bitsToNat_natToBits`). Thus `G.dlProb B n ≥ 3ε/(8(8n^c+1)) − 2n^{2c+2}(1/2)^n`
for infinitely many `n`, an inverse polynomial, contradicting `hDL B` via `not_negligible_iff`. -/
theorem fullDLCollection_hardCore (H : ArithmeticFP) (G : FullGroupGen)
    (hbig : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.FullLengthExcept δ) (hDL : FullDLAssumption G) :
    (fullDLCollection H G).HardCore halfPred := by
  sorry

end TCSlib.Cryptography.Candidates
