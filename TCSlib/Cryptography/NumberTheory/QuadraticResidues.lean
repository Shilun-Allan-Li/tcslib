/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Sampling
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Units.Equiv

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Quadratic residues, square roots and the Chinese remainder theorem

The square-root theory of [PS10, §2.12] behind the Rabin collection:

* `QR N = {x² | x ∈ Z_N^*}`, the quadratic residues modulo `N`, as a subgroup of `Z_N^*`
  (the image of the squaring homomorphism) [PS10, pp. 57 and 59];
* for an odd prime `p`, `QR_p` has `(p−1)/2` elements and every residue has exactly two
  square roots `±x` [PS10, Lemma 57.1];
* for `p ≡ 3 (mod 4)`, `y ↦ y^{(p+1)/4}` extracts square roots in `QR_p`
  [PS10, Theorem 58.2];
* the Chinese remainder theorem for two coprime moduli at the level of unit groups,
  `crtUnits : Z_{pq}^* ≃* Z_p^* × Z_q^*` [PS10, Theorem 58.3, Mathlib's
  `ZMod.chineseRemainder`];
* `x ∈ QR_N` iff both CRT components are residues [PS10, Theorem 59.4];
* squaring on `Z_N^*` is `4`-to-`1` for `N = pq`, `p ≠ q` odd primes [PS10, Theorem 60.5], so
  `|QR_N| = |Z_N^*|/4` [PS10, Corollary 60.6] and squaring pushes the uniform distribution on
  `Z_N^*` to the uniform distribution on `QR_N` (lemma C5, the sampler of
  [PS10, Theorem 63.10]);
* square roots modulo `N` from square roots modulo `p` and `q` [PS10, Claim-60.7 of the
  inventory, p. 60];
* two square roots `x, z` of the same residue with `z ≠ ±x` factor `N` through
  `gcd(x − z, N)` [PS10, proof of Theorem 61.8, Claim-62.1 of the inventory];
* for a Blum integer (`p ≡ q ≡ 3 (mod 4)`) every residue has exactly one square root in
  `QR_N`, computed by `blumSqrt` [PS10, p. 63, Claim-63.1 of the inventory].

**Deviation:** [PS10, Theorems 60.5, 61.7, 61.8, 63.10 and Corollary 60.6] silently need
`p ≠ q` odd primes (they fail for `N = p²` and for `p = 2`); the hypotheses are explicit.
**Deviation:** [PS10, Theorem 59.4] has the typo "`zinQRq`" and its proof labels the two
directions backwards. The CRT is stated for two moduli only (every use in the chapter).

## Main definitions

* `TCSlib.Cryptography.NumberTheory.QR` — the quadratic residues `QR_N ≤ Z_N^*`.
* `TCSlib.Cryptography.NumberTheory.sqTo` — squaring `Z_N^* → QR_N`.
* `TCSlib.Cryptography.NumberTheory.sqrtMod3` — square roots modulo `p ≡ 3 (mod 4)`.
* `TCSlib.Cryptography.NumberTheory.crtUnits` — the CRT isomorphism of unit groups.
* `TCSlib.Cryptography.NumberTheory.blumSqrt` — the square root in `QR_N` for Blum `N`.

## Main results

* `TCSlib.Cryptography.NumberTheory.card_sqrt_eq_two`,
  `TCSlib.Cryptography.NumberTheory.card_QR_prime` — [PS10, Lemma 57.1].
* `TCSlib.Cryptography.NumberTheory.sq_pow_div_four_succ`,
  `TCSlib.Cryptography.NumberTheory.sqrtMod3_sq` — [PS10, Theorem 58.2].
* `TCSlib.Cryptography.NumberTheory.mem_QR_mul_iff` — [PS10, Theorem 59.4].
* `TCSlib.Cryptography.NumberTheory.card_sqrt_mul_eq_four` — [PS10, Theorem 60.5].
* `TCSlib.Cryptography.NumberTheory.card_QR_mul`,
  `TCSlib.Cryptography.NumberTheory.pushesUniform_sqTo` — [PS10, Corollary 60.6] and C5.
* `TCSlib.Cryptography.NumberTheory.sq_crtUnits_symm` — Claim-60.7.
* `TCSlib.Cryptography.NumberTheory.gcd_sub_eq_prime_of_sq_eq_sq` — Claim-62.1.
* `TCSlib.Cryptography.NumberTheory.blumSqrt_sq`,
  `TCSlib.Cryptography.NumberTheory.blumSqrt_mem_QR`,
  `TCSlib.Cryptography.NumberTheory.eq_blumSqrt_of_sq_eq`,
  `TCSlib.Cryptography.NumberTheory.sqTo_bijective_of_blum` — Claim-63.1.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.12: Lemma 57.1, Theorem 58.2, Theorem 58.3, Theorem 59.4, Theorem 60.5,
  Corollary 60.6, the remark on p. 60, the proof of Theorem 61.8, and the remark after
  Theorem 63.10.)
-/

namespace TCSlib.Cryptography.NumberTheory

open Finset

/-! ### Quadratic residues -/

/-- **The quadratic residues** `QR_N = {x² mod N | x ∈ Z_N^*}` [PS10, p. 57 for `N = p`,
p. 59 for `N = pq`], as the subgroup of `Z_N^* = (ZMod N)ˣ` which is the range of the
squaring homomorphism. -/
def QR (N : ℕ) : Subgroup (ZMod N)ˣ := (powMonoidHom 2 : (ZMod N)ˣ →* (ZMod N)ˣ).range

/-- Unfolding: `x ∈ QR_N` iff `x = y²` for some unit `y`. -/
theorem mem_QR_iff {N : ℕ} (x : (ZMod N)ˣ) : x ∈ QR N ↔ ∃ y : (ZMod N)ˣ, y ^ 2 = x := by
  simp [QR, MonoidHom.mem_range, powMonoidHom_apply]

/-- Membership in `QR_N` is decidable (finite search for a root), so `QR_N` is a `Fintype`. -/
instance (N : ℕ) [NeZero N] : DecidablePred (· ∈ QR N) :=
  MonoidHom.decidableMemRange (powMonoidHom 2 : (ZMod N)ˣ →* (ZMod N)ˣ)

/-- Every square is a residue. -/
theorem sq_mem_QR {N : ℕ} (x : (ZMod N)ˣ) : x ^ 2 ∈ QR N := (mem_QR_iff _).2 ⟨x, rfl⟩

/-- Squaring as a map `Z_N^* → QR_N` (the Rabin function `f_N(x) = x² mod N`
[PS10, Theorems 61.7 and 63.10], with its codomain made explicit). -/
def sqTo (N : ℕ) (x : (ZMod N)ˣ) : QR N := ⟨x ^ 2, sq_mem_QR x⟩

/-- Unfolding: the value of `sqTo`. -/
@[simp] theorem coe_sqTo {N : ℕ} (x : (ZMod N)ˣ) : (sqTo N x : (ZMod N)ˣ) = x ^ 2 := rfl

/-- Fibre counting for the squaring map: if every residue has exactly `c` square roots then
`|Z_N^*| = c · |QR_N|` [PS10, Lemma 57.1 and Corollary 60.6, the counting step].

**Proof sketch.** `Finset.card_eq_sum_card_fiberwise` for `sqTo N : Z_N^* → QR_N`; each fibre
`{x | sqTo N x = y}` is `{x | x² = y}`, of size `c`. -/
theorem card_units_eq_mul_card_QR {N : ℕ} [NeZero N] {c : ℕ}
    (hfib : ∀ y ∈ QR N, (univ.filter fun x : (ZMod N)ˣ => x ^ 2 = y).card = c) :
    Fintype.card (ZMod N)ˣ = c * Nat.card (QR N) := by
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ (α := (ZMod N)ˣ),
    Finset.card_eq_sum_card_fiberwise (f := sqTo N) (t := univ) (fun _ _ => mem_univ _)]
  have : ∀ y : QR N, (univ.filter fun x : (ZMod N)ˣ => sqTo N x = y).card = c := by
    intro y
    rw [← hfib y y.2]
    congr 1
    ext x
    simp only [mem_filter, mem_univ, true_and]
    rw [Subtype.ext_iff, coe_sqTo]
  simp only [this, sum_const, card_univ, smul_eq_mul, mul_comm]

/-! ### Square roots modulo a prime -/

section Prime

variable {p : ℕ} [hp : Fact p.Prime]

/-- `-1 ≠ 1` in `Z_p` for an odd prime `p`, in the form `y ≠ -y` for a unit `y`. -/
private theorem ne_neg_self (hp2 : p ≠ 2) (y : (ZMod p)ˣ) : y ≠ -y := by
  intro h
  have h2 : (2 : ZMod p) * (y : ZMod p) = 0 := by
    have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h
    simp only [Units.val_neg] at this
    linear_combination this
  rcases mul_eq_zero.1 h2 with h2 | hy
  · have := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h2)
    rcases (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this with rfl
    exact hp2 rfl
  · exact y.ne_zero hy

/-- **Residues modulo an odd prime have exactly two square roots** [PS10, Lemma 57.1,
"for every `a ∈ QR_p` there are exactly two distinct values `x` with `x² = a`"]: for
`a ∈ QR_p`, `#{x ∈ Z_p^* | x² = a} = 2`.

**Proof sketch.** With `a = y²`, `x² = y²` iff `(x − y)(x + y) = 0` iff `x = ±y` in the
field `Z_p` (`Units.sq_eq_sq_iff_eq_or_eq_neg`), and `y ≠ −y` since `p` is odd. -/
theorem card_sqrt_eq_two (hp2 : p ≠ 2) {a : (ZMod p)ˣ} (ha : a ∈ QR p) :
    (univ.filter fun x : (ZMod p)ˣ => x ^ 2 = a).card = 2 := by
  obtain ⟨y, rfl⟩ := (mem_QR_iff a).1 ha
  have hfilter : (univ.filter fun x : (ZMod p)ˣ => x ^ 2 = y ^ 2) = {y, -y} := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    exact Units.sq_eq_sq_iff_eq_or_eq_neg
  rw [hfilter, Finset.card_pair (ne_neg_self hp2 y)]

/-- **`|QR_p| = (p−1)/2`** for an odd prime `p` [PS10, Lemma 57.1].

**Proof sketch.** Fibre counting (`card_units_eq_mul_card_QR`) with `c = 2`
(`card_sqrt_eq_two`) and `|Z_p^*| = p − 1`. -/
theorem card_QR_prime (hp2 : p ≠ 2) : Nat.card (QR p) = (p - 1) / 2 := by
  have h := card_units_eq_mul_card_QR (N := p) (c := 2) fun y hy => card_sqrt_eq_two hp2 hy
  rw [ZMod.card_units] at h
  omega

/-- The exponent of [PS10, Theorem 58.2]: for `p = 4k + 3`, `p / 4 + 1 = k + 1`. -/
theorem div_four_succ_eq (hp3 : p % 4 = 3) : 4 * (p / 4 + 1) = (p - 1) + 2 := by
  have := Nat.div_add_mod p 4
  have := hp.out.two_le
  omega

/-- **Square roots modulo `p ≡ 3 (mod 4)`** [PS10, Theorem 58.2]: if `p = 4k + 3` and
`y ∈ QR_p` then `(y^{k+1})² = y` (and so `(−y^{k+1})² = y`), with `k + 1 = p / 4 + 1`.

**Proof sketch.** With `y = a²`: `(y^{k+1})² = a^{4k+4} = a^{p−1} · a² = a² = y` by Fermat's
little theorem (`ZMod.units_pow_card_sub_one_eq_one`). -/
theorem sq_pow_div_four_succ (hp3 : p % 4 = 3) {y : (ZMod p)ˣ} (hy : y ∈ QR p) :
    (y ^ (p / 4 + 1)) ^ 2 = y := by
  obtain ⟨a, rfl⟩ := (mem_QR_iff y).1 hy
  calc ((a ^ 2) ^ (p / 4 + 1)) ^ 2 = a ^ (4 * (p / 4 + 1)) := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        ring
    _ = a ^ (p - 1) * a ^ 2 := by rw [div_four_succ_eq hp3, pow_add]
    _ = a ^ 2 := by rw [ZMod.units_pow_card_sub_one_eq_one, one_mul]

/-- The root `y^{(p+1)/4}` of [PS10, Theorem 58.2] is itself a residue (an even power of a
root of `y`): the root selected by the Rabin trapdoor [PS10, Theorem 63.10]. -/
theorem pow_div_four_succ_mem_QR {y : (ZMod p)ˣ} (hy : y ∈ QR p) : y ^ (p / 4 + 1) ∈ QR p := by
  obtain ⟨a, rfl⟩ := (mem_QR_iff y).1 hy
  exact (mem_QR_iff _).2 ⟨a ^ (p / 4 + 1), by rw [← pow_mul, ← pow_mul, mul_comm]⟩

/-- **The square-root algorithm for `p ≡ 3 (mod 4)`** [PS10, Theorem 58.2] on residues:
`sqrtMod3 p y = y^{p/4 + 1}`. -/
def sqrtMod3 (p : ℕ) (y : ZMod p) : ZMod p := y ^ (p / 4 + 1)

/-- **Correctness of `sqrtMod3`** [PS10, Theorem 58.2]: for `p ≡ 3 (mod 4)` and a square
`y ∈ Z_p` (including `0`), `(sqrtMod3 p y)² = y`.

**Proof sketch.** `y = 0` is immediate; otherwise `y = a·a` with `a ≠ 0` and
`(y^{k+1})² = a^{p−1} a² = a²` by `ZMod.pow_card_sub_one_eq_one`. -/
theorem sqrtMod3_sq (hp3 : p % 4 = 3) {y : ZMod p} (hy : IsSquare y) : sqrtMod3 p y ^ 2 = y := by
  obtain ⟨a, rfl⟩ := hy
  unfold sqrtMod3
  by_cases ha : a = 0
  · subst ha
    rw [mul_zero, zero_pow (by omega), zero_pow (by norm_num)]
  calc ((a * a) ^ (p / 4 + 1)) ^ 2 = a ^ (4 * (p / 4 + 1)) := by
        rw [← pow_two, ← pow_mul, ← pow_mul]
        congr 1
        ring
    _ = a ^ (p - 1) * a ^ 2 := by rw [div_four_succ_eq hp3, pow_add]
    _ = a * a := by rw [ZMod.pow_card_sub_one_eq_one ha, one_mul, pow_two]

end Prime

/-! ### The Chinese remainder theorem on unit groups -/

section CRT

variable {p q : ℕ}

/-- **The Chinese remainder theorem for units** [PS10, Theorem 58.3, two moduli]: for coprime
`p, q`, reduction modulo `p` and `q` is a group isomorphism `Z_{pq}^* ≃ Z_p^* × Z_q^*`
(Mathlib's ring isomorphism `ZMod.chineseRemainder` restricted to units). -/
def crtUnits (h : p.Coprime q) : (ZMod (p * q))ˣ ≃* (ZMod p)ˣ × (ZMod q)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

/-- The first component of `crtUnits` is reduction modulo `p`. -/
theorem crtUnits_fst (h : p.Coprime q) (x : (ZMod (p * q))ˣ) :
    ((crtUnits h x).1 : ZMod p) = ((x : ZMod (p * q)).cast : ZMod p) := by
  show (ZMod.chineseRemainder h (x : ZMod (p * q))).1 = _
  exact Prod.fst_zmod_cast _

/-- The second component of `crtUnits` is reduction modulo `q`. -/
theorem crtUnits_snd (h : p.Coprime q) (x : (ZMod (p * q))ˣ) :
    ((crtUnits h x).2 : ZMod q) = ((x : ZMod (p * q)).cast : ZMod q) := by
  show (ZMod.chineseRemainder h (x : ZMod (p * q))).2 = _
  exact Prod.snd_zmod_cast _

/-- **Residues modulo `pq`** [PS10, Theorem 59.4]: for coprime `p, q` and `x ∈ Z_{pq}^*`,
`x ∈ QR_{pq}` iff `x mod p ∈ QR_p` and `x mod q ∈ QR_q`.

**Deviation:** the text's "`zinQRq`" typo; its proof labels `⇒`/`⇐` backwards.

**Proof sketch.** `crtUnits` is a group isomorphism, so it maps squares to squares and a pair
is a square iff both components are; the inverse direction lifts roots `a, b` of the
components to the root `crtUnits⁻¹(a, b)` of `x`. -/
theorem mem_QR_mul_iff (h : p.Coprime q) (x : (ZMod (p * q))ˣ) :
    x ∈ QR (p * q) ↔ (crtUnits h x).1 ∈ QR p ∧ (crtUnits h x).2 ∈ QR q := by
  simp only [mem_QR_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨⟨(crtUnits h y).1, by rw [map_pow]; rfl⟩, ⟨(crtUnits h y).2, by rw [map_pow]; rfl⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨(crtUnits h).symm (a, b), ?_⟩
    rw [← map_pow, show (a, b) ^ 2 = (a ^ 2, b ^ 2) from rfl, ha, hb, MulEquiv.symm_apply_apply]

/-- **Square roots modulo `N` from square roots modulo the factors** [PS10, p. 60, the remark
after Corollary 60.6; Claim-60.7 of the inventory]: if `a² = x mod p` and `b² = x mod q`
then `s = crtUnits⁻¹(a, b)` satisfies `s² = x`. -/
theorem sq_crtUnits_symm (h : p.Coprime q) {x : (ZMod (p * q))ˣ} {a : (ZMod p)ˣ} {b : (ZMod q)ˣ}
    (ha : a ^ 2 = (crtUnits h x).1) (hb : b ^ 2 = (crtUnits h x).2) :
    ((crtUnits h).symm (a, b)) ^ 2 = x := by
  rw [← map_pow, show (a, b) ^ 2 = (a ^ 2, b ^ 2) from rfl, ha, hb, MulEquiv.symm_apply_apply]

/-- The square roots of `x` modulo `pq` correspond to pairs of square roots modulo `p` and
modulo `q` [PS10, proof of Theorem 60.5]: `#{s | s² = x} = #{a | a² = x mod p} · #{b | b² = x mod q}`.

**Proof sketch.** `crtUnits` restricts to a bijection between the root sets
(`Equiv.subtypeEquiv`, `Equiv.subtypeProdEquivProd`). -/
theorem card_sqrt_mul (h : p.Coprime q) [NeZero p] [NeZero q] (x : (ZMod (p * q))ˣ) :
    (univ.filter fun s : (ZMod (p * q))ˣ => s ^ 2 = x).card =
      (univ.filter fun a : (ZMod p)ˣ => a ^ 2 = (crtUnits h x).1).card *
        (univ.filter fun b : (ZMod q)ˣ => b ^ 2 = (crtUnits h x).2).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype, ← Fintype.card_subtype, ← Fintype.card_prod]
  refine Fintype.card_congr (((crtUnits h).toEquiv.subtypeEquiv ?_).trans
    (Equiv.subtypeProdEquivProd (p := fun a : (ZMod p)ˣ => a ^ 2 = (crtUnits h x).1)
      (q := fun b : (ZMod q)ˣ => b ^ 2 = (crtUnits h x).2)))
  intro s
  show s ^ 2 = x ↔ (crtUnits h s).1 ^ 2 = (crtUnits h x).1 ∧ (crtUnits h s).2 ^ 2 = (crtUnits h x).2
  rw [← (crtUnits h).injective.eq_iff, map_pow, Prod.ext_iff]
  rfl

end CRT

/-! ### Squaring modulo `pq` is four-to-one -/

section TwoPrimes

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

/-- Distinct primes are coprime. -/
theorem coprime_of_ne (hpq : p ≠ q) : p.Coprime q := (Nat.coprime_primes hp.out hq.out).2 hpq

/-- **Squaring on `Z_N^*` is `4`-to-`1`** [PS10, Theorem 60.5]: for `N = pq` with `p ≠ q` odd
primes, every residue `y ∈ QR_N` has exactly four square roots in `Z_N^*`.

**Deviation:** the text omits `p ≠ q` and oddness.

**Proof sketch.** `card_sqrt_mul` reduces to the root counts modulo `p` and `q`, each `2`
by `card_sqrt_eq_two` (the components are residues by `mem_QR_mul_iff`). -/
theorem card_sqrt_mul_eq_four (hpq : p ≠ q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) {y : (ZMod (p * q))ˣ}
    (hy : y ∈ QR (p * q)) : (univ.filter fun x : (ZMod (p * q))ˣ => x ^ 2 = y).card = 4 := by
  have h := coprime_of_ne hpq
  obtain ⟨h1, h2⟩ := (mem_QR_mul_iff h y).1 hy
  rw [card_sqrt_mul h, card_sqrt_eq_two hp2 h1, card_sqrt_eq_two hq2 h2]

/-- **`|QR_N| = |Z_N^*| / 4`** [PS10, Corollary 60.6]: for `N = pq`, `p ≠ q` odd primes,
`|Z_N^*| = 4 |QR_N|` (so `|QR_N| = (p−1)(q−1)/4`).

**Proof sketch.** Fibre counting (`card_units_eq_mul_card_QR`) with `c = 4`
(`card_sqrt_mul_eq_four`). -/
theorem card_QR_mul (hpq : p ≠ q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    Fintype.card (ZMod (p * q))ˣ = 4 * Nat.card (QR (p * q)) := by
  haveI : NeZero (p * q) := ⟨mul_ne_zero hp.out.ne_zero hq.out.ne_zero⟩
  exact card_units_eq_mul_card_QR fun y hy => card_sqrt_mul_eq_four hpq hp2 hq2 hy

/-- **Squaring pushes uniform to uniform** (lemma C5 for `QR_N`; the sampler of
[PS10, Theorem 63.10 (3)] and the "same distribution" step of [PS10, Theorem 61.8]): for
`N = pq`, `p ≠ q` odd primes, the square of a uniform unit is a uniform residue.

**Proof sketch.** `pushesUniform_of_card_fiber` with every fibre of `sqTo N` of size `4`
(`card_sqrt_mul_eq_four`). -/
theorem pushesUniform_sqTo (hpq : p ≠ q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    haveI : NeZero (p * q) := ⟨mul_ne_zero hp.out.ne_zero hq.out.ne_zero⟩
    HardcoreBit.PushesUniform (sqTo (p * q)) := by
  haveI : NeZero (p * q) := ⟨mul_ne_zero hp.out.ne_zero hq.out.ne_zero⟩
  refine pushesUniform_of_card_fiber (sqTo (p * q)) (c := 4) (by norm_num) fun y => ?_
  rw [← card_sqrt_mul_eq_four hpq hp2 hq2 y.2]
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and]
  rw [Subtype.ext_iff, coe_sqTo]

/-- **Two square roots that differ by more than a sign factor `N`** [PS10, proof of
Theorem 61.8; Claim-62.1 of the inventory]: for `N = pq` with `p ≠ q` primes and units `x, z`
with `x² = z²`, `z ≠ x` and `z ≠ −x`, the number `gcd((x − z) mod N, N)` is `p` or `q`.

**Proof sketch.** `(x − z)(x + z) = 0` in `Z_N`, so `N ∣ (x−z).val · (x+z).val`; `x − z ≠ 0` and
`x + z ≠ 0` give `N ∤ (x−z).val` and `N ∤ (x+z).val` (both values are `< N`). By
`Nat.Prime.dvd_mul`, each of `p, q` divides `(x−z).val` or `(x+z).val`; not both divide
`(x−z).val` (else `N ∣ (x−z).val`, `Nat.Coprime.mul_dvd_of_dvd_of_dvd`) and not both divide
`(x+z).val`; so exactly one of them divides `(x−z).val`, and the gcd with `N = pq`, a
divisor of `N` different from `1` and `N`, is that prime (`Nat.dvd_mul`, `Nat.dvd_prime`). -/
theorem gcd_sub_eq_prime_of_sq_eq_sq (hpq : p ≠ q) {x z : (ZMod (p * q))ˣ} (hsq : x ^ 2 = z ^ 2)
    (hne : z ≠ x) (hne' : z ≠ -x) :
    Nat.gcd ((x : ZMod (p * q)) - z).val (p * q) = p ∨
      Nat.gcd ((x : ZMod (p * q)) - z).val (p * q) = q := by
  haveI : NeZero (p * q) := ⟨mul_ne_zero hp.out.ne_zero hq.out.ne_zero⟩
  have hcop : p.Coprime q := coprime_of_ne hpq
  -- `(x − z)(x + z) = 0` in `Z_N`
  have hprod : ((x : ZMod (p * q)) - (z : ZMod (p * q))) * ((x : ZMod (p * q)) + (z : ZMod (p * q))) = 0 := by
    have h2 : (x : ZMod (p * q)) ^ 2 = (z : ZMod (p * q)) ^ 2 := by
      have := congrArg Units.val hsq
      simpa [Units.val_pow_eq_pow_val] using this
    linear_combination h2
  have hdvd : p * q ∣ ((x : ZMod (p * q)) - z).val * ((x : ZMod (p * q)) + z).val := by
    have := ZMod.val_mul ((x : ZMod (p * q)) - (z : ZMod (p * q)))
      ((x : ZMod (p * q)) + (z : ZMod (p * q)))
    rw [hprod, ZMod.val_zero] at this
    exact Nat.dvd_of_mod_eq_zero this.symm
  -- neither factor is divisible by `N`
  have hd0 : ¬ p * q ∣ ((x : ZMod (p * q)) - z).val := by
    intro hdv
    have h0 : ((x : ZMod (p * q)) - z) = 0 :=
      (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt hdv (ZMod.val_lt _))
    exact hne (Units.ext (sub_eq_zero.1 h0).symm)
  have he0 : ¬ p * q ∣ ((x : ZMod (p * q)) + z).val := by
    intro hdv
    have h0 : ((x : ZMod (p * q)) + z) = 0 :=
      (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt hdv (ZMod.val_lt _))
    apply hne'
    apply Units.ext
    rw [Units.val_neg]
    exact eq_neg_of_add_eq_zero_right h0
  have hp_dvd := (Nat.Prime.dvd_mul hp.out).1 (dvd_trans (dvd_mul_right p q) hdvd)
  have hq_dvd := (Nat.Prime.dvd_mul hq.out).1 (dvd_trans (dvd_mul_left q p) hdvd)
  rcases hp_dvd with hpd | hpe <;> rcases hq_dvd with hqd | hqe
  · exact absurd (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpd hqd) hd0
  · left
    have hqd : ¬ q ∣ ((x : ZMod (p * q)) - z).val :=
      fun hqd => hd0 (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpd hqd)
    rw [Nat.Coprime.gcd_mul _ hcop, Nat.gcd_eq_right hpd,
      Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hq.out).2 hqd).symm, mul_one]
  · right
    have hpd : ¬ p ∣ ((x : ZMod (p * q)) - z).val :=
      fun hpd => hd0 (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpd hqd)
    rw [Nat.Coprime.gcd_mul _ hcop, Nat.gcd_eq_right hqd,
      Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpd).symm, one_mul]
  · exact absurd (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpe hqe) he0

end TwoPrimes

/-! ### Blum integers -/

section Blum

variable {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]

/-- **The square root in `QR_N` of a Blum integer** [PS10, Theorem 63.10, `f⁻¹_{p,q}`]: for
`N = pq` with `p ≡ q ≡ 3 (mod 4)`, combine the roots `y^{(p+1)/4} mod p` and `y^{(q+1)/4} mod q`
of [PS10, Theorem 58.2] by the CRT. -/
def blumSqrt (h : p.Coprime q) (y : (ZMod (p * q))ˣ) : (ZMod (p * q))ˣ :=
  (crtUnits h).symm ((crtUnits h y).1 ^ (p / 4 + 1), (crtUnits h y).2 ^ (q / 4 + 1))

/-- **`blumSqrt` is a square root** [PS10, Theorem 63.10 (6)]: for `p ≡ q ≡ 3 (mod 4)` and
`y ∈ QR_N`, `(blumSqrt y)² = y`.

**Proof sketch.** The components of `y` are residues (`mem_QR_mul_iff`), their
`(·)^{(p+1)/4}` powers are roots (`sq_pow_div_four_succ`), and `sq_crtUnits_symm` combines
them. -/
theorem blumSqrt_sq (h : p.Coprime q) (hp3 : p % 4 = 3) (hq3 : q % 4 = 3) {y : (ZMod (p * q))ˣ}
    (hy : y ∈ QR (p * q)) : (blumSqrt h y) ^ 2 = y := by
  obtain ⟨h1, h2⟩ := (mem_QR_mul_iff h y).1 hy
  exact sq_crtUnits_symm h (sq_pow_div_four_succ hp3 h1) (sq_pow_div_four_succ hq3 h2)

/-- **`blumSqrt` lands in `QR_N`** [PS10, p. 63, "only one of the roots is also a square"]:
for `y ∈ QR_N`, `blumSqrt y ∈ QR_N`.

**Proof sketch.** Both components are residues (`pow_div_four_succ_mem_QR`), and
`mem_QR_mul_iff` for `crtUnits⁻¹(a, b)`. -/
theorem blumSqrt_mem_QR (h : p.Coprime q) {y : (ZMod (p * q))ˣ} (hy : y ∈ QR (p * q)) :
    blumSqrt h y ∈ QR (p * q) := by
  obtain ⟨h1, h2⟩ := (mem_QR_mul_iff h y).1 hy
  rw [mem_QR_mul_iff h, blumSqrt, MulEquiv.apply_symm_apply]
  exact ⟨pow_div_four_succ_mem_QR h1, pow_div_four_succ_mem_QR h2⟩

/-- **Uniqueness of the residue root** [PS10, p. 63, Claim-63.1 of the inventory]: for a Blum
integer `N = pq` (`p ≠ q`, `p ≡ q ≡ 3 (mod 4)`), a residue `x ∈ QR_N` with `x² = y` equals
`blumSqrt y`.

**Proof sketch.** Let `a = x mod p`, `r = (y mod p)^{(p+1)/4}`; both are residues with
`a² = r² = y mod p`, so `a = ±r` (`Units.sq_eq_sq_iff_eq_or_eq_neg`). If `a = −r` then
`−1 = a r⁻¹` is a residue (quotient of residues, `QR p` a subgroup), contradicting
`ZMod.exists_sq_eq_neg_one_iff` for `p ≡ 3 (mod 4)`; hence `a = r`. Likewise modulo `q`; so
`crtUnits x = crtUnits (blumSqrt y)` and `x = blumSqrt y` by injectivity. -/
theorem eq_blumSqrt_of_sq_eq (h : p.Coprime q) (hp3 : p % 4 = 3) (hq3 : q % 4 = 3)
    {x y : (ZMod (p * q))ˣ} (hx : x ∈ QR (p * q)) (hxy : x ^ 2 = y) : x = blumSqrt h y := by
  obtain ⟨hxp, hxq⟩ := (mem_QR_mul_iff h x).1 hx
  have hy : y ∈ QR (p * q) := hxy ▸ sq_mem_QR x
  obtain ⟨hyp, hyq⟩ := (mem_QR_mul_iff h y).1 hy
  -- the component lemma: a residue root of a residue is the `(·)^{(r+1)/4}` root
  have key : ∀ {r : ℕ} [Fact r.Prime] (_ : r % 4 = 3) {a b : (ZMod r)ˣ},
      a ∈ QR r → b ∈ QR r → a ^ 2 = b → a = b ^ (r / 4 + 1) := by
    intro r _ hr3 a b ha hb hab
    have hroot : (b ^ (r / 4 + 1)) ^ 2 = b := sq_pow_div_four_succ hr3 hb
    have hmem : b ^ (r / 4 + 1) ∈ QR r := pow_div_four_succ_mem_QR hb
    rcases Units.sq_eq_sq_iff_eq_or_eq_neg.1 (hab.trans hroot.symm) with h1 | h1
    · exact h1
    · exfalso
      have hneg : (-1 : (ZMod r)ˣ) ∈ QR r := by
        have : (-1 : (ZMod r)ˣ) = a * (b ^ (r / 4 + 1))⁻¹ := by
          rw [h1, neg_mul, mul_inv_cancel]
        rw [this]
        exact (QR r).mul_mem ha ((QR r).inv_mem hmem)
      obtain ⟨u, hu⟩ := (mem_QR_iff _).1 hneg
      have hsq : IsSquare (-1 : ZMod r) := by
        refine ⟨(u : ZMod r), ?_⟩
        have := congrArg Units.val hu
        rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] at this
        rw [← this, sq]
      exact ZMod.exists_sq_eq_neg_one_iff.1 hsq hr3
  have hp' : (crtUnits h x).1 = (crtUnits h y).1 ^ (p / 4 + 1) :=
    key hp3 hxp hyp (by rw [← hxy, map_pow]; rfl)
  have hq' : (crtUnits h x).2 = (crtUnits h y).2 ^ (q / 4 + 1) :=
    key hq3 hxq hyq (by rw [← hxy, map_pow]; rfl)
  apply (crtUnits h).injective
  rw [blumSqrt, MulEquiv.apply_symm_apply, Prod.ext_iff]
  exact ⟨hp', hq'⟩

/-- **Squaring is a permutation of `QR_N` for a Blum integer** [PS10, Theorem 63.10 (1),
"this makes Rabin a (trapdoor) permutation"]: `sqTo N` restricted to `QR_N` is a bijection of
`QR_N`, with inverse `blumSqrt`.

**Proof sketch.** Injective by `eq_blumSqrt_of_sq_eq` (two residue roots of the same `y` are
both `blumSqrt y`); surjective by `blumSqrt_sq` and `blumSqrt_mem_QR`. -/
theorem sqTo_bijective_of_blum (h : p.Coprime q) (hp3 : p % 4 = 3) (hq3 : q % 4 = 3) :
    Function.Bijective (fun x : QR (p * q) => sqTo (p * q) (x : (ZMod (p * q))ˣ)) := by
  constructor
  · intro x x' hxx'
    have hsq : (x : (ZMod (p * q))ˣ) ^ 2 = (x' : (ZMod (p * q))ˣ) ^ 2 := by
      have := congrArg (fun u : QR (p * q) => (u : (ZMod (p * q))ˣ)) hxx'
      simpa using this
    exact Subtype.ext ((eq_blumSqrt_of_sq_eq h hp3 hq3 x.2 rfl).trans
      (eq_blumSqrt_of_sq_eq h hp3 hq3 x'.2 hsq.symm).symm)
  · intro y
    exact ⟨⟨blumSqrt h y, blumSqrt_mem_QR h y.2⟩, Subtype.ext (blumSqrt_sq h hp3 hq3 y.2)⟩

end Blum

end TCSlib.Cryptography.NumberTheory
