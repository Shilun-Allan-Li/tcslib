/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Candidates.RSA
import TCSlib.Cryptography.NumberTheory.QuadraticResidues

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Rabin: the Rabin collection, Rabin ⟺ factoring, Rabin trapdoor permutations

The Rabin material of [PS10, §2.12]: the collection `R = {f_N(x) = x² mod N}` with indices
`N = pq`, domain `Z_N^*` and range `QR_N`, one-way under the factoring assumption
[PS10, Theorem 61.7]; the equivalence of its one-wayness with the factoring assumption
[PS10, Theorem 61.8] through the factoring adversary `A'(N)` of [PS10, Algorithm 62.9]
("sample `x ← Z_N^*`, `y := x²`, `z ← A(N, y)`, output `gcd(x − z, N)`") and the
symmetry lemma "the root returned differs from `±x` half the time" (Claim-62.2 of the inventory,
replacing the text's heuristic "one of the four roots with equal probability"); and the
Rabin collection of *trapdoor permutations* on Blum integers `N = pq`,
`p ≡ q ≡ 3 (mod 4)`, with domain `QR_N`, where squaring is a permutation with the unique
residue root as inverse [PS10, Theorem 63.10].

Conventions (decision log "Rabin/RSA scope", plan errors 5–6; D3–D5, D10, D11). The moduli
are products of distinct *odd* primes of `Π_n` for Theorems 61.7/61.8 (the symmetry lemma
needs `−1 ≠ 1` modulo both factors) and of distinct *Blum* primes for Theorem 63.10; the
factoring assumption is used on these restricted index distributions through the
conditioning lemmas `oddFactorProb_le`, `blumFactorProb_le`, the latter under the explicit
density hypothesis `BlumDensity` (`2^n ≤ 4n · #{p ∈ Π_n : p ≡ 3 (mod 4)}`, not available in
Mathlib). The generators run truncated restricted `SamplePrime` loops with the fallbacks
`(3, 5)` and `(3, 7)` and output `⟨N, ⟨p, q⟩⟩`; domains at string indices follow the RSA
module (valid indices carry `Z_N^*` resp. `QR_N`, invalid ones the one-element group); the
evaluator is one modular squaring; the trapdoor inverter combines the roots
`y^{(p+1)/4} mod p`, `y^{(q+1)/4} mod q` [PS10, Theorem 58.2] by the CRT formula of
[PS10, Theorem 58.3]. Every machine statement is conditional on `ArithmeticFP`.

**Deviation:** Candidates: `A` receives `1^n` in Assumptions 30.1/52.2/53.1; `Π_n`
throughout; `p ≠ q` (odd / Blum) in RSA and Rabin; expected time replaced by strict PPT
with `2^{-n}` failure. Theorem 61.8 (⇐) is stated for Blum moduli only (square roots modulo
`p ≡ 1 (mod 4)` are not formalized, text gap); Theorem 63.10's hardness takes the density
hypothesis `BlumDensity`; the generators work at `max n 3`.

## Main definitions

* `TCSlib.Cryptography.Candidates.OddDistinctPrimes`, `BlumDistinctPrimes`, `oddFactorProb`,
  `blumFactorProb`, `BlumFactoringAssumption`, `BlumDensity` — the restricted index
  distributions and hypotheses.
* `TCSlib.Cryptography.Candidates.rabinGenParams`, `rabinGenOut`, `oddGen`, `blumGen`,
  `rabinSampler`, `blumSampler`, `blumInvNat`, `blumInv` — generators, samplers, inverter.
* `TCSlib.Cryptography.Candidates.rabinCollection` [PS10, Theorem 61.7];
  `TCSlib.Cryptography.Candidates.rabinBlumTrapdoor` [PS10, Theorem 63.10].
* `TCSlib.Cryptography.Candidates.rabinFactorStep`, `rabinFactorer` — the adversary `A'`
  of [PS10, Algorithm 62.9]; `rabinBlumInverter` — the root finder from a factorer
  [PS10, Theorem 61.8 ⇐].

## Main results

* `TCSlib.Cryptography.Candidates.rabin_symmetry` — Claim-62.2 (the symmetry lemma).
* `TCSlib.Cryptography.Candidates.rabinCollection_oneWay` [PS10, Theorems 61.7, 61.8 ⇒].
* `TCSlib.Cryptography.Candidates.blumFactoring_of_rabinBlum_oneWay` [PS10, Theorem 61.8 ⇐].
* `TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_oneWay` [PS10, Theorem 63.10].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.12: Theorems 58.2, 58.3, 60.5, 61.7, 61.8, Algorithm 62.9, Theorem 63.10.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definition 2.1 (the concrete inversion experiment).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory Finset

/-! ## Restricted index distributions -/

/-- Pairs of distinct *odd* primes of `Π_n`: the index distribution of the Rabin collection
[PS10, Theorem 61.7] (`p ≠ q` odd is needed by Theorem 60.5 and the symmetry lemma). -/
abbrev OddDistinctPrimes (n : ℕ) : Type := {z : DistinctPrimes n // z.p ≠ 2 ∧ z.q ≠ 2}

/-- Pairs of distinct *Blum* primes (`≡ 3 (mod 4)`) of `Π_n`: the index distribution of
[PS10, Theorem 63.10]. -/
abbrev BlumDistinctPrimes (n : ℕ) : Type := {z : DistinctPrimes n // z.p % 4 = 3 ∧ z.q % 4 = 3}

/-- The Blum primes of `Π_n`. -/
abbrev BlumPrimes (n : ℕ) : Type := {p : Primes n // (p.1 : ℕ) % 4 = 3}

/-- Blum primes are odd. -/
theorem BlumDistinctPrimes.ne_two {n : ℕ} (z : BlumDistinctPrimes n) : z.1.p ≠ 2 ∧ z.1.q ≠ 2 :=
  ⟨fun h => by have := z.2.1; rw [h] at this; omega, fun h => by have := z.2.2; rw [h] at this; omega⟩

/-- The factoring experiment of [PS10, Assumption 30.1] on uniform pairs of distinct odd
primes (`factorProb` conditioned on oddness). -/
noncomputable def oddFactorProb (A : NUPPT) (n : ℕ) : ℝ :=
  uprob fun w : OddDistinctPrimes n × A.Coins n =>
    ∃ x : Fin n → Bool, A.inverter n n (2 * n) (modulusBits n w.1.1) w.2 = some x ∧
      (bitsToNat x = w.1.1.p ∨ bitsToNat x = w.1.1.q)

/-- The factoring experiment on uniform pairs of distinct Blum primes. -/
noncomputable def blumFactorProb (A : NUPPT) (n : ℕ) : ℝ :=
  uprob fun w : BlumDistinctPrimes n × A.Coins n =>
    ∃ x : Fin n → Bool, A.inverter n n (2 * n) (modulusBits n w.1.1) w.2 = some x ∧
      (bitsToNat x = w.1.1.p ∨ bitsToNat x = w.1.1.q)

/-- **The factoring assumption on Blum integers** [PS10, Theorem 63.10, "if the Factoring
Assumption holds", restricted to `p ≡ q ≡ 3 (mod 4)`]: every non-uniform PPT factors a
uniform Blum modulus with negligible probability. -/
def BlumFactoringAssumption : Prop := ∀ A : NUPPT, Negligible fun n => blumFactorProb A n

/-- **Density of Blum primes** (explicit hypothesis, decision log "Rabin/RSA scope"):
`2^n ≤ 4n · #{p < 2^n prime, p ≡ 3 (mod 4)}` for `n ≥ 2`, the analogue of
[PS10, Claim 33.1] for primes `≡ 3 (mod 4)` (true by Dirichlet's theorem with error terms,
not available in Mathlib). -/
def BlumDensity : Prop := ∀ n, 2 ≤ n → 2 ^ n ≤ 4 * n * Fintype.card (BlumPrimes n)

/-- **Conditioning on oddness** [PS10, Theorem 61.7, implicit]: for `n ≥ 6` the factoring
probability on odd pairs is at most twice the factoring probability.

**Proof sketch.** `uprob_and_eq_mul_subtype` with `E` = "both odd" (transported along
`uprob_subtype_prod_eq`): `Pr[E] · oddFactorProb = Pr[E ∧ S] ≤ factorProb`, and
`Pr[¬E] ≤ Pr[p = 2] + Pr[q = 2] = 2/|Π_n| ≤ 4n/2^n ≤ 1/2` for `n ≥ 6`
(`one_div_card_primes_le`, `uprob_eq_one_div_card` on the first coordinate), so
`Pr[E] ≥ 1/2`. -/
theorem oddFactorProb_le (A : NUPPT) {n : ℕ} (hn : 6 ≤ n) : oddFactorProb A n ≤ 2 * factorProb A n := by
  sorry

/-- **Conditioning on Blum primes** under the density hypothesis: for `n ≥ 6`,
`blumFactorProb A n ≤ 64 n² · factorProb A n`.

**Proof sketch.** As `oddFactorProb_le` with `E` = "both `≡ 3 (mod 4)`":
`Pr[E] = B(B−1)/(|Π_n|(|Π_n|−1)) ≥ ((B−1)/2^n)² ≥ 1/(64n²)` with `B = #BlumPrimes n ≥ 2^n/(4n)`
(`hD`), `B − 1 ≥ 2^n/(8n)` for `n ≥ 6` and `|Π_n| ≤ 2^n`. -/
theorem blumFactorProb_le (hD : BlumDensity) (A : NUPPT) {n : ℕ} (hn : 6 ≤ n) :
    blumFactorProb A n ≤ 64 * (n : ℝ) ^ 2 * factorProb A n := by
  sorry

/-- **Factoring is hard on Blum integers** under the factoring assumption and the density
hypothesis: `blumFactorProb_le`, `hF A`, `Negligible.mul_pow`, `Negligible.const_mul`,
`Negligible.mono` (threshold `6`). -/
theorem blumFactoring_of_factoring (hD : BlumDensity) (hF : FactoringAssumption) :
    BlumFactoringAssumption := by
  sorry

/-! ## The symmetry lemma (Claim-62.2) -/

/-- The unit `u = CRT⁻¹(1, −1)` of `Z_{pq}^*`: a square root of `1` different from `±1`
[PS10, proof of Theorem 61.8, "it can only be that they are congruent modulo `p` and `q`"]. -/
noncomputable def crtNegOne {p q : ℕ} (h : p.Coprime q) : (ZMod (p * q))ˣ :=
  (crtUnits h).symm (1, -1)

/-- `u² = 1`. -/
theorem crtNegOne_sq {p q : ℕ} (h : p.Coprime q) : crtNegOne h ^ 2 = 1 := by
  rw [crtNegOne, ← map_pow, show ((1 : (ZMod p)ˣ), (-1 : (ZMod q)ˣ)) ^ 2 = (1, 1) by
    rw [Prod.pow_mk, one_pow, neg_one_sq], Prod.mk_one_one, map_one]

/-- `u ≠ 1` for `q` odd: the second CRT component of `u` is `−1 ≠ 1` in `Z_q`
(`ZMod.neg_one_ne_one`). -/
theorem crtNegOne_ne_one {p q : ℕ} [Fact p.Prime] [hq : Fact q.Prime] (h : p.Coprime q)
    (hq2 : q ≠ 2) : crtNegOne h ≠ 1 := by
  intro heq
  haveI : Fact (2 < q) := ⟨lt_of_le_of_ne hq.out.two_le (Ne.symm hq2)⟩
  have h1 : ((crtUnits h (crtNegOne h)).2 : ZMod q) = -1 := by
    rw [crtNegOne, MulEquiv.apply_symm_apply]; simp
  have h2 := crtUnits_snd h (crtNegOne h)
  rw [h1, heq, Units.val_one, ZMod.cast_one (dvd_mul_left q p)] at h2
  exact ZMod.neg_one_ne_one h2

/-- `u ≠ −1` for `p` odd: the first CRT component of `u` is `1 ≠ −1` in `Z_p`. -/
theorem crtNegOne_ne_neg_one {p q : ℕ} [hp : Fact p.Prime] [Fact q.Prime] (h : p.Coprime q)
    (hp2 : p ≠ 2) : crtNegOne h ≠ -1 := by
  intro heq
  haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)⟩
  have h1 : ((crtUnits h (crtNegOne h)).1 : ZMod p) = 1 := by
    rw [crtNegOne, MulEquiv.apply_symm_apply]; simp
  have h2 := crtUnits_fst h (crtNegOne h)
  rw [h1, heq, Units.val_neg, Units.val_one, ZMod.cast_neg (dvd_mul_right p q),
    ZMod.cast_one (dvd_mul_right p q)] at h2
  exact ZMod.neg_one_ne_one h2.symm

/-- **The symmetry lemma** (Claim-62.2 of the inventory; the concrete content of
[PS10, Theorem 61.8 ⇒] replacing "`A` outputs one of the four square roots with equal
probability"): for `N = pq`, `p ≠ q` odd primes, and any (possibly failing) root finder
`Z : Z_N^* → ρ → Option Z_N^*` that sees only `y = x²` and independent coins, the probability
that `Z(x²)` is a root of `x²` *different from `±x`* is at least half the probability that
it is a root of `x²`.

**Proof sketch.** Let `u := crtNegOne` and `σ(x) := u x`, a bijection of `Z_N^*`
(`Equiv.mulLeft`) with `σ(x)² = x²` (`crtNegOne_sq`) and `σ(x) ∉ {±x}` (else `u = ±1`,
i.e. `(1, −1) = (1, 1)` or `(−1, −1)` in `Z_p^* × Z_q^*`, contradicting `−1 ≠ 1` for odd
`p, q`, `crtNegOne_ne_one`, `crtNegOne_ne_neg_one`). Let `S(x, r)` be "the answer is a
root", `B(x, r)` "`S` and the answer is `±x`" and `G(x, r)` "`S` and the answer is not
`±x`". Then `B(σ x, r)` implies `G(x, r)` (the answer is `±ux`, which is not `±x`), so
`Pr[B] = Pr[B ∘ (σ × id)] ≤ Pr[G]` (`uprob_comp_equiv (Equiv.prodCongr σ (Equiv.refl ρ))`,
`uprob_mono`), and `Pr[S] ≤ Pr[B ∨ G] ≤ Pr[B] + Pr[G] ≤ 2 Pr[G]` (`uprob_or_le`). -/
theorem rabin_symmetry {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hpq : p ≠ q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) {ρ : Type*} [Fintype ρ]
    (Z : (ZMod (p * q))ˣ → ρ → Option (ZMod (p * q))ˣ) :
    uprob (fun w : (ZMod (p * q))ˣ × ρ => ∃ z, Z (w.1 ^ 2) w.2 = some z ∧ z ^ 2 = w.1 ^ 2) ≤
      2 * uprob (fun w : (ZMod (p * q))ˣ × ρ =>
        ∃ z, Z (w.1 ^ 2) w.2 = some z ∧ z ^ 2 = w.1 ^ 2 ∧ z ≠ w.1 ∧ z ≠ -w.1) := by
  haveI : NeZero (p * q) := ⟨mul_ne_zero hp.out.ne_zero hq.out.ne_zero⟩
  have hcop := coprime_of_ne hpq
  have hu2 : crtNegOne hcop ^ 2 = 1 := crtNegOne_sq hcop
  have hu1 : crtNegOne hcop ≠ 1 := crtNegOne_ne_one hcop hq2
  have hu1' : crtNegOne hcop ≠ -1 := crtNegOne_ne_neg_one hcop hp2
  let e : (ZMod (p * q))ˣ × ρ ≃ (ZMod (p * q))ˣ × ρ :=
    Equiv.prodCongr (Equiv.mulLeft (crtNegOne hcop)) (Equiv.refl ρ)
  have hB : uprob (fun w : (ZMod (p * q))ˣ × ρ =>
      ∃ z, Z (w.1 ^ 2) w.2 = some z ∧ z ^ 2 = w.1 ^ 2 ∧ (z = w.1 ∨ z = -w.1)) ≤
      uprob (fun w : (ZMod (p * q))ˣ × ρ =>
        ∃ z, Z (w.1 ^ 2) w.2 = some z ∧ z ^ 2 = w.1 ^ 2 ∧ z ≠ w.1 ∧ z ≠ -w.1) := by
    rw [← uprob_comp_equiv e]
    apply uprob_mono
    rintro ⟨x, r⟩ ⟨z, hz, hz2, hzx⟩
    have hsq : (crtNegOne hcop * x) ^ 2 = x ^ 2 := by rw [mul_pow, hu2, one_mul]
    simp only [e, Equiv.prodCongr_apply, Equiv.coe_mulLeft, Equiv.refl_apply, Prod.map_apply,
      hsq] at hz hz2 hzx
    refine ⟨z, hz, hz2, ?_, ?_⟩
    · intro hzx'
      rw [hzx'] at hzx
      rcases hzx with h | h
      · exact hu1 (mul_right_cancel ((one_mul x).trans h)).symm
      · have h' : crtNegOne hcop * x = -1 * x := by
          rw [neg_one_mul]; exact neg_eq_iff_eq_neg.mp h.symm
        exact hu1' (mul_right_cancel h')
    · intro hzx'
      rw [hzx'] at hzx
      rcases hzx with h | h
      · have h' : crtNegOne hcop * x = -1 * x := by rw [neg_one_mul]; exact h.symm
        exact hu1' (mul_right_cancel h')
      · exact hu1 (mul_right_cancel ((one_mul x).trans (neg_inj.mp h))).symm
  calc uprob (fun w : (ZMod (p * q))ˣ × ρ => ∃ z, Z (w.1 ^ 2) w.2 = some z ∧ z ^ 2 = w.1 ^ 2)
      ≤ uprob (fun w : (ZMod (p * q))ˣ × ρ =>
          (∃ z, Z (w.1 ^ 2) w.2 = some z ∧ z ^ 2 = w.1 ^ 2 ∧ (z = w.1 ∨ z = -w.1)) ∨
          (∃ z, Z (w.1 ^ 2) w.2 = some z ∧ z ^ 2 = w.1 ^ 2 ∧ z ≠ w.1 ∧ z ≠ -w.1)) := by
        apply uprob_mono
        rintro w ⟨z, hz, hz2⟩
        by_cases h : z = w.1 ∨ z = -w.1
        · exact Or.inl ⟨z, hz, hz2, h⟩
        · push_neg at h
          exact Or.inr ⟨z, hz, hz2, h.1, h.2⟩
    _ ≤ _ + _ := uprob_or_le _ _
    _ ≤ 2 * _ := by linarith

/-! ## Generators for restricted prime classes -/

/-- The number of trials `4m²` of the restricted prime sampler (density at least `1/(4m)`
of odd primes, resp. of Blum primes under `BlumDensity`, gives failure `≤ e^{-m}`). -/
def rabinTrials : PolyExpr := .mul (.const 4) (.pow .var 2)

/-- The coins of one restricted prime sampler: `4m² · m`. -/
def rabinPrimeCoins : PolyExpr := .mul rabinTrials .var

/-- The coins of the Rabin generators: two restricted prime samplers. -/
def rabinGenCoins : PolyExpr := .mul (.const 2) rabinPrimeCoins

/-- One truncated run of `SamplePrime` restricted to a class `P` of primes
[PS10, Theorem 63.10, "`Gen(1^n)` samples a pair `(N, (p, q))` s.t. `N ∈ I`"; Algorithm 50.16
with the extra test]: `Candidates.rejectBlocksL` with the test "prime and in `P`" on `4m²`
blocks of `m` bits, output as the `m`-bit numeral of the first hit, or of the fallback prime
`d` (in `P`) when every block is rejected. Repair (run-3 audit P7-6/P7-7): an instance of the
shared `rejectBlocksL` (formerly the typed `firstHit` on `chunk`ed blocks with the fallback
`[]`), so that `statClose_rejectBlocksL` applies with the default `d`. -/
def samplePrimePL (P : ℕ → Prop) [DecidablePred P] (m d : ℕ) (r : List Bool) : List Bool :=
  natToList m ((rejectBlocksL (fun v => v.Prime ∧ P v) m m (4 * m ^ 2) r).getD d)

/-- The parameters of a Rabin generator: a pair of distinct primes of `Π_m` in the class `P`. -/
structure RabinParams (P : ℕ → Prop) (m : ℕ) where
  /-- The pair of distinct primes. -/
  z : DistinctPrimes m
  /-- `p ∈ P`. -/
  hp : P z.p
  /-- `q ∈ P`. -/
  hq : P z.q

/-- A pair of primes below `8` as an element of `DistinctPrimes (max m 3)`. -/
def smallDistinctPrimes (m : ℕ) {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b)
    (ha8 : a < 8) (hb8 : b < 8) : DistinctPrimes (max m 3) :=
  have h8 : 8 ≤ 2 ^ max m 3 :=
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ max m 3 := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  ⟨(⟨⟨a, lt_of_lt_of_le ha8 h8⟩, ha⟩, ⟨⟨b, lt_of_lt_of_le hb8 h8⟩, hb⟩), hab⟩

/-- The fallback `(3, 5)` of the odd generator. -/
def oddDefault (m : ℕ) : RabinParams (· ≠ 2) (max m 3) :=
  ⟨smallDistinctPrimes m Nat.prime_three Nat.prime_five (by norm_num) (by norm_num) (by norm_num),
    (by decide : (3 : ℕ) ≠ 2), (by decide : (5 : ℕ) ≠ 2)⟩

/-- The fallback `(3, 7)` of the Blum generator. -/
def blumDefault (m : ℕ) : RabinParams (· % 4 = 3) (max m 3) :=
  ⟨smallDistinctPrimes m Nat.prime_three (by decide : Nat.Prime 7) (by norm_num) (by norm_num)
    (by norm_num), (by decide : 3 % 4 = 3), (by decide : 7 % 4 = 3)⟩

/-- **The computation of a Rabin generator** at parameter `m` (primes from `Π_{max m 3}`):
two restricted `SamplePrime` runs on the two halves of the coins (fallback primes: the
components of `dflt m`), the fallback `dflt` unless both are distinct primes of the class
below `2^{max m 3}`. -/
def rabinGenParams (P : ℕ → Prop) [DecidablePred P] (dflt : ∀ m, RabinParams P (max m 3)) (m : ℕ)
    (r : List Bool) : RabinParams P (max m 3) :=
  let L := rabinPrimeCoins.eval (max m 3)
  let p := listToNat (samplePrimePL P (max m 3) (dflt m).z.p (r.take L))
  let q := listToNat (samplePrimePL P (max m 3) (dflt m).z.q ((r.drop L).take L))
  if h : p.Prime ∧ q.Prime ∧ p ≠ q ∧ p < 2 ^ max m 3 ∧ q < 2 ^ max m 3 ∧ P p ∧ P q then
    ⟨⟨(⟨⟨p, h.2.2.2.1⟩, h.1⟩, ⟨⟨q, h.2.2.2.2.1⟩, h.2.1⟩), h.2.2.1⟩, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  else dflt m

/-- The index `N = pq` as a `2m`-bit numeral. -/
def rabinIndexOf {P : ℕ → Prop} (m : ℕ) (R : RabinParams P m) : List Bool :=
  natToList (2 * m) (R.z.p * R.z.q)

/-- The output `⟨N, ⟨p, q⟩⟩` of a Rabin generator at parameter `m` on the coins `r`
(the trapdoor `⟨p, q⟩` with `m`-bit numerals, `encodeDistinctPrimes`). -/
def rabinGenOut (P : ℕ → Prop) [DecidablePred P] (dflt : ∀ m, RabinParams P (max m 3)) (m : ℕ)
    (r : List Bool) : List Bool :=
  pairEncode (rabinIndexOf _ (rabinGenParams P dflt m r))
    (encodeDistinctPrimes _ (rabinGenParams P dflt m r).z)

/-- The string function of a Rabin generator on the raw layout `⟨⟨⟨1^n, []⟩, α⟩, r⟩`. -/
def rabinGenRaw (P : ℕ → Prop) [DecidablePred P] (dflt : ∀ m, RabinParams P (max m 3))
    (z : List Bool) : List Bool :=
  rabinGenOut P dflt (NUPPT.inParam z).length (NUPPT.inCoins z)

/-- **The odd generator is polynomial-time** [PS10, Theorem 61.7, "`I` is easy to sample"].

**Proof sketch.** As `polyTimeComputable_rsaGenRaw` without the exponent: the coins are cut
at `1^{4m³}` (`polyTimeComputable_pairTakePoly`/`_pairDropPoly rabinPrimeCoins`); each
prime is an `iterateFind` loop (`Complexity.polyTimeComputable_iterateFind`) whose test is
`H.prime` conjoined with the oddness test (the last bit, `polyTimeComputable_lenEq`-style
projection) and whose `none` branch is the constant fallback numeral; the validity test uses
`H.prime`, `polyTimeComputable_pairEq`, `H.le`; `N` by `H.mul`; the fallback pair is a
constant (`polyTimeComputable_ite`). -/
theorem polyTimeComputable_oddGenRaw (H : ArithmeticFP) :
    PolyTimeComputable (rabinGenRaw (· ≠ 2) oddDefault) := by
  sorry

/-- **The Blum generator is polynomial-time** [PS10, Theorem 63.10 (2)]: as
`polyTimeComputable_oddGenRaw` with the test "`p ≡ 3 (mod 4)`" on the last two bits. -/
theorem polyTimeComputable_blumGenRaw (H : ArithmeticFP) :
    PolyTimeComputable (rabinGenRaw (· % 4 = 3) blumDefault) := by
  sorry

/-- **The generator of the Rabin collection** (odd distinct primes) as a uniform `NUPPT`. -/
noncomputable def oddGen (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_oddGenRaw H) rabinGenCoins

/-- **The generator of the Blum Rabin collection** as a uniform `NUPPT`,
`Gen(1^n) = ⟨N, ⟨p, q⟩⟩` [PS10, Theorem 63.10 (2)].

**Deviation (run-3 audit P3-5):** the trapdoor inverter receives `⟨⟨p, q⟩, y⟩` without the
index `N` (`TrapdoorCollection.inv_spec`; the literal `Inv((i, t), y)` form of Definition
56.1 (6) was not adopted) and recomputes `N = pq`. -/
noncomputable def blumGen (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_blumGenRaw H) rabinGenCoins

/-- The activation of the odd generator. -/
theorem oddGen_runAt (H : ArithmeticFP) (n : ℕ) (r : (oddGen H).Coins n) :
    (oddGen H).runAt n [] r = rabinGenOut (· ≠ 2) oddDefault n (List.ofFn r) := by
  rw [NUPPT.runAt_eq]
  unfold oddGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp [rabinGenRaw, NUPPT.inParam, NUPPT.inCoins, NUPPT.advInput]

/-- The activation of the Blum generator. -/
theorem blumGen_runAt (H : ArithmeticFP) (n : ℕ) (r : (blumGen H).Coins n) :
    (blumGen H).runAt n [] r = rabinGenOut (· % 4 = 3) blumDefault n (List.ofFn r) := by
  rw [NUPPT.runAt_eq]
  unfold blumGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp [rabinGenRaw, NUPPT.inParam, NUPPT.inCoins, NUPPT.advInput]

/-- The modulus read from a Rabin index is `N`. -/
@[simp] theorem listToNat_rabinIndexOf {P : ℕ → Prop} (m : ℕ) (R : RabinParams P m) :
    listToNat (rabinIndexOf m R) = R.z.p * R.z.q :=
  listToNat_natToList R.z.mul_lt

/-! ## The Rabin collection [PS10, Theorem 61.7] -/

/-- The modulus of the domain at the index `N`: `N` itself, or `1` when the string reads as
`0` (so that the domain is a finite group). -/
def rabinMod (i : List Bool) : ℕ := max (listToNat i) 1

instance (i : List Bool) : NeZero (rabinMod i) := ⟨by unfold rabinMod; omega⟩

/-- `rabinMod i ≤ 2^{|i|}`. -/
theorem rabinMod_le (i : List Bool) : rabinMod i ≤ 2 ^ i.length := by
  unfold rabinMod
  have := listToNat_lt_two_pow i
  have := Nat.one_le_two_pow (n := i.length)
  omega

/-- The encoding of `x ∈ Z_N^*`: its residue as a numeral of the width of the index. -/
def rabinEnc (i : List Bool) (x : (ZMod (rabinMod i))ˣ) : List Bool :=
  natToList i.length (x : ZMod (rabinMod i)).val

/-- The decoder of `Z_N^*`: a numeral of the width of the index reading as a number below `N`
coprime to `N`. -/
def rabinDec (i : List Bool) (w : List Bool) : Option (ZMod (rabinMod i))ˣ :=
  if h : w.length = i.length ∧ listToNat w < rabinMod i ∧ Nat.Coprime (listToNat w) (rabinMod i) then
    some (ZMod.unitOfCoprime (listToNat w) h.2.2)
  else none

/-- Decoding inverts encoding on `Z_N^*`. -/
theorem rabinDec_rabinEnc (i : List Bool) (x : (ZMod (rabinMod i))ˣ) : rabinDec i (rabinEnc i x) = some x := by
  have hl : listToNat (rabinEnc i x) = (x : ZMod (rabinMod i)).val :=
    listToNat_natToList (lt_of_lt_of_le (ZMod.val_lt _) (rabinMod_le i))
  rw [rabinDec, dif_pos ⟨by simp [rabinEnc], by rw [hl]; exact ZMod.val_lt _,
    by rw [hl]; exact ZMod.val_coe_unit_coprime x⟩]
  congr 1
  ext
  simp [ZMod.coe_unitOfCoprime, hl]

/-- `f_N(x) = x² mod N` on the encoded element, mirroring the evaluator [PS10, Theorem 61.7]. -/
def rabinF (i : List Bool) (x : (ZMod (rabinMod i))ˣ) : List Bool :=
  natToList i.length (listToNat (rabinEnc i x) ^ 2 % listToNat i)

/-- The evaluator of the Rabin collections on `⟨N, x⟩`: `modExpStr ⟨x, ⟨2, N⟩⟩`
[PS10, Theorem 61.7, one modular squaring]. -/
def rabinEval (z : List Bool) : List Bool :=
  modExpStr (pairEncode (pairSndD z) (pairEncode [true, false] (pairFstD z)))

/-- The evaluator computes `rabinF` on encoded elements. -/
theorem rabinEval_spec (i : List Bool) (x : (ZMod (rabinMod i))ˣ) :
    rabinEval (pairEncode i (rabinEnc i x)) = rabinF i x := by
  simp [rabinEval, rabinF, listToNat]

/-- The evaluator is polynomial-time given modular exponentiation. -/
theorem polyTimeComputable_rabinEval (H : ArithmeticFP) : PolyTimeComputable rabinEval :=
  H.modExp.comp (polyTimeComputable_pairSndD.pairEncode
    ((polyTimeComputable_const [true, false]).pairEncode polyTimeComputable_pairFstD))

/-- The string function of the domain sampler of the Rabin collection on the raw layout
`⟨⟨⟨1^n, N⟩, α⟩, r⟩`: a unit modulo `N` by rejection (`unitSampleStr`). -/
def rabinSampleRaw (z : List Bool) : List Bool :=
  unitSampleStr (NUPPT.inArg z) (NUPPT.inParam z).length (NUPPT.inCoins z)

/-- **The domain sampler of the Rabin collection**: a uniform `NUPPT` with `T(n) B(n)` coins
(`polyTimeComputable_unitSampleStr`). -/
noncomputable def rabinSampler (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_unitSampleStr H NUPPT.polyTimeComputable_inArg)
    rsaSampleCoins

/-- **The Rabin sampler's outputs decode and evaluate honestly** (the clause `sample_spec` of
`Collection`, [PS10, Definition 41.1 (2)]; repair of the run-3 audit, P3-1): at every parameter
the generated index is the numeral of `N = pq` (`oddGen_runAt`, `rabinIndexOf`) with
`rabinMod i = N` (`listToNat_rabinIndexOf`), and the sampler outputs the `|i|`-bit numeral of a
unit `v < N` (`unitSampleStr`, `sampleUnitL_spec`, or the fallback `1 % N = 1`), which
`rabinDec` decodes to `ZMod.unitOfCoprime v` with `rabinEnc` the same numeral; `rabinEval_spec`
gives the evaluator clause.

**Proof sketch.** As `rsaSampler_spec`: unfold the activation
(`NUPPT.runAtL_ofPolyTimeUniform`, `rabinSampleRaw`), case on `sampleUnitL`, discharge
`rabinDec`'s test by `length_natToList`, `listToNat_natToList`, `sampleUnitL_spec` /
`Nat.coprime_one_left`, and read the value back (`ZMod.coe_unitOfCoprime`, `ZMod.val_natCast`). -/
theorem rabinSampler_spec (H : ArithmeticFP) (n : ℕ) (r : (oddGen H).Coins n)
    (s : (rabinSampler H).Coins n) :
    ∃ x, rabinDec (pairFstD ((oddGen H).runAt n [] r))
        ((rabinSampler H).runAt n (pairFstD ((oddGen H).runAt n [] r)) s) = some x ∧
      rabinEval (pairEncode (pairFstD ((oddGen H).runAt n [] r))
        ((rabinSampler H).runAt n (pairFstD ((oddGen H).runAt n [] r)) s)) = rabinF _ x := by
  sorry

/-- **The Rabin collection** [PS10, Theorem 61.7]: indices `N = pq` (distinct odd primes),
domains `Z_N^*`, `f_N(x) = x² mod N`, generator `oddGen`, sampler `rabinSampler`, evaluator
`rabinEval`.

**Deviation:** module docstring (odd distinct primes, truncated samplers, `max n 3`);
"`Z_n^*`" of the text read as `Z_N^*`. -/
noncomputable def rabinCollection (H : ArithmeticFP) : Collection where
  D i := (ZMod (rabinMod i))ˣ
  encD := rabinEnc
  decD := rabinDec
  decD_encD := rabinDec_rabinEnc
  f := rabinF
  gen := oddGen H
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  sample := rabinSampler H
  sample_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  eval := rabinEval
  eval_poly := polyTimeComputable_rabinEval H
  eval_spec := rabinEval_spec
  sample_spec := rabinSampler_spec H

/-- The index generated by the Rabin collection is the numeral of `N`. -/
theorem rabinCollection_index (H : ArithmeticFP) (n : ℕ) (r : (rabinCollection H).gen.Coins n) :
    (rabinCollection H).index n r = rabinIndexOf _ (rabinGenParams (· ≠ 2) oddDefault n (List.ofFn r)) := by
  show pairFstD ((oddGen H).runAt n [] r) = _
  rw [oddGen_runAt, rabinGenOut, pairFstD_pairEncode]

/-- The statistical error of the Rabin reductions at parameter `n`: two restricted prime
samplers and the unit sampler of `rabinFactorer`, the latter counted twice because it enters
through the factor `2` of the symmetry lemma (`e^{-n}` each: `4e^{-n}`), and the diagonal
`p = q` of the restricted class: `1/(P − 1) ≤ 2/P ≤ 4n/2^n` for the `P = |Π_n| − 1 ≥ 2` odd
primes (`one_div_card_primes_le`) and `1/B ≤ 4n/2^n` for the `B` Blum primes (`BlumDensity`).

Repair (run-3 audit P7-3): the diagonal term was `2n/2^n`, which neither the Chebyshev bound
`2^n ≤ 2n|Π_n|` (odd class: `1/(|Π_n| − 1)`) nor `BlumDensity` (`1/B`) yields; both give
`4n/2^n`. -/
noncomputable def rabinErr (n : ℕ) : ℝ := 4 * Real.exp (-(n : ℝ)) + 4 * n / 2 ^ n

/-- `rabinErr` is negligible (`exp_neg_le_half_pow`, `negligible_two_pow_neg`,
`Negligible.const_mul`, `Negligible.mul_pow`, `Negligible.add`). -/
theorem negligible_rabinErr : Negligible rabinErr := by
  have h1 : Negligible fun n : ℕ => (1 / 2 : ℝ) ^ n := by
    simpa [one_div] using negligible_two_pow_neg
  have h4 : Negligible fun n : ℕ => Real.exp (-(n : ℝ)) :=
    h1.mono ⟨0, fun n _ => by
      rw [abs_of_pos (Real.exp_pos _), abs_of_pos (by positivity)]
      exact exp_neg_le_half_pow n⟩
  refine ((h4.const_mul 4).add ((h1.mul_pow 1).const_mul 4)).mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  unfold rabinErr
  rw [pow_one, one_div, inv_pow]
  field_simp

/-- **The domain sampler of the Rabin collection is close to uniform** [PS10, Theorem 61.7]:
as `rsaCollection_sampleClose` (`δ n := 1` for `n < 3`, `e^{-n}` otherwise) at the index
`N = pq` with `N < 2^{2n}` (`rabinCollection_index`, `listToNat_rabinIndexOf`), decoding by
`rabinDec`. -/
theorem rabinCollection_sampleClose (H : ArithmeticFP) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ (rabinCollection H).SampleClose δ := by
  sorry

/-! ## The factoring adversary `A'` [PS10, Algorithm 62.9] -/

/-- **The computation of `A'(N)`** [PS10, Algorithm 62.9] after `x ← Z_N^*` and
`z ← A(N, x² mod N)`: abort (output `[]`) unless `z² ≡ x² (mod N)`; else output
`gcd((x − z) mod N, N)` as an `n`-bit numeral (the answer format of Assumption 30.1). -/
def rabinFactorStep (n N x : ℕ) (zs : List Bool) : List Bool :=
  if listToNat zs ^ 2 % N = x ^ 2 % N then
    natToList n (Nat.gcd ((x : ZMod N) - (listToNat zs : ZMod N)).val N)
  else []

/-- The string function of `A'` on the raw layout `⟨⟨⟨1^n, N⟩, α⟩, r⟩`: `x` from the first
`T(n) B(n)` coins by `unitSampleStr`, `y := x² mod N`, the call `A(1^n, ⟨N, y⟩)` on the
remaining coins with the advice of `A`, then `rabinFactorStep`. -/
def rabinFactorRaw (A : NUPPT) (z : List Bool) : List Bool :=
  rabinFactorStep (NUPPT.inParam z).length (listToNat (NUPPT.inArg z))
    (listToNat (unitSampleStr (NUPPT.inArg z) (NUPPT.inParam z).length
      ((NUPPT.inCoins z).take (rsaSampleCoins.eval (NUPPT.inParam z).length))))
    (A.output (NUPPT.layout (NUPPT.inParam z)
      (pairEncode (NUPPT.inArg z) (natToList (NUPPT.inArg z).length
        (listToNat (unitSampleStr (NUPPT.inArg z) (NUPPT.inParam z).length
          ((NUPPT.inCoins z).take (rsaSampleCoins.eval (NUPPT.inParam z).length))) ^ 2 %
          listToNat (NUPPT.inArg z))))
      (NUPPT.inAdvice z) ((NUPPT.inCoins z).drop (rsaSampleCoins.eval (NUPPT.inParam z).length))))

/-- **`A'` is polynomial-time** [PS10, Theorem 61.8 ⇒].

**Proof sketch.** Cut the coins at `1^{T(n) B(n)}` (`polyTimeComputable_pairTakePoly`/
`_pairDropPoly rsaSampleCoins`); `x` by `polyTimeComputable_unitSampleStr`; `y` by
`H.modExp` with the exponent `[true, false]`; the call by `A.polyTimeComputable_output` on
`NUPPT.polyTimeComputable_layout`; the test `z² ≡ y` by `H.modExp` and
`polyTimeComputable_pairEq`; `(x − z) mod N = (x + (N ∸ (z mod N))) mod N` by `H.divMod`,
`H.sub`, `H.add` and `H.divMod` (run-3 audit P7-1); the gcd is the first component of
`xgcdStr` (`H.xgcd`); the width `n` by `polyTimeComputable_pairTakePoly var`. -/
theorem polyTimeComputable_rabinFactorRaw (H : ArithmeticFP) (A : NUPPT) :
    PolyTimeComputable (rabinFactorRaw A) := by
  sorry

/-- **The factoring adversary `A'`** [PS10, Algorithm 62.9] as a non-uniform PPT: coins
`T(n) B(n)` (for `x`) plus the coins of `A`, advice of `A`. -/
noncomputable def rabinFactorer (H : ArithmeticFP) (A : NUPPT) : NUPPT :=
  NUPPT.ofPolyTime (polyTimeComputable_rabinFactorRaw H A) (.add rsaSampleCoins A.coins)
    A.adv A.advice A.advice_length

/-- The activation of `A'` on the numeral `N` with coins `r`. -/
theorem rabinFactorer_runAt (H : ArithmeticFP) (A : NUPPT) (n : ℕ) (N : List Bool)
    (r : (rabinFactorer H A).Coins n) :
    (rabinFactorer H A).runAt n N r =
      rabinFactorStep n (listToNat N)
        (listToNat (unitSampleStr N n ((List.ofFn r).take (rsaSampleCoins.eval n))))
        (A.runAtL n (pairEncode N (natToList N.length
          (listToNat (unitSampleStr N n ((List.ofFn r).take (rsaSampleCoins.eval n))) ^ 2 % listToNat N)))
          ((List.ofFn r).drop (rsaSampleCoins.eval n))) := by
  rw [NUPPT.runAt_eq]
  unfold rabinFactorer
  rw [NUPPT.runAtL_ofPolyTime]
  simp [rabinFactorRaw, NUPPT.runAtL, NUPPT.layout, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice,
    NUPPT.inCoins, NUPPT.advInput]

/-- **Inverting the Rabin collection factors** [PS10, Theorem 61.8 ⇒, Algorithm 62.9]: for
`n ≥ 3`, the inversion probability of `A` against the Rabin collection is at most twice the
factoring probability of `A'` on odd moduli plus the statistical error.

**Proof sketch.** At a generated index `N = pq` (`rabinCollection_index`), the domain is
`Z_N^*` and `f_N(x)` is the numeral of `(x²).val` (`val_units_pow`), so the event is "`A`
decodes to a root of `x²`". With `Z(y, r) := rabinDec N (A(1^n, ⟨N, y⟩; r))`, the
symmetry lemma `rabin_symmetry` (odd `p ≠ q`) shows that with probability at least half of it the
root `z` differs from `±x`, and then `gcd((x − z).val, N) ∈ {p, q}`
(`NumberTheory.gcd_sub_eq_prime_of_sq_eq_sq`), which `rabinFactorStep` outputs as an
`n`-bit numeral (`rabinFactorer_runAt`, `NUPPT.inverter_eq_some_iff`, `natToBits_bitsToNat`).
The unit `x` of `A'` is sampled by `unitSampleStr` within `e^{-n}` of uniform
(`statClose_rejectBlocksL`, as in `rsaCollection_sampleClose`; `StatClose.abs_uprob_sub_le_prod`),
paid twice through the factor `2` of the symmetry step, and the law of `N` under `oddGen` is
within `2e^{-n} + 4n/2^n` of the uniform *distinct* odd pair: each restricted sampler is
`statClose_rejectBlocksL` with the fallback prime of `oddDefault` and the odd-prime density
`(|Π_n| − 1)/2^n ≥ 1/(4n)` for `n ≥ 3` (`two_pow_le_two_mul_card_primes`), `4n²` trials
(`one_sub_one_div_pow_le_exp_neg`), then `StatClose.prod` and `StatClose.map` through the
validity test, whose pushforward of the uniform odd pair differs from the uniform distinct odd
pair by the diagonal `uprob_diag` on the restricted class, `1/(P − 1) ≤ 2/P` (`P ≥ 2`) with
`one_div_card_primes_le` (run-3 audit P7-3); `uexp_prod`/`uprob_prod` reorganize the coins
(total `rabinErr n`). -/
theorem rabinCollection_invProbAt_le (H : ArithmeticFP) (A : NUPPT) {n : ℕ} (hn : 3 ≤ n) :
    (rabinCollection H).invProbAt A n ≤ 2 * oddFactorProb (rabinFactorer H A) n + rabinErr n := by
  sorry

/-- **Theorem 61.7 / Theorem 61.8 (⇒)** [PS10, Theorems 61.7 and 61.8]: under the factoring
assumption (and the arithmetic hypotheses), the Rabin collection `{f_N(x) = x² mod N}` is a
collection of one-way functions.

**Deviation:** indices with distinct odd primes; the factoring assumption on `DistinctPrimes`
is transferred by `oddFactorProb_le`.

**Proof sketch.** Sampling: `rabinCollection_sampleClose H`. Hardness: for `n ≥ 6`,
`rabinCollection_invProbAt_le` and `oddFactorProb_le` give
`invProbAt ≤ 4 · factorProb (rabinFactorer H A) n + rabinErr n`, negligible by
`hF (rabinFactorer H A)`, `Negligible.const_mul`, `negligible_rabinErr`, `Negligible.add`;
conclude by `Negligible.mono` (`Collection.invProbAt_nonneg`). -/
theorem rabinCollection_oneWay (H : ArithmeticFP) (hF : FactoringAssumption) :
    (rabinCollection H).OneWay := by
  sorry

/-! ## The Rabin trapdoor collection on Blum integers [PS10, Theorem 63.10] -/

/-- A string index is a *valid Blum index* when it reads as `N = pq` with `p ≠ q` primes
`≡ 3 (mod 4)` (decidable by bounded search; the generator only outputs such indices). -/
def BlumValid (i : List Bool) : Prop :=
  ∃ p ∈ Finset.range (listToNat i), ∃ q ∈ Finset.range (listToNat i),
    p.Prime ∧ q.Prime ∧ p ≠ q ∧ p % 4 = 3 ∧ q % 4 = 3 ∧ listToNat i = p * q

instance : DecidablePred BlumValid := fun i => by unfold BlumValid; infer_instance

/-- The modulus of the domain at a Blum index: `N` for a valid index, `1` otherwise. -/
def blumMod (i : List Bool) : ℕ := if BlumValid i then listToNat i else 1

instance (i : List Bool) : NeZero (blumMod i) := by
  unfold blumMod
  split_ifs with h
  · obtain ⟨p, hp, q, hq, hpp, hqp, -, -, -, hN⟩ := h
    exact ⟨by rw [hN]; exact mul_ne_zero hpp.ne_zero hqp.ne_zero⟩
  · exact ⟨one_ne_zero⟩

/-- `blumMod` of a valid index is `N`. -/
theorem blumMod_of_valid {i : List Bool} (h : BlumValid i) : blumMod i = listToNat i := if_pos h

/-- `blumMod` of an invalid index is `1`. -/
theorem blumMod_of_not_valid {i : List Bool} (h : ¬ BlumValid i) : blumMod i = 1 := if_neg h

/-- `blumMod i ≤ 2^{|i|}`. -/
theorem blumMod_le (i : List Bool) : blumMod i ≤ 2 ^ i.length := by
  unfold blumMod
  split_ifs
  · exact (listToNat_lt_two_pow _).le
  · exact Nat.one_le_two_pow

/-- A valid Blum index has a Blum factorization. -/
theorem BlumValid.exists_mul {i : List Bool} (h : BlumValid i) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p % 4 = 3 ∧ q % 4 = 3 ∧ blumMod i = p * q := by
  have hM := blumMod_of_valid h
  obtain ⟨p, -, q, -, hp, hq, hpq, hp3, hq3, hN⟩ := h
  exact ⟨p, q, hp, hq, hpq, hp3, hq3, by rw [hM, hN]⟩

/-- **Squaring is a permutation of `QR_M`** for every Blum modulus `M = pq`
(`NumberTheory.sqTo_bijective_of_blum` transported along `M = pq`). -/
theorem sqTo_bijective_of_exists (M : ℕ) [NeZero M]
    (h : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p % 4 = 3 ∧ q % 4 = 3 ∧ M = p * q) :
    Function.Bijective (fun x : QR M => sqTo M (x : (ZMod M)ˣ)) := by
  obtain ⟨p, q, hp, hq, hpq, hp3, hq3, rfl⟩ := h
  haveI := Fact.mk hp
  haveI := Fact.mk hq
  exact sqTo_bijective_of_blum (coprime_of_ne hpq) hp3 hq3

/-- The number encoding an element of `QR_N`: its residue for a valid index, the canonical
`1 mod N` for the one-element domain of an invalid index. -/
def blumEncVal (i : List Bool) (x : QR (blumMod i)) : ℕ :=
  if BlumValid i then ((x : (ZMod (blumMod i))ˣ) : ZMod (blumMod i)).val else 1 % listToNat i

/-- The string encoding of an element of `D_N = QR_N`. -/
def blumEnc (i : List Bool) (x : QR (blumMod i)) : List Bool := natToList i.length (blumEncVal i x)

/-- The decoder of `QR_N`: for a valid index, a numeral of the right width reading as a unit
below `N` that is a quadratic residue (`QR` membership is decidable); for an invalid index,
the canonical string of the one-element domain. -/
def blumDec (i : List Bool) (w : List Bool) : Option (QR (blumMod i)) :=
  if BlumValid i then
    if h : w.length = i.length ∧ listToNat w < blumMod i ∧ Nat.Coprime (listToNat w) (blumMod i) then
      if hq : ZMod.unitOfCoprime (listToNat w) h.2.2 ∈ QR (blumMod i) then some ⟨_, hq⟩ else none
    else none
  else if w = natToList i.length (1 % listToNat i) then some 1 else none

/-- The residue of an element of `QR_N` fits in the width of the index. -/
theorem blum_val_lt_two_pow (i : List Bool) (x : QR (blumMod i)) :
    ((x : (ZMod (blumMod i))ˣ) : ZMod (blumMod i)).val < 2 ^ i.length :=
  lt_of_lt_of_le (ZMod.val_lt _) (blumMod_le i)

/-- **Decoding inverts encoding on `QR_N`** (as `rsaDec_rsaEnc`, with the residue test
discharged by `x.2`). -/
theorem blumDec_blumEnc (i : List Bool) (x : QR (blumMod i)) : blumDec i (blumEnc i x) = some x := by
  by_cases hv : BlumValid i
  · have hl : listToNat (blumEnc i x) = ((x : (ZMod (blumMod i))ˣ) : ZMod (blumMod i)).val := by
      simp only [blumEnc, blumEncVal, if_pos hv]
      exact listToNat_natToList (blum_val_lt_two_pow i x)
    have hu : ZMod.unitOfCoprime (listToNat (blumEnc i x))
        (by rw [hl]; exact ZMod.val_coe_unit_coprime _) = (x : (ZMod (blumMod i))ˣ) := by
      ext
      simp [ZMod.coe_unitOfCoprime, hl]
    have hmem : ZMod.unitOfCoprime (listToNat (blumEnc i x))
        (by rw [hl]; exact ZMod.val_coe_unit_coprime _) ∈ QR (blumMod i) := by
      rw [hu]; exact x.2
    rw [blumDec, if_pos hv, dif_pos ⟨by simp [blumEnc], by rw [hl]; exact ZMod.val_lt _,
      by rw [hl]; exact ZMod.val_coe_unit_coprime _⟩, dif_pos hmem]
    congr 1
    exact Subtype.ext hu
  · haveI : Subsingleton (ZMod (blumMod i)) := ZMod.subsingleton_iff.2 (blumMod_of_not_valid hv)
    rw [blumDec, if_neg hv, if_pos (by simp [blumEnc, blumEncVal, if_neg hv])]
    congr 1
    exact Subtype.ext (Units.ext (Subsingleton.elim _ _))

/-- `f_N(x) = x² mod N` on the encoded residue, mirroring the evaluator [PS10, Theorem 63.10]. -/
def blumF (i : List Bool) (x : QR (blumMod i)) : List Bool :=
  natToList i.length (listToNat (blumEnc i x) ^ 2 % listToNat i)

/-- The evaluator `rabinEval` computes `blumF` on encoded residues. -/
theorem blumEval_spec (i : List Bool) (x : QR (blumMod i)) :
    rabinEval (pairEncode i (blumEnc i x)) = blumF i x := by
  simp [rabinEval, blumF, listToNat]

/-- The permutation of `D_N = QR_N`: squaring [PS10, Theorem 63.10 (1), Claim-63.1] for a
valid Blum index, the identity of the one-element domain otherwise. -/
noncomputable def blumPermAt (i : List Bool) : QR (blumMod i) ≃ QR (blumMod i) :=
  if hv : BlumValid i then
    Equiv.ofBijective (fun x : QR (blumMod i) => sqTo (blumMod i) (x : (ZMod (blumMod i))ˣ))
      (sqTo_bijective_of_exists _ hv.exists_mul)
  else Equiv.refl _

/-- **`f_N` is the encoded permutation** at every index (the clause `f_perm`): as `rsaF_perm`
with `e = 2`. -/
theorem blumF_perm (i : List Bool) (x : QR (blumMod i)) : blumF i x = blumEnc i (blumPermAt i x) := by
  rcases Nat.eq_zero_or_pos i.length with hl | hl
  · simp [blumF, blumEnc, hl, natToList_zero]
  by_cases hv : BlumValid i
  · have hM := blumMod_of_valid hv
    simp only [blumF, blumEnc, blumEncVal, if_pos hv, blumPermAt, dif_pos hv, Equiv.ofBijective_apply,
      coe_sqTo, listToNat_natToList (blum_val_lt_two_pow i x), val_units_pow]
    congr 1
    exact congrArg (fun M => ((x : (ZMod (blumMod i))ˣ) : ZMod (blumMod i)).val ^ 2 % M) hM.symm
  · have h1 : 1 % listToNat i < 2 ^ i.length :=
      lt_of_le_of_lt (Nat.mod_le _ _) (Nat.one_lt_two_pow hl.ne')
    simp only [blumF, blumEnc, blumEncVal, if_neg hv, blumPermAt, dif_neg hv, Equiv.refl_apply,
      listToNat_natToList h1]
    congr 1
    rcases Nat.lt_or_ge (listToNat i) 2 with h2 | h2
    · interval_cases (listToNat i)
      · simp
      · simp
    · rw [Nat.mod_eq_of_lt (by omega : 1 < listToNat i), one_pow,
        Nat.mod_eq_of_lt (by omega : 1 < listToNat i)]

/-- The string function of the `QR_N` sampler on the raw layout `⟨⟨⟨1^n, N⟩, α⟩, r⟩`: the
square of a rejection-sampled unit [PS10, Theorem 63.10 (3)]; `4`-to-`1` maps push uniform
to uniform (`NumberTheory.pushesUniform_sqTo`, C5). -/
def blumSampleRaw (z : List Bool) : List Bool :=
  modExpStr (pairEncode (unitSampleStr (NUPPT.inArg z) (NUPPT.inParam z).length (NUPPT.inCoins z))
    (pairEncode [true, false] (NUPPT.inArg z)))

/-- The `QR_N` sampler is polynomial-time (`polyTimeComputable_unitSampleStr`, `H.modExp`). -/
theorem polyTimeComputable_blumSampleRaw (H : ArithmeticFP) : PolyTimeComputable blumSampleRaw :=
  H.modExp.comp ((polyTimeComputable_unitSampleStr H NUPPT.polyTimeComputable_inArg).pairEncode
    ((polyTimeComputable_const [true, false]).pairEncode NUPPT.polyTimeComputable_inArg))

/-- **The domain sampler of the Blum Rabin collection** as a uniform `NUPPT`. -/
noncomputable def blumSampler (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_blumSampleRaw H) rsaSampleCoins

/-- **The CRT root formula** [PS10, Theorems 58.2 and 58.3, Algorithm 60.4 "`C⁻¹`"]: the
residue root of `y` modulo a Blum integer `pq`, `(a · q · (q⁻¹ mod p) + b · p · (p⁻¹ mod q)) mod pq`
with `a = y^{(p+1)/4} mod p` and `b = y^{(q+1)/4} mod q`; equals `NumberTheory.blumSqrt`. -/
def blumInvNat (p q y : ℕ) : ℕ :=
  (y ^ (p / 4 + 1) % p * (q * ((q : ZMod p)⁻¹).val) + y ^ (q / 4 + 1) % q * (p * ((p : ZMod q)⁻¹).val)) %
    (p * q)

/-- The string function of the trapdoor inverter on the raw layout
`⟨⟨⟨1^n, ⟨⟨p, q⟩, y⟩⟩, α⟩, r⟩`: `blumInvNat p q y` as a numeral of the width of `y`. -/
def blumInvRaw (z : List Bool) : List Bool :=
  natToList (pairSndD (NUPPT.inArg z)).length
    (blumInvNat (listToNat (pairFstD (pairFstD (NUPPT.inArg z))))
      (listToNat (pairSndD (pairFstD (NUPPT.inArg z)))) (listToNat (pairSndD (NUPPT.inArg z))))

/-- **The inverter is polynomial-time** [PS10, Theorem 63.10 (6)]: two `H.modExp` calls with
the exponents `p/4 + 1`, `q/4 + 1` (`H.divMod`, then `H.add` with `[true]`), the CRT
coefficients by `H.xgcd` and `H.mul`, the sum by `H.add` (run-3 audit P7-1) and a final
`H.divMod`. -/
theorem polyTimeComputable_blumInvRaw (H : ArithmeticFP) : PolyTimeComputable blumInvRaw := by
  sorry

/-- **The trapdoor inverter** `Inv(1^n, ⟨⟨p, q⟩, y⟩)` as a uniform `NUPPT` without coins. -/
noncomputable def blumInv (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_blumInvRaw H) (.const 0)

/-- **The inverter decodes to the residue root** at every generated Blum index (the clause
`inv_spec` of `TrapdoorCollection`, [PS10, Theorem 63.10 (6)]).

**Proof sketch.** By `blumGen_runAt` the index is the numeral of `N = pq` and the trapdoor
`⟨p, q⟩` (`encodeDistinctPrimes`), with `p ≠ q` Blum primes (`rabinGenParams`), so the index
is `BlumValid`; `blumEnc i y` is the numeral of `y.val`. The inverter returns the numeral of
`blumInvNat p q y.val`, which equals `(blumSqrt y).val`: the CRT formula `s` satisfies
`s ≡ y^{(p+1)/4} (mod p)` and `s ≡ y^{(q+1)/4} (mod q)` (`ZMod.coe_mul_inv_eq_one`,
`crtUnits_fst`/`crtUnits_snd`), hence `s = crtUnits⁻¹(a, b)` by injectivity of `crtUnits`
(`ZMod.chineseRemainder`); `blumSqrt_mem_QR` puts it in `QR_N`, so `blumDec` decodes it
(`blumDec_blumEnc`), and `(blumPermAt i).symm y = blumSqrt y` by `eq_blumSqrt_of_sq_eq`
(`Equiv.ofBijective_symm_apply_apply`). -/
theorem blumInv_spec (H : ArithmeticFP) (n : ℕ) (r : (blumGen H).Coins n)
    (y : QR (blumMod (pairFstD ((blumGen H).runAt n [] r)))) (s : (blumInv H).Coins n) :
    blumDec _ ((blumInv H).runAt n (pairEncode (pairSndD ((blumGen H).runAt n [] r)) (blumEnc _ y)) s) =
      some ((blumPermAt _).symm y) := by
  sorry

/-- **The `QR_N` sampler's outputs decode and evaluate honestly** (the clause `sample_spec` of
`Collection`, [PS10, Definition 41.1 (2), Theorem 63.10 (3)]; repair of the run-3 audit,
P3-1): at every parameter the generated index is a valid Blum index (`blumGen_runAt`,
`rabinGenParams`, `BlumValid`), and the sampler outputs the `|i|`-bit numeral of `u² mod N` for
a unit `u < N` (`blumSampleRaw`, `modExpStr_pairEncode`, `unitSampleStr`, `sampleUnitL_spec`),
a unit residue (`Nat.Coprime.pow_left`, `sq_mem_QR`), which `blumDec` decodes to that residue
with `blumEnc` the same numeral; `blumEval_spec` gives the evaluator clause.

**Proof sketch.** Unfold the activation (`NUPPT.runAtL_ofPolyTimeUniform`), then the
computation above with `blumDec`'s tests (`length_natToList`, `listToNat_natToList`,
`Nat.mod_lt`, `ZMod.coe_unitOfCoprime`, `ZMod.val_natCast`). -/
theorem blumSampler_spec (H : ArithmeticFP) (n : ℕ) (r : (blumGen H).Coins n)
    (s : (blumSampler H).Coins n) :
    ∃ x, blumDec (pairFstD ((blumGen H).runAt n [] r))
        ((blumSampler H).runAt n (pairFstD ((blumGen H).runAt n [] r)) s) = some x ∧
      rabinEval (pairEncode (pairFstD ((blumGen H).runAt n [] r))
        ((blumSampler H).runAt n (pairFstD ((blumGen H).runAt n [] r)) s)) = blumF _ x := by
  sorry

/-- **The Rabin collection of trapdoor permutations on Blum integers** [PS10, Theorem 63.10]:
indices `N = pq` with `p ≡ q ≡ 3 (mod 4)`, domains `D_N = R_N = QR_N`,
`Gen(1^n) = ⟨N, ⟨p, q⟩⟩`, `f_N(x) = x² mod N`, `f⁻¹_{p,q}(y)` the unique residue root
(`blumPermAt`, `blumInv`).

**Deviation:** module docstring (Blum primes, valid/invalid indices, `max n 3`). -/
noncomputable def rabinBlumTrapdoor (H : ArithmeticFP) : TrapdoorCollection where
  D i := QR (blumMod i)
  inhabitedD _ := ⟨1⟩
  encD := blumEnc
  decD := blumDec
  decD_encD := blumDec_blumEnc
  f := blumF
  gen := blumGen H
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  sample := blumSampler H
  sample_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  eval := rabinEval
  eval_poly := polyTimeComputable_rabinEval H
  eval_spec := blumEval_spec
  sample_spec := blumSampler_spec H
  perm := blumPermAt
  f_perm := blumF_perm
  inv := blumInv H
  inv_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  inv_spec := blumInv_spec H

/-- The index generated by the Blum Rabin collection is the numeral of `N`. -/
theorem rabinBlumTrapdoor_index (H : ArithmeticFP) (n : ℕ) (r : (rabinBlumTrapdoor H).gen.Coins n) :
    (rabinBlumTrapdoor H).index n r =
      rabinIndexOf _ (rabinGenParams (· % 4 = 3) blumDefault n (List.ofFn r)) := by
  show pairFstD ((blumGen H).runAt n [] r) = _
  rw [blumGen_runAt, rabinGenOut, pairFstD_pairEncode]

/-- **The `QR_N` sampler is close to uniform** [PS10, Theorem 63.10 (3)]: the square of a
unit within `e^{-n}` of uniform (`rsaCollection_sampleClose`'s argument) is within `e^{-n}`
of a uniform residue (`NumberTheory.pushesUniform_sqTo`, `statClose_of_pushesUniform`,
`StatClose.map`, `StatClose.trans`); decoding by `blumDec` (`sq_mem_QR`). -/
theorem rabinBlumTrapdoor_sampleClose (H : ArithmeticFP) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ (rabinBlumTrapdoor H).toCollection.SampleClose δ := by
  sorry

/-- **Inverting the Blum Rabin collection factors** [PS10, Theorem 63.10 (5), via
Algorithm 62.9]: for `n ≥ 3` and under the density hypothesis, the inversion probability of
`A` against `rabinBlumTrapdoor` is at most twice the Blum factoring probability of `A'`
plus the statistical error.

**Proof sketch.** As `rabinCollection_invProbAt_le`: the ideal `x ← QR_N` gives `y = x²`
uniform on `QR_N` (squaring is a bijection of `QR_N`, `blumPermAt`), and the reduction's
`y = r²` for a uniform unit `r` has the same law (`pushesUniform_sqTo`); the answer `z` of
`A` decodes to a residue root of `y`, and `rabin_symmetry` (with `Z` the decoded answer,
coerced to `Z_N^*`) gives `z ∉ {±r}` half the time, hence a factor by
`gcd_sub_eq_prime_of_sq_eq_sq`. The law of `N` under `blumGen` is within `2e^{-n} + 4n/2^n`
of the uniform distinct Blum pair by `statClose_rejectBlocksL` with the fallback prime of
`blumDefault` and the density `hD` (acceptance `≥ 1/(4n)` per trial, `4n²` trials,
`one_sub_one_div_pow_le_exp_neg`), `StatClose.prod`, `StatClose.map` through the validity test
and the diagonal `1/B ≤ 4n/2^n` from `hD` (`uprob_diag`; run-3 audit P7-3); the unit sampler's
`e^{-n}` is paid twice (total `rabinErr n`). -/
theorem rabinBlumTrapdoor_invProbAt_le (H : ArithmeticFP) (hD : BlumDensity) (A : NUPPT) {n : ℕ}
    (hn : 3 ≤ n) :
    (rabinBlumTrapdoor H).toCollection.invProbAt A n ≤
      2 * blumFactorProb (rabinFactorer H A) n + rabinErr n := by
  sorry

/-- **Theorem 63.10** [PS10, Theorem 63.10]: under the factoring assumption, the density of
Blum primes and the arithmetic hypotheses, the Rabin collection on Blum integers with domain
`QR_N` is a collection of trapdoor permutations: clauses (1)–(4) and (6) are the data of
`rabinBlumTrapdoor` (`blumPermAt` [Claim-63.1], `blumGen`, `blumSampler`, `rabinEval`,
`blumInv_spec`), and the hardness clause (5) follows from
`rabinBlumTrapdoor_invProbAt_le`, `blumFactoring_of_factoring hD hF`, `negligible_rabinErr`
and `Negligible.mono` (sampling: `rabinBlumTrapdoor_sampleClose`).

**Deviation:** factoring assumption restricted to Blum moduli through the density hypothesis. -/
theorem rabinBlumTrapdoor_oneWay (H : ArithmeticFP) (hD : BlumDensity) (hF : FactoringAssumption) :
    (rabinBlumTrapdoor H).OneWay := by
  sorry

/-! ## Theorem 61.8 (⇐): Rabin one-way implies factoring (Blum moduli) -/

/-- **The root finder from a factorer** [PS10, proof of Theorem 61.8, "only if" direction]:
`A'(N, y)`: `p' ← A(N)`, `q' := N / p'`, abort unless `p' q' = N`, else output the CRT root
`blumInvNat p' q' y` as a numeral of the width of `y`. -/
def rabinRootStep (s : List Bool) (N : ℕ) (y : List Bool) : List Bool :=
  if listToNat s * (N / listToNat s) = N then
    natToList y.length (blumInvNat (listToNat s) (N / listToNat s) (listToNat y))
  else []

/-- The string function of the root finder on the raw layout `⟨⟨⟨1^n, ⟨N, y⟩⟩, α⟩, r⟩`: run
`A` on `⟨⟨⟨1^n, N⟩, α⟩, r⟩` and apply `rabinRootStep`. -/
def rabinRootRaw (A : NUPPT) (z : List Bool) : List Bool :=
  rabinRootStep (A.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z))
      (NUPPT.inAdvice z) (NUPPT.inCoins z)))
    (listToNat (pairFstD (NUPPT.inArg z))) (pairSndD (NUPPT.inArg z))

/-- **The root finder is polynomial-time**: `A.polyTimeComputable_output` on the re-paired
layout, `H.divMod`, `H.mul`, `polyTimeComputable_pairEq`, `polyTimeComputable_ite`, and the
CRT formula as in `polyTimeComputable_blumInvRaw`. -/
theorem polyTimeComputable_rabinRootRaw (H : ArithmeticFP) (A : NUPPT) :
    PolyTimeComputable (rabinRootRaw A) := by
  sorry

/-- **The inverter of the Blum Rabin collection built from a factorer** `A` (coins and advice
of `A`) [PS10, Theorem 61.8 ⇐]. -/
noncomputable def rabinBlumInverter (H : ArithmeticFP) (A : NUPPT) : NUPPT :=
  NUPPT.ofPolyTime (polyTimeComputable_rabinRootRaw H A) A.coins A.adv A.advice A.advice_length

/-- The activation of the root finder: `A'(1^n, ⟨N, y⟩; r) = rabinRootStep (A(1^n, N; r)) N y`. -/
theorem rabinBlumInverter_runAt (H : ArithmeticFP) (A : NUPPT) (n : ℕ) (N y : List Bool)
    (r : (rabinBlumInverter H A).Coins n) :
    (rabinBlumInverter H A).runAt n (pairEncode N y) r = rabinRootStep (A.runAt n N r) (listToNat N) y := by
  rw [NUPPT.runAt_eq]
  unfold rabinBlumInverter
  rw [NUPPT.runAtL_ofPolyTime]
  simp [rabinRootRaw, NUPPT.runAt, NUPPT.layout, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice,
    NUPPT.inCoins, NUPPT.advInput]

/-- **A Blum factorer inverts the Blum Rabin collection** [PS10, proof of Theorem 61.8 ⇐,
"from the correct `p, q` we can compute the square root of `u` with probability 1"]: for
`n ≥ 3` and under the density hypothesis, `blumFactorProb A n` is at most the inversion
probability of `rabinBlumInverter A` plus the statistical error.

**Proof sketch.** When `A(1^n, N; r)` reads as `p` or `q`, `q' = N / p'` is the other prime
and `blumInvNat p' q' y.val = (blumSqrt y).val` (the CRT argument of `blumInv_spec`), the
residue root of `y`, which `blumDec` decodes and which is `(blumPermAt N).symm y`; hence
`A'` wins for every `y` (`rabinBlumInverter_runAt`, `uprob_mono`). The ideal uniform Blum
pair is within `2e^{-n} + 4n/2^n ≤ rabinErr n` of the generator's law
(`statClose_rejectBlocksL` with `hD`, the diagonal `1/B ≤ 4n/2^n` from `hD`,
`StatClose.abs_uprob_sub_le_prod`, `uexp_prod`; run-3 audit P7-3). -/
theorem blumFactorProb_le_invProbAt (H : ArithmeticFP) (hD : BlumDensity) (A : NUPPT) {n : ℕ}
    (hn : 3 ≤ n) :
    blumFactorProb A n ≤ (rabinBlumTrapdoor H).toCollection.invProbAt (rabinBlumInverter H A) n + rabinErr n := by
  sorry

/-- **Theorem 61.8 (⇐)** [PS10, Theorem 61.8, "only if"], Blum form: if the Blum Rabin
collection is one-way (and the density hypothesis holds) then factoring Blum integers is
hard.

**Deviation:** stated for Blum moduli (square roots modulo `p ≡ 1 (mod 4)` are not
formalized, text gap) and for the `QR_N`-domain collection of Theorem 63.10.

**Proof sketch.** For every `A`, `blumFactorProb_le_invProbAt` bounds `blumFactorProb A n`
by `invProbAt (rabinBlumInverter H A) n + rabinErr n`, negligible by `h.hard`,
`negligible_rabinErr`, `Negligible.add`; conclude by `Negligible.mono` (`uprob_nonneg`). -/
theorem blumFactoring_of_rabinBlum_oneWay (H : ArithmeticFP) (hD : BlumDensity)
    (h : (rabinBlumTrapdoor H).OneWay) : BlumFactoringAssumption := by
  sorry

end TCSlib.Cryptography.Candidates
