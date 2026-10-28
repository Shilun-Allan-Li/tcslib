/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Candidates.Arithmetic
import TCSlib.Cryptography.Candidates.Concrete
import TCSlib.Cryptography.Asymptotic.OneWay
import TCSlib.Cryptography.Asymptotic.Collections
import TCSlib.Cryptography.NumberTheory.Primality

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Factoring: `f_mult`, the factoring assumption, and the factoring-based candidates

The first candidate one-way function of [PS10, §2.3]: `f_mult(x, y) = 1` if `x = 1 ∨ y = 1`
and `x · y` otherwise [PS10, Definition 29.1], on pairs of `n`-bit numbers; the *factoring
assumption* [PS10, Assumption 30.1]; and the three theorems resting on it: `f_mult` is a weak
one-way function [PS10, Theorem 33.5] through the one-call reduction `A''` of
[PS10, Algorithm 33.6] and the unique-factorization step [PS10, Claim 34.1]; its direct
product with `4n³` blocks is strongly one-way [PS10, Theorem 36.3] through the
random-planting one-call reduction of [PS10, Algorithm 37.4] and [PS10, Claim 36.2]; and
the factoring collection `{(p, q) ↦ pq}` is a collection of one-way functions
[PS10, Theorem 51.1].

Every statement about machines is conditional on the arithmetic hypothesis bundle
`Candidates.ArithmeticFP` (plan decision "conditional candidates", D11): `f_mult` is easy to
compute, the collection's evaluator is multiplication and its sampler runs `SamplePrime`
with a primality test, all of which need binary arithmetic on tapes.

**Deviation:** Candidates: `A` receives `1^n` in Assumptions 30.1/52.2/53.1; `Π_n`
throughout; `p ≠ q` (odd / Blum) in RSA and Rabin; expected time replaced by strict PPT
with `2^{-n}` failure. Concretely: the factoring assumption draws a uniform pair of
*distinct* primes of `Π_n` (the restriction `p ≠ q` needed by RSA and Rabin, decision log
"Rabin/RSA scope"), hands `A` the input `⟨1^n, N⟩` with `N = pq` as a `2n`-bit numeral, and
reads its answer as an `n`-bit numeral (wrong length = failure, D5); the text's
"`Pr[…] < ε(n)` for a negligible `ε`" is "`Pr[…]` is negligible" (the convention of
`FunFamily.StrongOneWay`). The reductions of Theorems 33.5 and 36.3 are the one-call
variants without primality test (the text's own remarks, pp. 34 and 37); the planting
position of Algorithm 37.4 is uniform, sampled by rejection (D10). The collection of
Theorem 51.1 uses `Π_n` (the text's `D_i` has exactly-`i/2`-bit primes, source error 24),
pairs of distinct primes, and at the degenerate parameters `n < 2`, where `Π_n` has no two
distinct primes, the domain of `n = 2`.

## Main definitions

* `TCSlib.Cryptography.Candidates.fmultNat`, `TCSlib.Cryptography.Candidates.fmult` —
  `f_mult` [PS10, Definition 29.1] as a `FunFamily` (input and output length `2n`).
* `TCSlib.Cryptography.Candidates.modulusBits`, `factorProb`,
  `TCSlib.Cryptography.Candidates.FactoringAssumption` — [PS10, Assumption 30.1] (the
  distribution `DistinctPrimes` is in `Candidates.Concrete`).
* `TCSlib.Cryptography.Candidates.oneCallFactorer` — the one-call reduction `A''`
  [PS10, Algorithm 33.6]; `TCSlib.Cryptography.Candidates.plantFactor`,
  `prodInverter` — the random-planting reduction [PS10, Algorithm 37.4] at the concrete
  level; `fmultBlocks` — `m_n = 4n³`; `fmultWeakPoly` — `q(n) = 8(n+1)²`.
* `TCSlib.Cryptography.Candidates.factoringCollection`, `factoringGen`, `factoringSampler`,
  `samplePairOut`, `collectionFactorer` — the factoring collection [PS10, Theorem 51.1].

## Main results

* `TCSlib.Cryptography.Candidates.fmultNat_eq_mul_prime` [PS10, Claim 34.1],
  `fmult_inv_factor` — an inverse of `f_mult` at a product of primes is a factor.
* `TCSlib.Cryptography.Candidates.fmult_weakOneWay` [PS10, Theorem 33.5].
* `TCSlib.Cryptography.Candidates.fmult_prod_strongOneWay` [PS10, Theorem 36.3];
  `exists_plantFactorer` — the machine of [PS10, Algorithm 37.4].
* `TCSlib.Cryptography.Candidates.factoringCollection_oneWay` [PS10, Theorem 51.1].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.3: Definition 29.1, Assumption 30.1, Theorem 33.5, Algorithm 33.6, Claim 34.1;
  §2.4.2: Claim 36.2, Theorem 36.3, Algorithm 37.4; §2.7: Theorem 51.1.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.3 (`prodFun`, `yaoTry`: the concrete planting reduction).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory Finset

/-! ## The function `f_mult` [PS10, Definition 29.1] -/

/-- `f_mult(x, y) = 1` if `x = 1 ∨ y = 1`, and `x · y` otherwise [PS10, Definition 29.1]
(the special case makes `(1, xy)` never a preimage of `xy`, footnote 2 on p. 29). -/
def fmultNat (x y : ℕ) : ℕ := if x = 1 ∨ y = 1 then 1 else x * y

/-- `f_mult` of two `n`-bit numbers fits in `2n` bits. -/
theorem fmultNat_lt {n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n) : fmultNat x y < 2 ^ (2 * n) := by
  unfold fmultNat
  split_ifs with h1
  · have hn : n ≠ 0 := by
      rintro rfl
      simp only [pow_zero, Nat.lt_one_iff] at hx hy
      omega
    exact Nat.one_lt_two_pow (by omega)
  · rw [two_mul]
    exact mul_lt_two_pow_add hx hy

/-- **Claim 34.1** [PS10, Claim 34.1]: if `p, q` are primes and `f_mult(x', y') = pq` then
`x' ∈ {p, q}` (and `y'` is the other factor).

**Proof sketch.** `pq ≠ 1`, so `x' ≠ 1`, `y' ≠ 1` and `x' y' = pq`. A prime factor `r` of
`x'` (`Nat.exists_prime_and_dvd`) divides `pq`, so `r ∈ {p, q}` (`Nat.Prime.dvd_mul`,
`Nat.prime_dvd_prime_iff_eq`); if `r = p` then `x' = p s` with `s y' = q`, so `s ∈ {1, q}`
(`Nat.Prime.eq_one_or_self_of_dvd`), and `s = q` would force `y' = 1`; hence `x' = p`.
Symmetrically for `r = q`. -/
theorem fmultNat_eq_mul_prime {p q x y : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : fmultNat x y = p * q) : x = p ∨ x = q := by
  have hpq1 : p * q ≠ 1 := by
    intro h1
    exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right h1)
  unfold fmultNat at h
  split_ifs at h with h1
  · exact absurd h.symm hpq1
  push_neg at h1
  -- the key step: a prime `r` dividing `x`, with `r ∈ {p, q}`, and the cofactor analysis
  have key : ∀ {p q : ℕ}, p.Prime → q.Prime → x * y = p * q → p ∣ x → x = p := by
    intro p q hp hq h hpx
    obtain ⟨s, rfl⟩ := hpx
    have hsy : s * y = q := by
      have : p * (s * y) = p * q := by rw [← h]; ring
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
    rcases hq.eq_one_or_self_of_dvd s ⟨y, hsy.symm⟩ with hs | hs
    · rw [hs, mul_one]
    · exfalso
      apply h1.2
      rw [hs] at hsy
      have : q * y = q * 1 := by rw [hsy, mul_one]
      exact Nat.eq_of_mul_eq_mul_left hq.pos this
  obtain ⟨r, hr, hrx⟩ := Nat.exists_prime_and_dvd h1.1
  have hrpq : r ∣ p * q := hrx.trans (Dvd.intro y h)
  rcases (Nat.Prime.dvd_mul hr).mp hrpq with hrp | hrq
  · rw [(Nat.prime_dvd_prime_iff_eq hr hp).mp hrp] at hrx
    exact Or.inl (key hp hq h hrx)
  · rw [(Nat.prime_dvd_prime_iff_eq hr hq).mp hrq] at hrx
    exact Or.inr (key hq hp (by rw [h, mul_comm]) hrx)

/-- **`f_mult` as a function family** [PS10, Definition 29.1, §2.3]: at parameter `n` the
input is a `2n`-bit string `(x, y)` (two `n`-bit blocks, read as numbers) and the output is
`f_mult(x, y)` as a `2n`-bit numeral.

**Deviation:** the text's `f_mult : ℕ² → ℕ` "on inputs picked uniformly from `ℕ²`" is the
family of its restrictions to pairs of `n`-bit numbers, with input length `2n` (the proof
of Theorem 33.5 fixes the input length `2n`, `|x| = |y| = n`). -/
def fmult : FunFamily where
  inLen := .mul (.const 2) .var
  outLen := .mul (.const 2) .var
  f n x := natToBits (2 * n)
    (fmultNat (bitsToNat (FunFamily.blocks 2 n x 0)) (bitsToNat (FunFamily.blocks 2 n x 1)))

/-- The input length of `f_mult` at parameter `n` is `2n`. -/
@[simp] theorem fmult_inLen (n : ℕ) : fmult.inLen.eval n = 2 * n := rfl

/-- The output length of `f_mult` at parameter `n` is `2n`. -/
@[simp] theorem fmult_outLen (n : ℕ) : fmult.outLen.eval n = 2 * n := rfl

/-- Unfolding `f_mult` on a `2n`-bit string. -/
theorem fmult_f (n : ℕ) (x : Fin (2 * n) → Bool) :
    fmult.f n x = natToBits (2 * n)
      (fmultNat (bitsToNat (FunFamily.blocks 2 n x 0)) (bitsToNat (FunFamily.blocks 2 n x 1))) := rfl

/-- **An inverse of `f_mult` at a product of primes is a factor** [PS10, Claim 34.1, in the
form the reductions use]: if `f_mult(x') = pq` as `2n`-bit numerals, with `p, q < 2^n`
primes, then the first `n`-bit block of `x'` reads as `p` or as `q`.

Repair (run-3 audit P7-4): the former conclusion carried a dead middle disjunct
`bitsToNat (blocks 2 n x' 1) = q`, never produced by the proof and too weak for the reductions
(`A ∨ B ∨ C` does not give `A ∨ C`); it is now the two-way disjunction about block `0`.

**Proof sketch.** Both numerals encode numbers below `2^{2n}` (`fmultNat_lt`,
`mul_lt_two_pow_add`), so `f_mult(a, b) = pq` by `natToBits_injOn`; conclude by
`fmultNat_eq_mul_prime`. -/
theorem fmult_inv_factor {n p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpn : p < 2 ^ n)
    (hqn : q < 2 ^ n) (x' : Fin (2 * n) → Bool) (h : fmult.f n x' = natToBits (2 * n) (p * q)) :
    bitsToNat (FunFamily.blocks 2 n x' 0) = p ∨ bitsToNat (FunFamily.blocks 2 n x' 0) = q := by
  rw [fmult_f] at h
  have hlt : p * q < 2 ^ (2 * n) := by rw [two_mul]; exact mul_lt_two_pow_add hpn hqn
  exact fmultNat_eq_mul_prime hp hq
    (natToBits_injOn (fmultNat_lt (bitsToNat_lt _) (bitsToNat_lt _)) hlt h)

/-- **`f_mult` is easy to compute** [PS10, Theorem 33.5, "clearly computable in polynomial
time"], given binary multiplication and comparison (`ArithmeticFP`).

**Proof sketch.** The evaluator on `⟨1^n, w⟩` (`w` the `2n`-bit input) is an FP function:
`x := w.take n` and `y := w.drop n` (`Complexity.polyTimeComputable_pairTakePoly var`,
`polyTimeComputable_pairDropPoly var` on `⟨1^n, w⟩`), the tests `x = 1`, `y = 1` by two
comparisons with the numeral `[true]` (`H.le` on `⟨x, [true]⟩` and `⟨[true], x⟩`,
`polyTimeComputable_and`), the branch (`polyTimeComputable_ite`) between the constant
numeral `natToList (2n) 1 = 0^{2n-1} 1` (`polyTimeComputable_unaryPoly` mapped to zeros by
`polyTimeComputable_blockMap (const 1)`, then the last bit set) and `H.mul` on `⟨x, y⟩`
(`mulStr_natToList`: the `(n + n)`-bit product). Correctness: `List.ofFn x` on blocks is
`(List.ofFn w).take n`/`.drop n` (`FunFamily.ofFn_blocks_symm`, `List.ofFn_mul`) and
`bitsToNat = listToNat ∘ List.ofFn` (`bitsToNat_eq_listToNat`). -/
theorem fmult_easy (H : ArithmeticFP) : fmult.Easy := by
  sorry

/-! ## The factoring assumption [PS10, Assumption 30.1] -/

/-- The modulus `N = pq` of a pair of distinct primes of `Π_n`, as a `2n`-bit numeral: the
input handed to the factoring adversary (and the value `f_mult(p, q)`). -/
def modulusBits (n : ℕ) (z : DistinctPrimes n) : Fin (2 * n) → Bool := natToBits (2 * n) (z.p * z.q)

/-- `modulusBits` is `f_mult` at `(p, q)`: `fmultNat p q = pq` since neither prime is `1`. -/
theorem modulusBits_eq_fmult (n : ℕ) (z : DistinctPrimes n) :
    modulusBits n z = natToBits (2 * n) (fmultNat z.p z.q) := by
  unfold modulusBits fmultNat
  rw [if_neg]
  push_neg
  exact ⟨z.p_prime.ne_one, z.q_prime.ne_one⟩

/-- **The factoring experiment** [PS10, Assumption 30.1]:
`Pr[(p, q) ← Π_n × Π_n, p ≠ q; N ← pq; r : A(1^n, N; r) ∈ {p, q}]`, the answer of `A` read as
an `n`-bit numeral (`NUPPT.inverter n n (2n)`, wrong length = failure).

**Deviation:** uniform pair of *distinct* primes; `A` receives `1^n`; `N` as a `2n`-bit
numeral; `n`-bit answer (module docstring). -/
noncomputable def factorProb (A : NUPPT) (n : ℕ) : ℝ :=
  uprob fun w : DistinctPrimes n × A.Coins n =>
    ∃ x : Fin n → Bool, A.inverter n n (2 * n) (modulusBits n w.1) w.2 = some x ∧
      (bitsToNat x = w.1.p ∨ bitsToNat x = w.1.q)

/-- **The factoring assumption** [PS10, Assumption 30.1]: every non-uniform PPT `A`
factors `N = pq`, for a uniform pair of distinct primes `p, q ∈ Π_n`, with negligible
probability.

**Deviation:** "there exists a negligible `ε` with `Pr[…] < ε(n)`" is stated as
"`Pr[…]` is negligible" (equivalent: take `ε = Pr + 2^{-n}`); see the module docstring for
the distribution and the input/output conventions. -/
def FactoringAssumption : Prop := ∀ A : NUPPT, Negligible fun n => factorProb A n

/-- The factoring probability is nonnegative. -/
theorem factorProb_nonneg (A : NUPPT) (n : ℕ) : 0 ≤ factorProb A n := uprob_nonneg _

/-- The factoring probability is at most one. -/
theorem factorProb_le_one (A : NUPPT) (n : ℕ) : factorProb A n ≤ 1 := uprob_le_one _

/-- At the degenerate parameters `n < 2` the factoring experiment is empty, so no machine
factors there (sanity: the assumption only constrains `n ≥ 2`). -/
theorem factorProb_eq_zero_of_lt (A : NUPPT) {n : ℕ} (hn : n < 2) : factorProb A n = 0 := by
  haveI := DistinctPrimes.isEmpty_of_lt hn
  unfold factorProb uprob
  simp

/-! ## The one-call reduction `A''` [PS10, Algorithm 33.6] -/

/-- **The one-call reduction `A''`** [PS10, Algorithm 33.6 and the remark on p. 34]:
`A''(1^n, N) := fst(A(1^n, N))`, the first `n` bits of the answer of the inverter `A` of
`f_mult`, with no primality test; the coins and advice of `A`.

**Deviation:** under D5 the inverter of the family `fmult` is activated at the parameter `n`
(input length `2n`, `FunFamily.invProbAt`), so `A''` calls `A(1^n, z')` — which is what
Algorithm 33.6 line 7 writes (source error 14 reads it as `A(1^{2n}, z')` in the text's
input-length parametrisation); the primality tests and the resampling of `A'` are dropped
(the text's `A''`).

Repair (run-3 audit P7-2): the former definition activated `A` at parameter `2n` (coins
`A.coins.subst (2·var)`, advice `A.advice (2n)`), which `fmult.invProbAt A n` (parameter `n`)
cannot be compared with; it is now `A` at parameter `n` with `A`'s own coins, and
`oneCallFactorer_coinLen` (`= A.coinLen (2n)`) is replaced by `coins_oneCallFactorer`. -/
noncomputable def oneCallFactorer (A : NUPPT) : NUPPT :=
  NUPPT.ofPolyTime
    (f := fun z => (fun u => (pairSndD u).take (PolyExpr.var.eval (pairFstD u).length))
      (pairEncode (NUPPT.inParam z) (A.output (NUPPT.layout (NUPPT.inParam z)
        (NUPPT.inArg z) (NUPPT.inAdvice z) (NUPPT.inCoins z)))))
    ((polyTimeComputable_pairTakePoly .var).comp (NUPPT.polyTimeComputable_inParam.pairEncode
      (A.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
        NUPPT.polyTimeComputable_inParam NUPPT.polyTimeComputable_inArg
        NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins))))
    A.coins A.adv A.advice A.advice_length

/-- `A''` has the coins of `A` (so `(oneCallFactorer A).Coins n = A.Coins n`). -/
@[simp] theorem coins_oneCallFactorer (A : NUPPT) : (oneCallFactorer A).coins = A.coins := rfl

/-- **The activation of `A''`**: `A''(1^n, y; r) = (A(1^n, y; r)).take n`. -/
theorem oneCallFactorer_runAtL (A : NUPPT) (n : ℕ) (y r : List Bool) :
    (oneCallFactorer A).runAtL n y r = (A.runAtL n y r).take n := by
  unfold oneCallFactorer
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.runAtL, NUPPT.layout, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice, NUPPT.inCoins,
    NUPPT.advInput]

/-- The polynomial `q(n) = 8(n + 1)²` of the weak one-wayness of `f_mult`
[PS10, Theorem 33.5: `q(n) = 8n²`].

**Deviation:** `(n + 1)²` instead of `n²` (`q(0) > 0` is required by `WeakOneWay`); the
bound `1 - 1/(8(n+1)²)` is weaker than the text's. -/
def fmultWeakPoly : PolyExpr := PolyExpr.normal 8 2

/-- `q(n) = 8(n+1)²`. -/
theorem eval_fmultWeakPoly (n : ℕ) : fmultWeakPoly.eval n = 8 * (n + 1) ^ 2 := rfl

/-- **Theorem 33.5** [PS10, Theorem 33.5]: under the factoring assumption (and the arithmetic
hypotheses), `f_mult` is a weak one-way function: for every non-uniform PPT `A` and all
large `n`, `Pr[x, y ← {0,1}^n : f_mult(A(1^n, xy)) = xy] ≤ 1 - 1/(8(n+1)²)`.

**Deviation:** the adversary of the family receives `1^n` where the text writes `1^{2n}`
(the parameter is `n`, the input length `2n`; interderivable by `polyTimeComputable_unaryPoly`,
D5); `q(n) = 8(n+1)²` (`fmultWeakPoly`); the reduction is the one-call `A''` without
primality test; the factoring distribution is on distinct primes (module docstring).

**Proof sketch.** *Easy:* `fmult_easy H`. *Hard:* take `q := fmultWeakPoly` (positive) and
fix `A`. Suppose the bound fails infinitely often: `1 - 1/q(n) < fmult.invProbAt A n` for
`n` in an infinite set, and let `A'' := oneCallFactorer A` (same coins,
`coins_oneCallFactorer`; no reparametrisation: `invProbAt` and `factorProb` both activate
at parameter `n`, run-3 audit P7-2). On the event `S(x, r)` "`A(1^n, f_mult(x); r)` decodes
to a preimage `x'`" (`FunFamily.invProbAt_eq_uprob`, `NUPPT.inverter_eq_some_iff`) with `x`
a `2n`-bit string whose blocks read as primes `p, q`, `fmult_inv_factor` shows that block `0`
of `x'` reads as `p` or `q`, and block `0` is what `A''` returns: `oneCallFactorer_runAtL`,
`NUPPT.runAt_eq`, `(List.ofFn x').take n = List.ofFn (blocks 2 n x' 0)`
(`FunFamily.ofFn_blocks_symm`, `List.ofFn_succ`, `List.take_left`), so `A''` factors
`N = f_mult(x) = modulusBits` (`modulusBits_eq_fmult`) on `S`. Condition on `E` = "both blocks
prime" (`one_sub_div_le_uprob_subtype` with `δ = 1/(4n²)` from
`one_div_le_uprob_prime_pair_bits` transported along `FunFamily.blocks 2 n` and
`piFinTwoEquiv`, `uprob_subtype_prod_eq`): `Pr[S | E] ≥ 1 - 4n²/(8(n+1)²) ≥ 1/2`.
Transport the subtype to `Π_n × Π_n` by `primesPairEquiv` (`uprob_comp_equiv`), drop the
diagonal by `uprob_le_uprob_subtype_add` with `E' = (p ≠ q)`, `uprob_diag` and
`one_div_card_primes_le`: `factorProb A'' n ≥ 1/2 - 2n/2^n ≥ 1/4` for the infinitely many
`n ≥ 6`, contradicting `hF A''` by `not_negligible_iff` (`c = 1`). -/
theorem fmult_weakOneWay (H : ArithmeticFP) (hF : FactoringAssumption) : fmult.WeakOneWay := by
  sorry

/-! ## Hardness amplification for `f_mult` [PS10, Theorem 36.3] -/

/-- The number of blocks `m_n = 4n³` of [PS10, Theorem 36.3]. -/
def fmultBlocks : PolyExpr := .mul (.const 4) (.pow .var 3)

/-- `m_n = 4n³`. -/
@[simp] theorem eval_fmultBlocks (n : ℕ) : fmultBlocks.eval n = 4 * n ^ 3 := rfl

/-- The input length of `f_mult^{m_n}` at parameter `n` is `4n³ · 2n = 8n⁴` (the text's `n'`). -/
theorem fmult_prod_inLen (n : ℕ) : (fmult.prod fmultBlocks).inLen.eval n = 4 * n ^ 3 * (2 * n) := rfl

/-- **The total inverter of the direct product** induced by the machine `A` at parameter
`n`: encode the tuple of `m_n` values as a `8n⁴`-bit string (`FunFamily.blocks`), run
`A(1^n, ·)`, decode the answer as a tuple of `m_n` inputs, the all-zero tuple on a
wrong-length answer (the default of `invProbOpt_le_invProb`). -/
noncomputable def prodInverter (A : NUPPT) (n : ℕ) :
    (Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) → A.Coins n →
      (Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) :=
  fun ys r => FunFamily.blocks (fmultBlocks.eval n) (2 * n)
    ((A.inverter n ((fmult.prod fmultBlocks).inLen.eval n) ((fmult.prod fmultBlocks).outLen.eval n)
      ((FunFamily.blocks (fmultBlocks.eval n) (2 * n)).symm ys) r).getD (fun _ => false))

/-- **The random-planting one-call reduction** [PS10, Algorithm 37.4, one-call variant
without primality test] at the concrete level: on the challenge `N` with coins
`(i, (x⃗, y⃗), r)`, plant `N` at position `i` of `f'(x⃗, y⃗)` (`OneWay.yaoTry`), call the
inverter `B` of the direct product and return the first `n`-bit block (`x'_i`) of its
`i`-th answer.

**Deviation:** the position `i` is uniform instead of "the first prime pair" and no
primality test is made (the text's exercise, p. 37); the output is the first block of the
`i`-th answer ("Output `x'_i`"), which `fmult_inv_factor` shows to be a factor whenever
the answer is a preimage. -/
def plantFactor {n : ℕ} {ρ : Type*}
    (B : (Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) → ρ →
      (Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)))
    (N : Fin (2 * n) → Bool)
    (c : Fin (fmultBlocks.eval n) × ((Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) × ρ)) :
    Fin n → Bool :=
  FunFamily.blocks 2 n (OneWay.yaoTry (fmult.f n) B N c) 0

/-- **The machine of Algorithm 37.4** [PS10, Algorithm 37.4]: for every inverter `A` of the
direct product there is a non-uniform PPT `A''` whose factoring probability is, up to the
statistical term `2^{-n}` of the rejection-sampled position, at least the probability that
the concrete planting reduction `plantFactor (prodInverter A n)` with ideal uniform coins
outputs a factor of `N = pq` for a uniform pair of distinct primes.

Repair (run-3 audit P7-5): the former sketch read `k n := m n` bits per position trial, for
which every trial fails with probability `1 − m/2^m ≥ 1/2` (`m ≥ 4`) and
`uprob_rejectionSample_none_le_half_pow` (`2^k ≤ 2m`) does not apply; the position is now
sampled from `k n := Nat.size (m n)` bits.

**Proof sketch.** `A''` is `NUPPT.ofPolyTime` of an FP function of the raw input
`⟨⟨⟨1^n, N⟩, α⟩, r⟩` with coins `add (mul var Bp) (add (mul m (mul (const 2) var)) A.coins)`,
where `m = fmultBlocks` and `Bp := add (mul (const 3) var) (const 3)` is the width of a
position block (`4n³ < 2^{3n+3}`, so `k n := Nat.size (m n) ≤ Bp n`, `Nat.size_le`), and advice
`α n := ⟨A.advice n, ⟨natToList (Bp n) (m n), 1^{k n}⟩⟩` (length bounded by a `PolyExpr`; the
unary `1^{k n}` is also `sizeStr` of the numeral, `H.size`): cut the coins
(`polyTimeComputable_pairTakePoly`/`_pairDropPoly`), read the position
`i := (rejectionSample (m n) (k n) n (trials)).getD 0` from the first `k n` bits of each of the
`n` position blocks (`polyTimeComputable_pairTakePoly var` on `⟨1^{k n}, block⟩`, each trial
compared with the advice numeral by `H.le`, `polyTimeComputable_blockMap`,
`polyTimeComputable_ite`),
evaluate `f_mult` on the `m n` fresh `2n`-bit blocks (`polyTimeComputable_blockMap
(mul (const 2) var)` with the evaluator of `fmult_easy H`), plant `N` at block `i`
(`take`/`drop` at the unary offset `1^{i · 2n}`, `Turing.FinTM.computesFunInTime_unaryMul`),
call `A.output` on the layout `⟨⟨⟨1^n, z⃗⟩, A.advice n⟩, r'⟩` (`NUPPT.polyTimeComputable_layout`,
`A.polyTimeComputable_output`), take block `i` of the answer when its length is `8n⁴`
(`polyTimeComputable_lenEq`, `_ite`; otherwise `0^{2n}`) and output its first `n` bits.
Functional identity: `A''.inverter n n (2n) N r = some (plantFactor (prodInverter A n) N (S n r))`
with `S n` the typed coin sampler (position by `(rejectionSample …).getD 0`, blocks by
`FunFamily.blocks`, coins verbatim), by `NUPPT.runAtL_ofPolyTime`, `NUPPT.inverter_eq_some_iff`,
`FunFamily.ofFn_blocks_symm` and `decodeFin_ofFn`. Probability: `statClose_rejectionSample
(m n) (k n) n 0` with `uprob_rejectionSample_none_le_half_pow` — its hypotheses
`m n ≤ 2^{k n}` and `2^{k n} ≤ 2 m n` are `Nat.lt_size_self` and `Nat.lt_size` at `k n − 1`
(`m n ≥ 4`) — puts the sampled position within `(1/2)^n` of uniform; `StatClose.prod` with
`StatClose.refl` on the other components,
`StatClose.comp_equiv_left` for the coin-string bijection and
`StatClose.abs_uprob_sub_le_prod` (auxiliary coins: the pair of primes) give the claim. -/
theorem exists_plantFactorer (H : ArithmeticFP) (A : NUPPT) :
    ∃ A'' : NUPPT, ∀ n, 1 ≤ n →
      uprob (fun z : DistinctPrimes n × (Fin (fmultBlocks.eval n) ×
          ((Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) × A.Coins n)) =>
          bitsToNat (plantFactor (prodInverter A n) (modulusBits n z.1) z.2) = z.1.p ∨
            bitsToNat (plantFactor (prodInverter A n) (modulusBits n z.1) z.2) = z.1.q)
        - (1 / 2 : ℝ) ^ n ≤ factorProb A'' n := by
  sorry

/-- **Theorem 36.3** [PS10, Theorem 36.3]: under the factoring assumption (and the
arithmetic hypotheses), the direct product `f'((x₁, y₁), …, (x_{m_n}, y_{m_n})) =
(f_mult(x₁, y₁), …, f_mult(x_{m_n}, y_{m_n}))` with `m_n = 4n³` blocks is a strong one-way
function.

**Deviation:** the adversary receives `1^n` where the text writes `1^{n'}`, `n' = 8n⁴` (D5,
the deviation of `FunFamily.prod`); the reduction is the random-planting one-call variant
(`plantFactor`, `exists_plantFactorer`); factoring on distinct primes (module docstring).

**Proof sketch.** *Easy:* `FunFamily.Easy.prod (fmult_easy H)`. *Hard:* fix `A` and
suppose `fun n => (fmult.prod fmultBlocks).invProbAt A n` is not negligible;
`not_negligible_iff` gives `c` with `1/n^c ≤ invProbAt` for infinitely many `n`
(`FunFamily.invProbAt_nonneg`). `FunFamily.invProbAt_prod_eq` and `invProbOpt_le_invProb`
give `1/n^c ≤ invProb (prodFun (fmult.f n) (m n)) (prodInverter A n)` (the default
`fun _ => false` is `blocks` of the all-zero string). `invProb_prodFun_le_plant` with the
good set `G x` = "both blocks of `x` read as primes" yields
`1/n^c ≤ (1 - Pr[G])^{m n} + m n · Pr[G x ∧ f_mult(yaoTry … (f_mult x) c) = f_mult x]`;
`one_div_le_uprob_prime_pair_bits` (transported along `FunFamily.blocks 2 n` and
`piFinTwoEquiv`) gives `Pr[G] ≥ 1/(4n²)`, and `claim_36_2_half_pow` gives
`(1 - Pr[G])^{4n³} ≤ (1/2)^n`. Hence the planted experiment succeeds on a uniform good
input with probability at least `(1/n^c - (1/2)^n)/(4n³)` (`uprob_and_eq_mul_subtype`,
`uprob_le_one`). Transport the good subtype to `Π_n × Π_n` (`uprob_subtype_prod_eq`,
`primesPairEquiv`, `uprob_comp_equiv`); on it `fmult_inv_factor` turns a preimage into a
factor (`uprob_mono`, `modulusBits_eq_fmult`); drop the diagonal by
`uprob_le_uprob_subtype_add`, `uprob_diag` and `one_div_card_primes_le` to reach
`DistinctPrimes n`; `exists_plantFactorer H A` gives `A''` with
`factorProb A'' n ≥ (1/n^c - (1/2)^n)/(4n³) - 2n/2^n - (1/2)^n ≥ 1/(8 n^{c+3})` for the
infinitely many large `n`, contradicting `hF A''` through `not_negligible_iff`. -/
theorem fmult_prod_strongOneWay (H : ArithmeticFP) (hF : FactoringAssumption) :
    (fmult.prod fmultBlocks).StrongOneWay := by
  sorry

/-! ## The factoring collection [PS10, Theorem 51.1] -/

/-- One truncated run of `SamplePrime(n)` [PS10, Algorithm 50.16] on a coin string: the
first `2n²` blocks of `n` bits are read (`padFin`, `NumberTheory.chunk`), the first prime
block is output, and the `n`-bit numeral of the prime `2` on failure.

Repair (run-3 audit P7-7): the fallback was `[]`; with a *prime* fallback (`natToBits n 2`
reads as `2` for `n ≥ 2`, `bitsToNat_natToBits`) the closeness lemma
`NumberTheory.statClose_samplePrime` applies to each run verbatim, and the pair fallback of
`samplePairOut`/`rsaGenParams` is taken only on the diagonal `p = q`. (For `n < 2` the
fallback reads as `0`, rejected by their validity tests.) -/
def samplePrimeL (n : ℕ) (r : List Bool) : List Bool :=
  List.ofFn ((samplePrime n (2 * n ^ 2) (chunk (2 * n ^ 2) n (padFin (2 * n ^ 2 * n) r))).getD
    (natToBits n 2))

/-- The output of the collection's sampler from two sampled blocks `a`, `b`: the pair of
`m`-bit numerals of the two numbers they read as, when these are distinct primes below `2^m`,
and the canonical default pair `encodeDistinctPrimes m default = ⟨2, 3⟩` otherwise (the D10
`getD`-default convention). -/
def samplePairOut (m : ℕ) (hm : 2 ≤ m) (a b : List Bool) : List Bool :=
  if (listToNat a).Prime ∧ (listToNat b).Prime ∧ listToNat a ≠ listToNat b ∧
      listToNat a < 2 ^ m ∧ listToNat b < 2 ^ m then
    pairEncode (natToList m (listToNat a)) (natToList m (listToNat b))
  else encodeDistinctPrimes m (DistinctPrimes.default hm)

/-- **The sampler's output is always a canonical encoding**: `samplePairOut m hm a b` is
`encodeDistinctPrimes m z` for some pair `z` of distinct primes (the sampled pair in the
accepting branch, the default pair otherwise). -/
theorem samplePairOut_eq_encode (m : ℕ) (hm : 2 ≤ m) (a b : List Bool) :
    ∃ z : DistinctPrimes m, samplePairOut m hm a b = encodeDistinctPrimes m z := by
  unfold samplePairOut
  split_ifs with h
  · exact ⟨⟨(⟨⟨listToNat a, h.2.2.2.1⟩, h.1⟩, ⟨⟨listToNat b, h.2.2.2.2⟩, h.2.1⟩), h.2.2.1⟩, rfl⟩
  · exact ⟨_, rfl⟩

/-- The string function of the collection's sampler on the raw layout `⟨⟨⟨1^n, i⟩, α⟩, r⟩`:
two independent runs of `SamplePrime(n)` on the two halves of the coins, output as the pair
`⟨p, q⟩` of `(max n 2)`-bit numerals when both read as distinct primes, and the canonical
default pair `⟨2, 3⟩` otherwise (`samplePairOut`).

Repair (run-3 audit P3-1): the former output `⟨a, b⟩` with the fallback `[]` of a failed run
(rejected by `decodeDistinctPrimes`, as is `p = q`) is replaced by `samplePairOut`, so that
every output decodes (`Collection.sample_spec`). -/
def samplePairRaw (z : List Bool) : List Bool :=
  samplePairOut (max (NUPPT.inParam z).length 2) (le_max_right _ _)
    (samplePrimeL (NUPPT.inParam z).length ((NUPPT.inCoins z).take (2 * (NUPPT.inParam z).length ^ 2 * (NUPPT.inParam z).length)))
    (samplePrimeL (NUPPT.inParam z).length ((NUPPT.inCoins z).drop (2 * (NUPPT.inParam z).length ^ 2 * (NUPPT.inParam z).length)))

/-- **The sampler is polynomial-time** [PS10, Lemma 51.17] given a primality test: two
runs of the `SamplePrime` loop.

**Proof sketch.** Cut the coins at the unary length `1^{2n³}` (`polyTimeComputable_pairTakePoly`
/`_pairDropPoly samplePrimeCoins` on `⟨1^n, r⟩`); each half is handled by the
`iterateFind` loop of `NumberTheory.exists_samplePrime_nuppt` (`Complexity.polyTimeComputable_iterateFind`
with the step dropping `n` bits, the test `hP` on the first `n` bits, the payload those
bits, `R = 2n²`, `P = var`), whose `List.range.find?` form is `firstHit` over `chunk`
(`samplePrime`); the fallback numeral `natToList n 2 = 0^{n-2}10` of a failed run is the
`none` branch of `iterateFind` (a constant string of unary-polynomial length,
`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`); the acceptance test of
`samplePairOut` is two `H.prime` calls, a `pairEq` test and two `H.le`
comparisons with `1^{max n 2}` (`polyTimeComputable_ite`), the accepted blocks are re-encoded
with `max n 2` bits (`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`), and the
default pair is a constant; pair the two results (`PolyTimeComputable.pairEncode`). -/
theorem polyTimeComputable_samplePairRaw (hP : PolyTimeComputable primeStr) :
    PolyTimeComputable samplePairRaw := by
  sorry

/-- **The domain sampler of the factoring collection**: the uniform `NUPPT` running two
truncated `SamplePrime(n)` loops with `2 · 2n² · n` coins. -/
noncomputable def factoringSampler (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_samplePairRaw H.prime)
    (.mul (.const 2) samplePrimeCoins)

/-- **The index generator of the factoring collection**: `Gen(1^n) = ⟨1^n, []⟩`, no coins
(the index is the unary parameter, as in `FunFamily.toCollection`). -/
noncomputable def factoringGen : NUPPT :=
  NUPPT.ofPolyTimeUniform
    (NUPPT.polyTimeComputable_inParam.pairEncode (polyTimeComputable_const [])) (.const 0)

/-- The activation of the index generator: `⟨1^n, []⟩`. -/
theorem factoringGen_runAt (n : ℕ) (r : factoringGen.Coins n) :
    factoringGen.runAt n [] r = pairEncode (List.replicate n true) [] := by
  rw [NUPPT.runAt_eq]
  unfold factoringGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp [NUPPT.inParam, NUPPT.advInput]

/-- The activation of the sampler on any index: `samplePairOut` of the two `SamplePrime(n)`
runs on the two halves of the coins. -/
theorem factoringSampler_runAt (H : ArithmeticFP) (n : ℕ) (i : List Bool)
    (s : (factoringSampler H).Coins n) :
    (factoringSampler H).runAt n i s =
      samplePairOut (max n 2) (le_max_right _ _)
        (samplePrimeL n ((List.ofFn s).take (2 * n ^ 2 * n)))
        (samplePrimeL n ((List.ofFn s).drop (2 * n ^ 2 * n))) := by
  rw [NUPPT.runAt_eq]
  unfold factoringSampler
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp [samplePairRaw, NUPPT.inParam, NUPPT.inCoins, NUPPT.advInput]

/-- **The factoring sampler's outputs decode and evaluate honestly** (the clause
`sample_spec` of `Collection`, [PS10, Definition 41.1 (2)]): at every parameter the output of
`factoringSampler` is the canonical encoding `encodeDistinctPrimes (max n 2) z` of some pair
`z` (`samplePairOut_eq_encode`), so it decodes to `z` (`decodeDistinctPrimes_encode`) and the
evaluator computes `f(z) = pq` on it (`mulStr_natToList`). Repair (run-3 audit P3-1). -/
theorem factoringSampler_spec (H : ArithmeticFP) (n : ℕ) (r : factoringGen.Coins n)
    (s : (factoringSampler H).Coins n) :
    ∃ z : DistinctPrimes (max (pairFstD (factoringGen.runAt n [] r)).length 2),
      decodeDistinctPrimes _ ((factoringSampler H).runAt n (pairFstD (factoringGen.runAt n [] r)) s) =
          some z ∧
        mulStr (pairSndD (pairEncode (pairFstD (factoringGen.runAt n [] r))
          ((factoringSampler H).runAt n (pairFstD (factoringGen.runAt n [] r)) s))) =
          natToList (2 * max (pairFstD (factoringGen.runAt n [] r)).length 2) (z.p * z.q) := by
  revert s
  rw [factoringGen_runAt, pairFstD_pairEncode, List.length_replicate]
  intro s
  rw [factoringSampler_runAt, pairSndD_pairEncode]
  obtain ⟨z, hz⟩ := samplePairOut_eq_encode (max n 2) (le_max_right _ _)
    (samplePrimeL n ((List.ofFn s).take (2 * n ^ 2 * n)))
    (samplePrimeL n ((List.ofFn s).drop (2 * n ^ 2 * n)))
  rw [hz]
  refine ⟨z, decodeDistinctPrimes_encode _ z, ?_⟩
  simp only [encodeDistinctPrimes]
  rw [mulStr_natToList _ _ _ _ z.p_lt z.q_lt, two_mul]

/-- **The factoring collection** [PS10, Theorem 51.1]: indices `1^n` (`Gen(1^n) = ⟨1^n, []⟩`,
no coins, `factoringGen`), domains `D_{1^n} = {(p, q) ∈ Π_n × Π_n : p ≠ q}` encoded as `⟨p, q⟩`
with `n`-bit numerals, `f(p, q) = pq` as a `2n`-bit numeral, the sampler `factoringSampler`
(whose outputs always decode, `factoringSampler_spec`) and the evaluator `mulStr` of the
arithmetic bundle.

**Deviation:** `Π_n` and distinct primes instead of the text's "`|p| = |q| = i/2`" (source
error 24); at parameters `n < 2` the domain is that of `n = 2` (`max n 2`), since `Π_n`
has no two distinct primes there (`DistinctPrimes.isEmpty_of_lt`); the index is the unary
parameter (`I = ℕ`), as in `FunFamily.toCollection`. -/
noncomputable def factoringCollection (H : ArithmeticFP) : Collection where
  D i := DistinctPrimes (max i.length 2)
  inhabitedD i := ⟨DistinctPrimes.default (le_max_right _ _)⟩
  encD i z := encodeDistinctPrimes (max i.length 2) z
  decD i w := decodeDistinctPrimes (max i.length 2) w
  decD_encD i z := decodeDistinctPrimes_encode _ z
  f i z := natToList (2 * max i.length 2) (z.p * z.q)
  gen := factoringGen
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  sample := factoringSampler H
  sample_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  eval z := mulStr (pairSndD z)
  eval_poly := H.mul.comp polyTimeComputable_pairSndD
  eval_spec i z := by
    simp only [pairSndD_pairEncode, encodeDistinctPrimes]
    rw [mulStr_natToList _ _ _ _ z.p_lt z.q_lt, two_mul]
  sample_spec := factoringSampler_spec H

/-- The index generated by the factoring collection is `1^n`. -/
theorem factoringCollection_index (H : ArithmeticFP) (n : ℕ)
    (r : (factoringCollection H).gen.Coins n) :
    (factoringCollection H).index n r = List.replicate n true := by
  simp [Collection.index, factoringCollection, factoringGen, NUPPT.runAt_eq,
    NUPPT.runAtL_ofPolyTimeUniform, NUPPT.inParam, NUPPT.advInput]

/-- **The sampler is close to uniform** [PS10, Lemma 51.17 and Theorem 51.1, "sample two
random prime numbers"]: the decoded output of the factoring collection's sampler is within
a negligible statistical distance of the uniform pair of distinct primes.

**Proof sketch.** Take `δ n := 1` for `n < 2` and `δ n := 2 (1/2)^n + 2n/2^n` for `n ≥ 2`
(negligible: `negligible_two_pow_neg`, `Negligible.mul_pow`, `Negligible.add`). For
`n ≥ 2` the index is `1^n` (`factoringCollection_index`) and the domain `DistinctPrimes n`;
the sampler's output on coins `r` is `⟨samplePrimeL n r₁, samplePrimeL n r₂⟩`
(`NUPPT.runAtL_ofPolyTimeUniform`, `samplePairRaw`), each half a `samplePrime n (2n²)` run
on `chunk` of its coins with the prime fallback `d = natToBits n 2` (`bitsToNat_natToBits`,
`Nat.prime_two`; run-3 audit P7-7), so `statClose_samplePrime n (2n²)` applies verbatim to
each run — within `(1 − 1/(2n))^{2n²} ≤ (1/2)^n` of the uniform prime
(`uprob_samplePrime_none_le_two_pow`'s bound) — and `StatClose.prod` gives the pair within
`2(1/2)^n` of uniform on `Π_n × Π_n`. The output `samplePairOut` re-encodes the two blocks
with `n`-bit numerals when they read as distinct primes (`bitsToNat_eq_listToNat`,
`natToBits_bitsToNat`: the numeral of an `n`-bit block is the block) and is the default pair
on the diagonal `p = q` (a failed run outputs the prime `2`, so no other case is left), so
against the uniform `some x` on `DistinctPrimes n` the extra error is the diagonal
`uprob_diag`, bounded by `one_div_card_primes_le`; combine with `StatClose.trans` and
`StatClose.map`. -/
theorem factoringCollection_sampleClose (H : ArithmeticFP) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ (factoringCollection H).SampleClose δ := by
  sorry

/-- **The reduction from the collection to factoring** [PS10, proof of Theorem 51.1, "the
factoring assumption states that inverting `f_i` is hard"]: `A_fact(1^n, N) :=
fst(A(1^n, ⟨1^n, N⟩))`, the first component of the pair answered by an inverter `A` of the
collection at the index `1^n`; same coins and advice as `A`. -/
noncomputable def collectionFactorer (A : NUPPT) : NUPPT :=
  NUPPT.ofPolyTime
    (f := fun z => pairFstD (A.output (NUPPT.layout (NUPPT.inParam z)
      (pairEncode (NUPPT.inParam z) (NUPPT.inArg z)) (NUPPT.inAdvice z) (NUPPT.inCoins z))))
    (polyTimeComputable_pairFstD.comp (A.polyTimeComputable_output.comp
      (NUPPT.polyTimeComputable_layout NUPPT.polyTimeComputable_inParam
        (NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inArg)
        NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins)))
    A.coins A.adv A.advice A.advice_length

/-- `collectionFactorer` has the coins of `A`. -/
@[simp] theorem coins_collectionFactorer (A : NUPPT) : (collectionFactorer A).coins = A.coins := rfl

/-- **The activation of the reduction**: `A_fact(1^n, y; r) = fst(A(1^n, ⟨1^n, y⟩; r))`. -/
theorem collectionFactorer_runAt (A : NUPPT) (n : ℕ) (y : List Bool)
    (r : (collectionFactorer A).Coins n) :
    (collectionFactorer A).runAt n y r = pairFstD (A.runAt n (pairEncode (List.replicate n true) y) r) := by
  rw [NUPPT.runAt_eq]
  unfold collectionFactorer
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.runAt, NUPPT.layout, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice, NUPPT.inCoins,
    NUPPT.advInput]

/-- **Inverting the collection factors** [PS10, proof of Theorem 51.1]: for `n ≥ 2`, the
inversion probability of `A` against the factoring collection is at most the factoring
probability of `collectionFactorer A`.

**Proof sketch.** The generator has no coins, so `Collection.invProbAt` is the inner
probability at the index `1^n` (`OneWay.uexp_const`, `factoringCollection_index`), whose
domain is `DistinctPrimes n` (`max n 2 = n`) and whose encoded value `f_i(p, q)` is
`natToList (2n) (pq) = List.ofFn (modulusBits n z)`. If `A`'s answer decodes
(`decodeDistinctPrimes`) to `(p', q')` with `natToList (2n) (p'q') = natToList (2n) (pq)`,
then `p'q' = pq` (`natToList_injOn`, `DistinctPrimes.mul_lt`) and `p' ∈ {p, q}`
(`fmultNat_eq_mul_prime` with `fmultNat p' q' = p'q'`, `modulusBits_eq_fmult`); the first
component of the answer is the `n`-bit numeral of `p'` (`decodeFin`,
`length_eq_of_decodeFin_eq_some`), which `collectionFactorer_runAt` returns and
`NUPPT.inverter` decodes to `natToBits n p'` (`natToBits_bitsToNat`); conclude by
`uprob_mono` with the coin types identified (`coins_collectionFactorer`). -/
theorem factoringCollection_invProbAt_le (H : ArithmeticFP) (A : NUPPT) {n : ℕ} (hn : 2 ≤ n) :
    (factoringCollection H).invProbAt A n ≤ factorProb (collectionFactorer A) n := by
  sorry

/-- **Theorem 51.1** [PS10, Theorem 51.1]: under the factoring assumption (and the
arithmetic hypotheses), the factoring collection `{f_i(p, q) = pq}` is a collection of
one-way functions.

**Deviation:** see `factoringCollection` (`Π_n`, distinct primes, degenerate parameters)
and the module docstring.

**Proof sketch.** The sampling clause is `factoringCollection_sampleClose H`. For the
hardness clause fix `A`: `factoringCollection_invProbAt_le H A` bounds the inversion
probability by `factorProb (collectionFactorer A) n` for `n ≥ 2`, which is negligible by
`hF (collectionFactorer A)`; conclude with `Negligible.mono` (`Collection.invProbAt_nonneg`,
`factorProb_nonneg`, threshold `n₀ = 2`). -/
theorem factoringCollection_oneWay (H : ArithmeticFP) (hF : FactoringAssumption) :
    (factoringCollection H).OneWay := by
  sorry

end TCSlib.Cryptography.Candidates
