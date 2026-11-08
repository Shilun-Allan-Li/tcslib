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

/-- **Leading zeros**: the `(j + |w|)`-bit numeral of the number read from `w` is `0^j w`
(`natToList_length_listToNat` on `0^j w`, which reads as the same number). -/
private theorem fac_natToList_lead (j : ℕ) (w : List Bool) :
    natToList (j + w.length) (listToNat w) = List.replicate j false ++ w := by
  have h := natToList_length_listToNat (List.replicate j false ++ w)
  rw [List.length_append, List.length_replicate, listToNat_append, listToNat_replicate_false,
    zero_mul, zero_add] at h
  exact h

/-- The numeral of `1`: `natToList k 1 = (0^k ++ 1).drop 1` (`0^{k−1}1` for `k ≥ 1`, empty for
`k = 0`). -/
private theorem fac_natToList_one (k : ℕ) : natToList k 1 = (List.replicate k false ++ [true]).drop 1 := by
  rcases k with _ | m
  · rw [natToList_zero]; rfl
  · have h := fac_natToList_lead m [true]
    rw [listToNat_eq] at h
    exact h

/-- The two `n`-bit halves of a `2n`-bit string are its two blocks:
`(List.ofFn x).take n = List.ofFn (blocks 2 n x 0)` and `.drop n` is block `1`. -/
private theorem fac_ofFn_halves (n : ℕ) (x : Fin (2 * n) → Bool) :
    (List.ofFn x).take n = List.ofFn (FunFamily.blocks 2 n x 0) ∧
      (List.ofFn x).drop n = List.ofFn (FunFamily.blocks 2 n x 1) := by
  have h : List.ofFn x = List.ofFn (FunFamily.blocks 2 n x 0) ++ List.ofFn (FunFamily.blocks 2 n x 1) := by
    conv_lhs => rw [← (FunFamily.blocks 2 n).symm_apply_apply x]
    rw [FunFamily.ofFn_blocks_symm, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
    rfl
  rw [h]
  exact ⟨List.take_left' (List.length_ofFn), List.drop_left' (List.length_ofFn)⟩

/-- The test "the word reads as `1`" by two comparisons with the numeral `[true]` (`H.le`). -/
private theorem fac_polyTimeComputable_isOne (H : ArithmeticFP) {g : List Bool → List Bool}
    (hg : PolyTimeComputable g) :
    PolyTimeComputable fun z => [decide (listToNat (g z) ≤ 1) && decide (1 ≤ listToNat (g z))] := by
  have h1 := H.le.comp (hg.pairEncode (polyTimeComputable_const [true]))
  have h2 := H.le.comp ((polyTimeComputable_const [true]).pairEncode hg)
  simp only [Function.comp_def, leStr_pairEncode, listToNat_singleton_true] at h1 h2
  exact polyTimeComputable_and h1 h2

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
  rw [FunFamily.easy_iff]
  have hx := polyTimeComputable_pairTakePoly .var
  have hy := polyTimeComputable_pairDropPoly .var
  simp only [PolyExpr.eval_var] at hx hy
  have htest := polyTimeComputable_or (fac_polyTimeComputable_isOne H hx)
    (fac_polyTimeComputable_isOne H hy)
  have hone : PolyTimeComputable fun z =>
      (List.replicate (2 * (pairFstD z).length) false ++ [true]).drop 1 := by
    have h := (polyTimeComputable_pairDropPoly (.const 1)).comp ((polyTimeComputable_const []).pairEncode
      ((polyTimeComputable_zerosPoly (.mul (.const 2) .var)).append (polyTimeComputable_const [true])))
    simpa only [Function.comp_def, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_const,
      PolyExpr.eval_var, PolyExpr.eval_mul] using h
  refine ⟨_, polyTimeComputable_ite htest hone (H.mul.comp (hx.pairEncode hy)), fun n x => ?_⟩
  obtain ⟨h0, h1⟩ := fac_ofFn_halves n x
  simp only [Function.comp_apply, NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, h0, h1, mulStr_pairEncode, List.length_ofFn]
  have hf : List.ofFn (fmult.f n x) = natToList (2 * n)
      (fmultNat (bitsToNat (FunFamily.blocks 2 n x 0)) (bitsToNat (FunFamily.blocks 2 n x 1))) := by
    rw [fmult_f, natToList_eq]
  rw [hf]
  unfold fmultNat
  rw [← bitsToNat_eq_listToNat, ← bitsToNat_eq_listToNat]
  by_cases hc : bitsToNat (FunFamily.blocks 2 n x 0) = 1 ∨ bitsToNat (FunFamily.blocks 2 n x 1) = 1
  · rw [if_pos hc, if_pos, fac_natToList_one]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega
  · rw [if_neg hc, if_neg, ← two_mul]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega

/-! ## The factoring assumption [PS10, Assumption 30.1] -/

/-- The modulus `N = pq` of a pair of distinct primes of `Π_n`, as a `2n`-bit numeral: the
input handed to the factoring adversary (and the value `f_mult(p, q)`). -/
def modulusBits (n : ℕ) (z : DistinctPrimes n) : Fin (2 * n) → Bool := natToBits (2 * n) (z.p * z.q)

/-- The defining equation of `modulusBits`: `modulusBits n z = natToBits (2n) (pq)`, the
`2n`-bit numeral of the modulus. -/
theorem modulusBits_eq (n : ℕ) (z : DistinctPrimes n) :
    modulusBits n z = natToBits (2 * n) (z.p * z.q) := rfl

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

/-- The defining equation of `factorProb`: `factorProb A n` is the probability, over a uniform
pair `z` of distinct primes of `Π_n` and the coins of `A`, that `A`'s answer on the `2n`-bit
modulus `modulusBits n z` is an `n`-bit numeral reading as `z.p` or `z.q`. -/
theorem factorProb_eq (A : NUPPT) (n : ℕ) :
    factorProb A n = uprob fun w : DistinctPrimes n × A.Coins n =>
      ∃ x : Fin n → Bool, A.inverter n n (2 * n) (modulusBits n w.1) w.2 = some x ∧
        (bitsToNat x = w.1.p ∨ bitsToNat x = w.1.q) := rfl

/-- **The factoring assumption** [PS10, Assumption 30.1]: every non-uniform PPT `A`
factors `N = pq`, for a uniform pair of distinct primes `p, q ∈ Π_n`, with negligible
probability.

**Deviation:** "there exists a negligible `ε` with `Pr[…] < ε(n)`" is stated as
"`Pr[…]` is negligible" (equivalent: take `ε = Pr + 2^{-n}`); see the module docstring for
the distribution and the input/output conventions. -/
def FactoringAssumption : Prop := ∀ A : NUPPT, Negligible fun n => factorProb A n

/-- Unfolding: the factoring assumption is the negligibility of every `factorProb`. -/
theorem factoringAssumption_iff :
    FactoringAssumption ↔ ∀ A : NUPPT, Negligible fun n => factorProb A n := Iff.rfl

/-- The factoring probability is nonnegative. -/
theorem factorProb_nonneg (A : NUPPT) (n : ℕ) : 0 ≤ factorProb A n := uprob_nonneg _

/-- The factoring probability is at most one. -/
theorem factorProb_le_one (A : NUPPT) (n : ℕ) : factorProb A n ≤ 1 := uprob_le_one _

/-- At the degenerate parameters `n < 2` the factoring experiment is empty, so no machine
factors there (sanity: the assumption only constrains `n ≥ 2`). -/
theorem factorProb_eq_zero_of_lt (A : NUPPT) {n : ℕ} (hn : n < 2) : factorProb A n = 0 := by
  haveI := DistinctPrimes.isEmpty_of_lt hn
  unfold factorProb
  rw [uprob_def]
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
@[simp] theorem coins_oneCallFactorer (A : NUPPT) : (oneCallFactorer A).coins = A.coins := by
  unfold oneCallFactorer
  exact NUPPT.coins_ofPolyTime _ _ _ _ _

/-- **`A''` runs on the coins of `A`**: the published equivalence
`(oneCallFactorer A).Coins n ≃ A.Coins n` (`NUPPT.coinsCongr` along `coins_oneCallFactorer`). -/
noncomputable def oneCallFactorer_coinsEquiv (A : NUPPT) (n : ℕ) :
    (oneCallFactorer A).Coins n ≃ A.Coins n :=
  NUPPT.coinsCongr (coins_oneCallFactorer A) n

/-- The coin equivalence keeps the coin string:
`List.ofFn (oneCallFactorer_coinsEquiv A n r) = List.ofFn r`. -/
theorem oneCallFactorer_coinsEquiv_ofFn (A : NUPPT) (n : ℕ)
    (r : (oneCallFactorer A).Coins n) :
    List.ofFn (oneCallFactorer_coinsEquiv A n r) = List.ofFn r :=
  NUPPT.coinsCongr_ofFn (coins_oneCallFactorer A) n r

/-- **The activation of `A''`**: `A''(1^n, y; r) = (A(1^n, y; r)).take n`. -/
theorem oneCallFactorer_runAtL (A : NUPPT) (n : ℕ) (y r : List Bool) :
    (oneCallFactorer A).runAtL n y r = (A.runAtL n y r).take n := by
  unfold oneCallFactorer
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.runAtL_eq, NUPPT.layout_eq, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inAdvice_eq,
    NUPPT.inCoins_eq, NUPPT.advInput_eq]

/-- The polynomial `q(n) = 8(n + 1)²` of the weak one-wayness of `f_mult`
[PS10, Theorem 33.5: `q(n) = 8n²`].

**Deviation:** `(n + 1)²` instead of `n²` (`q(0) > 0` is required by `WeakOneWay`); the
bound `1 - 1/(8(n+1)²)` is weaker than the text's. -/
def fmultWeakPoly : PolyExpr := PolyExpr.normal 8 2

/-- `q(n) = 8(n+1)²`. -/
theorem eval_fmultWeakPoly (n : ℕ) : fmultWeakPoly.eval n = 8 * (n + 1) ^ 2 := by
  unfold fmultWeakPoly
  exact PolyExpr.eval_normal 8 2 n

/-- "Both `n`-bit blocks of `x` read as primes": the good set of [PS10, Theorems 33.5, 36.3]. -/
private def fac_PrimeBlocks (n : ℕ) (x : Fin (2 * n) → Bool) : Prop :=
  (bitsToNat (FunFamily.blocks 2 n x 0)).Prime ∧ (bitsToNat (FunFamily.blocks 2 n x 1)).Prime

/-- A `2n`-bit string as its pair of `n`-bit blocks (`FunFamily.blocks`, `piFinTwoEquiv`). -/
private noncomputable def fac_halvesEquiv (n : ℕ) :
    (Fin (2 * n) → Bool) ≃ (Fin n → Bool) × (Fin n → Bool) :=
  (FunFamily.blocks 2 n).trans (piFinTwoEquiv fun _ => Fin n → Bool)

private theorem fac_halvesEquiv_apply (n : ℕ) (x : Fin (2 * n) → Bool) :
    fac_halvesEquiv n x = (FunFamily.blocks 2 n x 0, FunFamily.blocks 2 n x 1) := rfl

/-- **Prime-pair density on `2n`-bit strings**: both blocks read as primes with probability at
least `1/(4n²)` (`one_div_le_uprob_prime_pair_bits` along `fac_halvesEquiv`). -/
private theorem fac_density (n : ℕ) (hn : 2 ≤ n) :
    1 / (4 * (n : ℝ) ^ 2) ≤ uprob (fac_PrimeBlocks n) := by
  have h := one_div_le_uprob_prime_pair_bits n hn
  rw [← uprob_comp_equiv (fac_halvesEquiv n)] at h
  exact h

/-- The good subtype of `2n`-bit strings is `Π_n × Π_n` (`fac_halvesEquiv`, `primesPairEquiv`). -/
private noncomputable def fac_goodEquiv (n : ℕ) :
    {x : Fin (2 * n) → Bool // fac_PrimeBlocks n x} ≃ Primes n × Primes n :=
  (Equiv.subtypeEquiv (fac_halvesEquiv n) fun _ => Iff.rfl).trans (primesPairEquiv n)

private theorem fac_goodEquiv_val (n : ℕ) (x : {x : Fin (2 * n) → Bool // fac_PrimeBlocks n x}) :
    (((fac_goodEquiv n x).1.1 : Fin (2 ^ n)) : ℕ) = bitsToNat (FunFamily.blocks 2 n x.1 0) ∧
      (((fac_goodEquiv n x).2.1 : Fin (2 ^ n)) : ℕ) = bitsToNat (FunFamily.blocks 2 n x.1 1) :=
  primesPairEquiv_apply_val n _

/-- **Dropping the diagonal**: a uniform pair of `Π_n × Π_n` is within `2n/2^n` of a uniform pair of
*distinct* primes (`uprob_le_uprob_subtype_add` both ways, `uprob_diag`, `one_div_card_primes_le`).

**Proof sketch.** For a test `T` let `a = Pr[T]` on `Π_n × Π_n`, `b = Pr[T | p ≠ q]` (the
experiment on `DistinctPrimes n`, `p_eq`/`q_eq`) and `d = Pr[p = q]`. Dropping the conditioning
gives `a ≤ b + d`, and the same for the complement of `T` gives `b ≤ a + d` (`uprob_not`); and
`d = 1/|Π_n| ≤ 2n/2^n` (`uprob_diag`, `one_div_card_primes_le`). -/
private theorem fac_statClose_diag (n : ℕ) (hn : 2 ≤ n) :
    StatClose (fun w : Primes n × Primes n => (((w.1.1 : Fin (2 ^ n)) : ℕ), ((w.2.1 : Fin (2 ^ n)) : ℕ)))
      (fun z : DistinctPrimes n => (z.p, z.q)) (2 * n / 2 ^ n) := by
  rw [statClose_iff]
  intro T
  haveI : Nonempty (Primes n) := ⟨(DistinctPrimes.default hn).1.1⟩
  haveI : Nonempty (DistinctPrimes n) := ⟨DistinctPrimes.default hn⟩
  let E : Primes n × Primes n → Prop := fun w => ((w.1.1 : Fin (2 ^ n)) : ℕ) ≠ w.2.1
  let S : Primes n × Primes n → Prop := fun w => T (((w.1.1 : Fin (2 ^ n)) : ℕ), ((w.2.1 : Fin (2 ^ n)) : ℕ))
  have hb : uprob (fun z : DistinctPrimes n => T (z.p, z.q)) = uprob (fun z : {w // E w} => S z.1) := by
    apply OneWay.uprob_congr
    intro z
    rw [DistinctPrimes.p_eq, DistinctPrimes.q_eq]
  have hd : uprob (fun w => ¬ E w) ≤ 2 * n / 2 ^ n := by
    have : uprob (fun w => ¬ E w) = uprob (fun w : Primes n × Primes n => w.2 = w.1) := by
      apply OneWay.uprob_congr
      intro w
      simp only [E, not_not]
      constructor
      · intro h; exact Subtype.ext (Fin.ext h.symm)
      · intro h; rw [h]
    rw [this, uprob_diag]
    exact one_div_card_primes_le n hn
  have h1 := uprob_le_uprob_subtype_add E S
  have h2 := uprob_le_uprob_subtype_add E (fun w => ¬ S w)
  rw [uprob_not, uprob_not (fun z : {w // E w} => S z.1)] at h2
  rw [hb, abs_sub_le_iff]
  constructor <;> linarith

/-- **From uniform prime pairs to uniform distinct prime pairs**: for any event `G` of the two
primes and auxiliary coins, `Pr_{Π_n × Π_n}[G] ≤ Pr_{distinct}[G] + 2n/2^n`
(`fac_statClose_diag` tested on `G`, the auxiliary coins carried along:
`StatClose.abs_uprob_sub_le_prod`). -/
private theorem fac_uprob_primes_le {ρ : Type*} [Fintype ρ] [Nonempty ρ] (n : ℕ) (hn : 2 ≤ n)
    (G : ℕ → ℕ → ρ → Prop) :
    uprob (fun z : (Primes n × Primes n) × ρ =>
        G ((z.1.1 : Fin (2 ^ n)) : ℕ) ((z.1.2 : Fin (2 ^ n)) : ℕ) z.2) ≤
      uprob (fun z : DistinctPrimes n × ρ => G z.1.p z.1.q z.2) + 2 * n / 2 ^ n := by
  have h := (fac_statClose_diag n hn).abs_uprob_sub_le_prod fun v r => G v.1 v.2 r
  exact sub_le_iff_le_add'.1 (abs_sub_le_iff.1 h).1

/-- `f_mult` of two primes is their product (neither is `1`). -/
private theorem fac_fmultNat_of_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) : fmultNat p q = p * q := by
  unfold fmultNat
  rw [if_neg]
  push_neg
  exact ⟨hp.ne_one, hq.ne_one⟩

/-- **The concrete step of Theorem 33.5** [PS10, proof of Theorem 33.5, `A''`]: if `A` inverts
`f_mult` at parameter `n ≥ 2` with probability above `1 − 1/q(n)`, then `A'' = oneCallFactorer A`
factors a uniform pair of distinct primes with probability at least `1/2 − 2n/2^n`.

**Proof sketch.** Let `S` be the inversion event on `(x, r)` and `E` "both blocks of `x` prime",
`Pr[E] ≥ 1/(4n²)` (`fac_density`). Conditioning (`one_sub_div_le_uprob_subtype`) gives
`Pr[S | E] ≥ 1 − 4n²/(8(n+1)²) ≥ 1/2`. On `S ∧ E`, with `p, q` the two blocks,
`f_mult(x) = ⟦pq⟧_{2n}` and block `0` of the preimage is `p` or `q` (`fmult_inv_factor`), which is
what `A''` returns (`oneCallFactorer_runAtL`, `fac_ofFn_halves`, the coins through
`oneCallFactorer_coinsEquiv`). The good subtype is `Π_n × Π_n` (`fac_goodEquiv`), and dropping
the diagonal costs `2n/2^n` (`fac_uprob_primes_le`); the experiment on distinct primes is
`factorProb A'' n` (`modulusBits_eq`). -/
private theorem fac_weak_key (A : NUPPT) (n : ℕ) (hn : 2 ≤ n)
    (h : 1 - 1 / (fmultWeakPoly.eval n : ℝ) < fmult.invProbAt A n) :
    1 / 2 - 2 * n / 2 ^ n ≤ factorProb (oneCallFactorer A) n := by
  classical
  rw [FunFamily.invProbAt_eq_uprob, eval_fmultWeakPoly] at h
  -- the inversion event, on `2n`-bit inputs (`fmult_inLen`)
  let S := fun z : (Fin (2 * n) → Bool) × A.Coins n =>
    ∃ x' : Fin (2 * n) → Bool, A.runAt n (List.ofFn (fmult.f n z.1)) z.2 = List.ofFn x' ∧
      fmult.f n x' = fmult.f n z.1
  have h' : 1 - 1 / ((8 * (n + 1) ^ 2 : ℕ) : ℝ) < uprob S := h
  have hE : 1 / (4 * (n : ℝ) ^ 2) ≤
      uprob (fun z : (Fin (2 * n) → Bool) × A.Coins n => fac_PrimeBlocks n z.1) := by
    rw [uprob_fst (fac_PrimeBlocks n)]
    exact fac_density n hn
  have hcond := one_sub_div_le_uprob_subtype
    (fun z : (Fin (2 * n) → Bool) × A.Coins n => fac_PrimeBlocks n z.1) S
    (by positivity) hE
  -- `Pr[S | E] ≥ 1/2`
  have hhalf : (1 : ℝ) / 2 ≤ uprob (fun z : {w : (Fin (2 * n) → Bool) × A.Coins n //
      fac_PrimeBlocks n w.1} => S z.1) := by
    refine le_trans ?_ hcond
    have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hq : (0 : ℝ) < 8 * ((n : ℝ) + 1) ^ 2 := by positivity
    have hlt : 1 - uprob S < 1 / (8 * ((n : ℝ) + 1) ^ 2) := by
      push_cast at h'; linarith
    rw [div_div_eq_mul_div, div_one]
    have h1 : (1 - uprob S) * (4 * (n : ℝ) ^ 2) ≤ 1 / (8 * ((n : ℝ) + 1) ^ 2) * (4 * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hlt.le (by positivity)
    have h2 : 1 / (8 * ((n : ℝ) + 1) ^ 2) * (4 * (n : ℝ) ^ 2) ≤ 1 / 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hq (by norm_num)]
      nlinarith
    linarith
  rw [← uprob_subtype_prod_eq (fac_PrimeBlocks n) S] at hhalf
  -- the factoring event of `A''`, on the coins of `A`
  let G : ℕ → ℕ → A.Coins n → Prop := fun p q r => ∃ y : Fin n → Bool,
    (oneCallFactorer A).inverter n n (2 * n) (natToBits (2 * n) (p * q))
      ((oneCallFactorer_coinsEquiv A n).symm r) = some y ∧ (bitsToNat y = p ∨ bitsToNat y = q)
  -- on a prime pair, an inverse of `f_mult` is a factor (Claim 34.1)
  have hmono : uprob (fun z : {a // fac_PrimeBlocks n a} × A.Coins n => S (z.1.1, z.2)) ≤
      uprob (fun z : {a // fac_PrimeBlocks n a} × A.Coins n =>
        G (bitsToNat (FunFamily.blocks 2 n z.1.1 0)) (bitsToNat (FunFamily.blocks 2 n z.1.1 1)) z.2) := by
    apply uprob_mono
    rintro ⟨a, r⟩ ⟨x', hrun, hx'⟩
    have hp := a.2.1
    have hq := a.2.2
    have hf : fmult.f n a.1 = natToBits (2 * n)
        (bitsToNat (FunFamily.blocks 2 n a.1 0) * bitsToNat (FunFamily.blocks 2 n a.1 1)) := by
      rw [fmult_f, fac_fmultNat_of_prime hp hq]
    rw [hf] at hx'
    have hrun' : A.runAt n (List.ofFn (natToBits (2 * n)
        (bitsToNat (FunFamily.blocks 2 n a.1 0) * bitsToNat (FunFamily.blocks 2 n a.1 1)))) r =
        List.ofFn x' := by rw [← hf]; exact hrun
    refine ⟨FunFamily.blocks 2 n x' 0, ?_, fmult_inv_factor hp hq (bitsToNat_lt _) (bitsToNat_lt _) x' hx'⟩
    have hco : List.ofFn ((oneCallFactorer_coinsEquiv A n).symm r) = List.ofFn r := by
      rw [← oneCallFactorer_coinsEquiv_ofFn A n, Equiv.apply_symm_apply]
    rw [NUPPT.inverter_eq_some_iff, NUPPT.runAt_eq, oneCallFactorer_runAtL, hco, ← NUPPT.runAt_eq,
      hrun']
    exact (fac_ofFn_halves n x').1
  -- the good subtype is `Π_n × Π_n`
  have htrans : uprob (fun z : {a // fac_PrimeBlocks n a} × A.Coins n =>
        G (bitsToNat (FunFamily.blocks 2 n z.1.1 0)) (bitsToNat (FunFamily.blocks 2 n z.1.1 1)) z.2) =
      uprob (fun z : (Primes n × Primes n) × A.Coins n =>
        G ((z.1.1 : Fin (2 ^ n)) : ℕ) ((z.1.2 : Fin (2 ^ n)) : ℕ) z.2) := by
    refine (OneWay.uprob_congr ?_).trans
      (uprob_comp_equiv (Equiv.prodCongr (fac_goodEquiv n) (Equiv.refl (A.Coins n))) _)
    rintro ⟨a, r⟩
    simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id_eq]
    rw [(fac_goodEquiv_val n a).1, (fac_goodEquiv_val n a).2]
  have hdrop := fac_uprob_primes_le n hn G
  have hfp : uprob (fun z : DistinctPrimes n × A.Coins n => G z.1.p z.1.q z.2) =
      factorProb (oneCallFactorer A) n := by
    rw [factorProb_eq]
    refine (OneWay.uprob_congr ?_).trans (uprob_comp_equiv (Equiv.prodCongr
      (Equiv.refl (DistinctPrimes n)) (oneCallFactorer_coinsEquiv A n).symm) _)
    rintro ⟨z, r⟩
    simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id_eq, G]
    rw [modulusBits_eq]
  linarith

/-- `8n ≤ 2^n` for `n ≥ 6`. -/
private theorem fac_eight_mul_le (n : ℕ) (hn : 6 ≤ n) : 8 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega

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
`oneCallFactorer_coinsEquiv`; no reparametrisation: `invProbAt` and `factorProb` both activate
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
  refine ⟨fmult_easy H, fmultWeakPoly, fun n => by rw [eval_fmultWeakPoly]; positivity, fun A => ?_⟩
  obtain ⟨n₁, hn₁⟩ := (negligible_iff _).1 ((factoringAssumption_iff.1 hF) (oneCallFactorer A)) 2
  refine ⟨max n₁ 6, fun n hn => ?_⟩
  have hn6 : 6 ≤ n := le_of_max_le_right hn
  have hsmall : factorProb (oneCallFactorer A) n < 1 / 4 := by
    have h := hn₁ n (le_of_max_le_left hn)
    rw [abs_of_nonneg (factorProb_nonneg _ _)] at h
    have h36 : (36 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (6 : ℝ) ≤ n := by exact_mod_cast hn6
      nlinarith
    have : 1 / (n : ℝ) ^ 2 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  by_contra hlt
  push_neg at hlt
  have key := fac_weak_key A n (by omega) hlt
  have h8 : (2 * n : ℝ) / 2 ^ n ≤ 1 / 4 := by
    have h8n : 8 * n ≤ 2 ^ n := fac_eight_mul_le n hn6
    have : (8 * n : ℝ) ≤ 2 ^ n := by exact_mod_cast h8n
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith

/-! ## Hardness amplification for `f_mult` [PS10, Theorem 36.3] -/

/-- The number of blocks `m_n = 4n³` of [PS10, Theorem 36.3]. -/
def fmultBlocks : PolyExpr := .mul (.const 4) (.pow .var 3)

/-- `m_n = 4n³`. -/
@[simp] theorem eval_fmultBlocks (n : ℕ) : fmultBlocks.eval n = 4 * n ^ 3 := rfl

/-- The input length of `f_mult^{m_n}` at parameter `n` is `4n³ · 2n = 8n⁴` (the text's `n'`). -/
theorem fmult_prod_inLen (n : ℕ) : (fmult.prod fmultBlocks).inLen.eval n = 4 * n ^ 3 * (2 * n) := by
  rw [FunFamily.prod_inLen, PolyExpr.eval_mul, eval_fmultBlocks, fmult_inLen]

/-- The output length of `f_mult^{m_n}` at parameter `n` is `4n³ · 2n = 8n⁴`. -/
theorem fmult_prod_outLen (n : ℕ) :
    (fmult.prod fmultBlocks).outLen.eval n = 4 * n ^ 3 * (2 * n) := by
  rw [FunFamily.prod_outLen, PolyExpr.eval_mul, eval_fmultBlocks, fmult_outLen]

/-- **The total inverter of the direct product** induced by the machine `A` at parameter
`n`: encode the tuple of `m_n` values as a `8n⁴`-bit string (`FunFamily.blocks`), run
`A(1^n, ·)`, decode the answer as a tuple of `m_n` inputs, the all-zero tuple on a
wrong-length answer (the default of `invProbOpt_le_invProb`). Both lengths of the direct
product are `m_n · 2n` (`fmult_prod_inLen`, `fmult_prod_outLen`). -/
noncomputable def prodInverter (A : NUPPT) (n : ℕ) :
    (Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) → A.Coins n →
      (Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) :=
  fun ys r => FunFamily.blocks (fmultBlocks.eval n) (2 * n)
    ((A.inverter n (fmultBlocks.eval n * (2 * n)) (fmultBlocks.eval n * (2 * n))
      ((FunFamily.blocks (fmultBlocks.eval n) (2 * n)).symm ys) r).getD (fun _ => false))

/-- **The defining equation of `prodInverter`**: decode `A(1^n, ys; r)` as a string of
`m_n · 2n` bits (the all-zero string on a wrong length) and split it into `m_n` blocks of `2n`
bits (`FunFamily.blocks`). -/
theorem prodInverter_eq (A : NUPPT) (n : ℕ) (ys : Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool))
    (r : A.Coins n) :
    prodInverter A n ys r = FunFamily.blocks (fmultBlocks.eval n) (2 * n)
      ((A.inverter n (fmultBlocks.eval n * (2 * n)) (fmultBlocks.eval n * (2 * n))
        ((FunFamily.blocks (fmultBlocks.eval n) (2 * n)).symm ys) r).getD (fun _ => false)) :=
  rfl

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

/-- The two block bijections of the library coincide: `FunFamily.blocks q ℓ = OneWay.blocksE q ℓ`
(their inverses read the same coordinate, `FunFamily.blocks_symm_apply`,
`OneWay.blocksE_symm_apply`). -/
private theorem fac_blocks_eq_blocksE (q ℓ : ℕ) : FunFamily.blocks q ℓ = OneWay.blocksE q ℓ := by
  have h : (FunFamily.blocks q ℓ).symm = (OneWay.blocksE q ℓ).symm :=
    Equiv.ext fun t => funext fun k => by
      rw [FunFamily.blocks_symm_apply, OneWay.blocksE_symm_apply]
  rw [← Equiv.symm_symm (FunFamily.blocks q ℓ), h, Equiv.symm_symm]

/-- The all-`false` string reads as `0`. -/
private theorem fac_bitsToNat_false (k : ℕ) : bitsToNat (fun _ : Fin k => false) = 0 := by
  rw [bitsToNat_eq_listToNat, List.ofFn_const, listToNat_replicate_false]

/-- Block `i` of `x` under `FunFamily.blocks` is the window `x (finProdFinEquiv (i, ·))`. -/
private theorem fac_blocks_apply (q ℓ : ℕ) (x : Fin (q * ℓ) → Bool) (i : Fin q) :
    FunFamily.blocks q ℓ x i = fun j => x (finProdFinEquiv (i, j)) := by
  rw [fac_blocks_eq_blocksE]
  funext j
  exact OneWay.blocksE_apply q ℓ x i j

/-- **The direct-product inverter and the padded inverter agree on success**: block `i` of the
answer of `prodInverter A n` (the all-`false` tuple on a wrong-length answer) is block `i` of the
padded answer `OneWay.yaoB` whenever its first half reads as a prime. -/
private theorem fac_prodInverter_eq_yaoB (A : NUPPT) (n : ℕ)
    (Y : Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) (r : A.Coins n) (i : Fin (fmultBlocks.eval n))
    (hp : (bitsToNat (FunFamily.blocks 2 n (prodInverter A n Y r i) 0)).Prime) :
    prodInverter A n Y r i = OneWay.yaoB fmult.inLen fmult.outLen fmultBlocks A n Y r i := by
  unfold prodInverter at hp ⊢
  rw [OneWay.yaoB_apply]
  rcases hx : A.inverter n (fmultBlocks.eval n * (2 * n)) (fmultBlocks.eval n * (2 * n))
      ((FunFamily.blocks (fmultBlocks.eval n) (2 * n)).symm Y) r with _ | x
  · rw [hx, Option.getD_none, fac_blocks_apply, fac_blocks_apply, fac_bitsToNat_false] at hp
    exact absurd hp Nat.not_prime_zero
  · have h2 : A.runAt n (List.ofFn ((FunFamily.blocks (fmultBlocks.eval n)
        (fmult.outLen.eval n)).symm Y)) r = List.ofFn x := (NUPPT.inverter_eq_some_iff _ _ _ _ _ _ _).1 hx
    rw [Option.getD_some, fac_blocks_apply, ← fac_blocks_eq_blocksE, h2]
    exact (OneWay.padTrue_drop_ofFn (q := fmultBlocks.eval n) (ℓ := fmult.inLen.eval n) x i).symm

/-- **The machine of Algorithm 37.4** [PS10, Algorithm 37.4]: for every inverter `A` of the
direct product there is a non-uniform PPT `A''` whose factoring probability is, up to the
statistical term `2^{-n}` of the rejection-sampled position, at least the probability that
the concrete planting reduction `plantFactor (prodInverter A n)` with ideal uniform coins
outputs a factor of `N = pq` for a uniform pair of distinct primes.

Repair (run-3 audit P7-5): the former sketch read `k n := m n` bits per position trial, for
which every trial fails with probability `1 − m/2^m ≥ 1/2` (`m ≥ 4`) and
`uprob_rejectionSample_none_le_half_pow` (`2^k ≤ 2m`) does not apply; the position is now
sampled from `k n := Nat.size (m n)` bits.

**Proof sketch.** (Route of the fill brief: the position by `OneWay.exists_posMachine`, the
model `OneWay.exists_yaoReduction`.) `A''` is `NUPPT.ofPolyTime` of the first `n` bits of the
proved one-round machine of Algorithm 38.5, `OneWay.YaoMachine.ans` (the round of
`OneWay.exists_yaoReduction`), instantiated with the evaluator of `fmult_easy H`, its blockwise
evaluator `OneWay.exists_prodEval` and the position sampler `OneWay.exists_posMachine`, the
lengths `inLen = outLen = 2n`, `m = fmultBlocks` and the inverter `A`; coins `YaoMachine.ρP`
(`n·m` position bits, of which the first `n·k` are read as `n` trials of
`k = OneWay.kkOf m = ⌊log₂ m⌋ + 1` bits, then `m·2n` fresh bits and the coins of `A`), advice
`⟨A.advice n, 1^k⟩` (`YaoMachine.adv`, `adv_length`), polynomial time by `YaoMachine.ans_poly`
and `Complexity.polyTimeComputable_pairTakePoly`. Functional identity: by
`NUPPT.runAtL_ofPolyTime`, the coin identification `NUPPT.coinsEquiv_ofPolyTime` (with
`YaoMachine.ρP_eval`) and the round identity `YaoMachine.ans_layout`, `A''(1^n, N; r)` is the
first `n`-bit block of `OneWay.yaoTry (f_mult) yaoB N (roundSample r)`, i.e.
`plantFactor yaoB N (roundSample r)`, where `OneWay.yaoB` reads block `i` of `A`'s answer
padded with `true`. Inverter comparison: whenever
`plantFactor (prodInverter A n)` outputs a factor its first block reads as a prime, so `A`'s
answer had the right length (a wrong-length answer gives the all-`false` block, which reads as
`0`), and then block `i` of `prodInverter A n` is block `i` of `yaoB` (`OneWay.padTrue_drop_ofFn`,
`FunFamily.blocks = OneWay.blocksE`); so the ideal success event with `prodInverter` is contained
in the one with `yaoB` (`uprob_mono`). Probability: `OneWay.statClose_roundSample` puts the
sampled round coins within `(1 − m/2^k)^n ≤ (1/2)^n` of uniform (`m ≤ 2^k ≤ 2m`,
`OneWay.lt_two_pow_kkOf`, `two_pow_kkOf_le`), and `StatClose.abs_uprob_sub_le_prod` (auxiliary
coins: the pair of primes) with `uprob_comp_equiv` for the coin and coordinate bijections gives
the claim. -/
theorem exists_plantFactorer (H : ArithmeticFP) (A : NUPPT) :
    ∃ A'' : NUPPT, ∀ n, 1 ≤ n →
      uprob (fun z : DistinctPrimes n × (Fin (fmultBlocks.eval n) ×
          ((Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) × A.Coins n)) =>
          bitsToNat (plantFactor (prodInverter A n) (modulusBits n z.1) z.2) = z.1.p ∨
            bitsToNat (plantFactor (prodInverter A n) (modulusBits n z.1) z.2) = z.1.q)
        - (1 / 2 : ℝ) ^ n ≤ factorProb A'' n := by
  obtain ⟨F, hF, hFx⟩ := (FunFamily.easy_iff _).1 (fmult_easy H)
  obtain ⟨F', hF', hF'x⟩ := OneWay.exists_prodEval hF fmult.inLen fmultBlocks
  obtain ⟨Pm, hPm, hPmx⟩ := OneWay.exists_posMachine
  let D : OneWay.YaoMachine.Data := ⟨F, F', Pm, fmult.inLen, fmult.outLen, fmultBlocks, A⟩
  have hans := OneWay.YaoMachine.ans_poly (D := D) hF' hPm
  have hpoly : PolyTimeComputable fun w =>
      (OneWay.YaoMachine.ans D w).take (NUPPT.inParam w).length := by
    have h := (polyTimeComputable_pairTakePoly .var).comp
      (NUPPT.polyTimeComputable_inParam.pairEncode hans)
    simpa only [Function.comp_def, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
      using h
  refine ⟨NUPPT.ofPolyTime hpoly (OneWay.YaoMachine.ρP D) (OneWay.YaoMachine.advP D)
    (OneWay.YaoMachine.adv D) (OneWay.YaoMachine.adv_length D), fun n hn => ?_⟩
  have hM : 0 < fmultBlocks.eval n := by rw [eval_fmultBlocks]; positivity
  have hFe : ∀ a : Fin (D.inLen.eval n) → Bool,
      D.Fe (pairEncode (List.replicate n true) (List.ofFn a)) = List.ofFn (fmult.f n a) :=
    fun a => by rw [← NUPPT.advInput_eq]; exact hFx n a
  have hF'' := hF'x n
  have hPm'' := hPmx (fmultBlocks.eval n) (OneWay.kkOf (fmultBlocks.eval n)) n hM
    (OneWay.kkOf_pos _) (OneWay.two_pow_kkOf_le _ hM)
  -- the coins of `A''` as the coins of a round (`NUPPT.coinsEquiv_ofPolyTime`, `ρP_eval`)
  set ce := (NUPPT.coinsEquiv_ofPolyTime hpoly (OneWay.YaoMachine.ρP D) (OneWay.YaoMachine.advP D)
    (OneWay.YaoMachine.adv D) (OneWay.YaoMachine.adv_length D) n).trans
    (Equiv.arrowCongr (finCongr (OneWay.YaoMachine.ρP_eval D n)) (Equiv.refl Bool)) with hce
  have hce_ofFn : ∀ r, List.ofFn (ce r) = List.ofFn r := fun r => by
    rw [hce, Equiv.trans_apply, ← NUPPT.coinsEquiv_ofPolyTime_ofFn hpoly _ _ _ _ n r]
    exact (List.ofFn_congr (OneWay.YaoMachine.ρP_eval D n) _).symm
  set S := OneWay.roundSample n (fmultBlocks.eval n) (fmult.inLen.eval n) (A.coinLen n)
    (OneWay.kkOf (fmultBlocks.eval n)) hM (OneWay.YaoMachine.nkk_le n _ hM) with hS
  -- the round identity: `A''` outputs the first half of the planted answer block
  have hround : ∀ (N : Fin (2 * n) → Bool) r,
      (NUPPT.ofPolyTime hpoly (OneWay.YaoMachine.ρP D) (OneWay.YaoMachine.advP D)
        (OneWay.YaoMachine.adv D) (OneWay.YaoMachine.adv_length D)).runAt n (List.ofFn N) r =
      List.ofFn (plantFactor (OneWay.yaoB fmult.inLen fmult.outLen fmultBlocks A n) N (S (ce r))) := by
    intro N r
    rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTime, NUPPT.advInput_eq, ← NUPPT.layout_eq,
      NUPPT.inParam_layout, List.length_replicate, ← hce_ofFn r,
      show List.ofFn (ce r) = List.ofFn (ce r) ++ [] from (List.append_nil _).symm,
      OneWay.YaoMachine.ans_layout (D := D) n hM (fmult.f n) hFe hF'' hPm'' N (ce r) []]
    unfold plantFactor
    exact (fac_ofFn_halves n _).1
  -- the success event of the planting reduction with the padded inverter `yaoB`
  let P : (Fin (fmultBlocks.eval n) × (Fin (fmultBlocks.eval n) → Fin (fmult.inLen.eval n) → Bool) ×
      (Fin (A.coinLen n) → Bool)) → DistinctPrimes n → Prop := fun c z =>
    bitsToNat (plantFactor (OneWay.yaoB fmult.inLen fmult.outLen fmultBlocks A n) (modulusBits n z) c) =
        z.p ∨
      bitsToNat (plantFactor (OneWay.yaoB fmult.inLen fmult.outLen fmultBlocks A n) (modulusBits n z) c) =
        z.q
  -- the factoring probability of `A''` is that event on the sampled coins
  have hfp : factorProb (NUPPT.ofPolyTime hpoly (OneWay.YaoMachine.ρP D) (OneWay.YaoMachine.advP D)
      (OneWay.YaoMachine.adv D) (OneWay.YaoMachine.adv_length D)) n =
      uprob (fun w : (Fin (n * fmultBlocks.eval n + (fmultBlocks.eval n * fmult.inLen.eval n +
        A.coinLen n)) → Bool) × DistinctPrimes n => P (S w.1) w.2) := by
    rw [factorProb_eq, ← uprob_comp_equiv ((Equiv.prodComm _ _).trans
      (Equiv.prodCongr ce (Equiv.refl (DistinctPrimes n))))]
    apply OneWay.uprob_congr
    rintro ⟨z, r⟩
    show (∃ x, _ ∧ _) ↔ P (S (ce r)) z
    constructor
    · rintro ⟨x, hx, hpq⟩
      rw [NUPPT.inverter_eq_some_iff, hround] at hx
      rw [← List.ofFn_injective hx] at hpq
      exact hpq
    · intro h
      exact ⟨_, (NUPPT.inverter_eq_some_iff _ _ _ _ _ _ _).2 (hround _ _), h⟩
  -- the sampled coins are close to uniform
  have hsc := OneWay.statClose_roundSample n (fmultBlocks.eval n) (fmult.inLen.eval n) (A.coinLen n)
    (OneWay.kkOf (fmultBlocks.eval n)) hM (OneWay.lt_two_pow_kkOf _).le
    (OneWay.YaoMachine.nkk_le n _ hM)
  have habs := hsc.abs_uprob_sub_le_prod P
  -- on uniform coins, the reduction with `prodInverter` succeeds only where the one with `yaoB` does
  have hideal : uprob (fun z : DistinctPrimes n × (Fin (fmultBlocks.eval n) ×
          ((Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) × A.Coins n)) =>
          bitsToNat (plantFactor (prodInverter A n) (modulusBits n z.1) z.2) = z.1.p ∨
            bitsToNat (plantFactor (prodInverter A n) (modulusBits n z.1) z.2) = z.1.q) ≤
      uprob (fun z : (Fin (fmultBlocks.eval n) × (Fin (fmultBlocks.eval n) →
        Fin (fmult.inLen.eval n) → Bool) × (Fin (A.coinLen n) → Bool)) × DistinctPrimes n =>
          P (id z.1) z.2) := by
    rw [← uprob_comp_equiv (Equiv.prodComm (DistinctPrimes n) _)]
    apply uprob_mono
    rintro ⟨z, i, xs, r⟩ h
    show bitsToNat (plantFactor (OneWay.yaoB fmult.inLen fmult.outLen fmultBlocks A n)
        (modulusBits n z) (i, xs, r)) = z.p ∨
      bitsToNat (plantFactor (OneWay.yaoB fmult.inLen fmult.outLen fmultBlocks A n)
        (modulusBits n z) (i, xs, r)) = z.q
    have hp : (bitsToNat (plantFactor (prodInverter A n) (modulusBits n z) (i, xs, r))).Prime := by
      rcases h with h | h
      · rw [h]; exact z.p_prime
      · rw [h]; exact z.q_prime
    unfold plantFactor at h hp ⊢
    rw [OneWay.yaoTry_eq] at h hp ⊢
    rw [← fac_prodInverter_eq_yaoB A n _ r i hp]
    exact h
  have hb : (1 - (fmultBlocks.eval n : ℝ) / 2 ^ OneWay.kkOf (fmultBlocks.eval n)) ^ n + 0 ≤
      (1 / 2 : ℝ) ^ n := by
    have h2 : ((2 ^ OneWay.kkOf (fmultBlocks.eval n) : ℕ) : ℝ) ≤ 2 * (fmultBlocks.eval n : ℕ) := by
      exact_mod_cast OneWay.two_pow_kkOf_le _ hM
    have h3 : ((fmultBlocks.eval n : ℕ) : ℝ) ≤ ((2 ^ OneWay.kkOf (fmultBlocks.eval n) : ℕ) : ℝ) := by
      exact_mod_cast (OneWay.lt_two_pow_kkOf _).le
    push_cast at h2 h3
    have hpos : (0 : ℝ) < 2 ^ OneWay.kkOf (fmultBlocks.eval n) := by positivity
    have h4 : (1 : ℝ) / 2 ≤ (fmultBlocks.eval n : ℝ) / 2 ^ OneWay.kkOf (fmultBlocks.eval n) := by
      rw [div_le_div_iff₀ (by norm_num) hpos]; linarith
    have h5 : (fmultBlocks.eval n : ℝ) / 2 ^ OneWay.kkOf (fmultBlocks.eval n) ≤ 1 := by
      rw [div_le_one hpos]; exact h3
    rw [add_zero]
    exact pow_le_pow_left₀ (by linarith) (by linarith) n
  -- unfold the local abbreviation `S`
  have key : uprob (fun w : (Fin (n * fmultBlocks.eval n + (fmultBlocks.eval n *
      fmult.inLen.eval n + A.coinLen n)) → Bool) × DistinctPrimes n => P (S w.1) w.2) =
      uprob (fun z : (Fin (n * fmultBlocks.eval n + (fmultBlocks.eval n *
        fmult.inLen.eval n + A.coinLen n)) → Bool) × DistinctPrimes n => P (OneWay.roundSample n (fmultBlocks.eval n)
        (fmult.inLen.eval n) (A.coinLen n) (OneWay.kkOf (fmultBlocks.eval n)) hM
        (OneWay.YaoMachine.nkk_le n _ hM) z.1) z.2) := rfl
  rw [hfp, key]
  have := (abs_le.1 habs).1
  linarith

/-- **The concrete chain of Theorem 36.3** [PS10, proof of Theorem 36.3]: for `n ≥ 2` and the
machine `A''` of `exists_plantFactorer`, the inversion probability of the direct product is at
most `(1/2)^n + 4n³ (Pr[A'' factors] + (1/2)^n + 2n/2^n)`.

**Proof sketch.** `FunFamily.invProbAt_prod_eq` and `invProbOpt_le_invProb` bound the inversion
probability by `invProb (prodFun f_mult (4n³)) (prodInverter A n)` (the default answer is the
all-`false` tuple, `fac_blocks_apply`). Random-position planting with the good set "both blocks
prime" (`invProb_prodFun_le_plant`) bounds this by `(1 − Pr[G])^{4n³} + 4n³ Pr[G ∧ planted
success]`; the first term is at most `(1 − 1/(4n²))^{4n³} ≤ (1/2)^n` (`fac_density`,
`claim_36_2_half_pow`). The second probability is at most the conditioned one
(`uprob_and_eq_mul_subtype`, `uprob_subtype_prod_eq`), on which a planted success is a factor
(`fmult_inv_factor`, `plantFactor`); the good subtype is `Π_n × Π_n` (`fac_goodEquiv`), the
diagonal costs `2n/2^n` (`fac_uprob_primes_le`), and on distinct primes the event is the left side
of `exists_plantFactorer`, at most `factorProb A'' n + (1/2)^n`. -/
private theorem fac_strong_key (A A'' : NUPPT) (n : ℕ) (hn : 2 ≤ n)
    (hA : uprob (fun z : DistinctPrimes n × (Fin (fmultBlocks.eval n) ×
          ((Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) × A.Coins n)) =>
          bitsToNat (plantFactor (prodInverter A n) (modulusBits n z.1) z.2) = z.1.p ∨
            bitsToNat (plantFactor (prodInverter A n) (modulusBits n z.1) z.2) = z.1.q)
        - (1 / 2 : ℝ) ^ n ≤ factorProb A'' n) :
    (fmult.prod fmultBlocks).invProbAt A n ≤
      (1 / 2 : ℝ) ^ n + 4 * (n : ℝ) ^ 3 * (factorProb A'' n + (1 / 2 : ℝ) ^ n + 2 * n / 2 ^ n) := by
  classical
  rw [FunFamily.invProbAt_prod_eq]
  refine (invProbOpt_le_invProb _ _).trans ?_
  have hB : (fun ys r => ((A.inverter n (fmultBlocks.eval n * fmult.inLen.eval n)
      (fmultBlocks.eval n * fmult.outLen.eval n)
      ((FunFamily.blocks (fmultBlocks.eval n) (fmult.outLen.eval n)).symm ys) r).map
        (FunFamily.blocks (fmultBlocks.eval n) (fmult.inLen.eval n))).getD default) =
      prodInverter A n := by
    have key : ∀ o : Option (Fin (fmultBlocks.eval n * (2 * n)) → Bool),
        (o.map (FunFamily.blocks (fmultBlocks.eval n) (2 * n))).getD default =
          FunFamily.blocks (fmultBlocks.eval n) (2 * n) (o.getD fun _ => false) := by
      rintro (_ | x)
      · rw [Option.map_none, Option.getD_none, Option.getD_none]
        funext i j
        rw [fac_blocks_apply]
        rfl
      · rw [Option.map_some, Option.getD_some, Option.getD_some]
    funext ys r
    unfold prodInverter
    exact key _
  rw [hB]
  -- random-position planting with the good set "both blocks prime" (lemma C3)
  have hplant : invProb (OneWay.prodFun (fmult.f n) (fmultBlocks.eval n)) (prodInverter A n) ≤
      (1 - uprob (fac_PrimeBlocks n)) ^ (fmultBlocks.eval n) + (fmultBlocks.eval n : ℕ) *
        uprob (fun z : (Fin (2 * n) → Bool) × (Fin (fmultBlocks.eval n) ×
          ((Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) × A.Coins n)) =>
          fac_PrimeBlocks n z.1 ∧
            fmult.f n (OneWay.yaoTry (fmult.f n) (prodInverter A n) (fmult.f n z.1) z.2) =
              fmult.f n z.1) :=
    invProb_prodFun_le_plant _ _ _
  -- Claim 36.2: no good block among `4n³` with probability at most `(1/2)^n`
  have hd := fac_density n hn
  have h1 : (1 - uprob (fac_PrimeBlocks n)) ^ (fmultBlocks.eval n) ≤ (1 / 2 : ℝ) ^ n := by
    rw [eval_fmultBlocks]
    refine le_trans (pow_le_pow_left₀ (sub_nonneg.2 (uprob_le_one _)) (by linarith) _)
      (claim_36_2_half_pow n (by omega))
  -- the planted experiment on a good input is the planting factorer on a prime pair
  let G : ℕ → ℕ → (Fin (fmultBlocks.eval n) × ((Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) ×
      A.Coins n)) → Prop := fun p q c =>
    bitsToNat (plantFactor (prodInverter A n) (natToBits (2 * n) (p * q)) c) = p ∨
      bitsToNat (plantFactor (prodInverter A n) (natToBits (2 * n) (p * q)) c) = q
  let S : (Fin (2 * n) → Bool) × (Fin (fmultBlocks.eval n) ×
      ((Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) × A.Coins n)) → Prop := fun z =>
    fmult.f n (OneWay.yaoTry (fmult.f n) (prodInverter A n) (fmult.f n z.1) z.2) = fmult.f n z.1
  have h2 : uprob (fun z : (Fin (2 * n) → Bool) × (Fin (fmultBlocks.eval n) ×
        ((Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) × A.Coins n)) =>
        fac_PrimeBlocks n z.1 ∧ S z) ≤
      uprob (fun z : {a // fac_PrimeBlocks n a} × (Fin (fmultBlocks.eval n) ×
        ((Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) × A.Coins n)) => S (z.1.1, z.2)) := by
    rw [uprob_and_eq_mul_subtype (fun z : (Fin (2 * n) → Bool) × (Fin (fmultBlocks.eval n) ×
        ((Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) × A.Coins n)) => fac_PrimeBlocks n z.1) S,
      uprob_subtype_prod_eq (fac_PrimeBlocks n) S]
    exact mul_le_of_le_one_left (uprob_nonneg _) (uprob_le_one _)
  have h3 : uprob (fun z : {a // fac_PrimeBlocks n a} × (Fin (fmultBlocks.eval n) ×
        ((Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) × A.Coins n)) => S (z.1.1, z.2)) ≤
      uprob (fun z : {a // fac_PrimeBlocks n a} × (Fin (fmultBlocks.eval n) ×
        ((Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) × A.Coins n)) =>
        G (bitsToNat (FunFamily.blocks 2 n z.1.1 0)) (bitsToNat (FunFamily.blocks 2 n z.1.1 1)) z.2) := by
    apply uprob_mono
    rintro ⟨a, c⟩ hS
    have hp := a.2.1
    have hq := a.2.2
    have hf : fmult.f n a.1 = natToBits (2 * n)
        (bitsToNat (FunFamily.blocks 2 n a.1 0) * bitsToNat (FunFamily.blocks 2 n a.1 1)) := by
      rw [fmult_f, fac_fmultNat_of_prime hp hq]
    change fmult.f n (OneWay.yaoTry (fmult.f n) (prodInverter A n) (fmult.f n a.1) c) = fmult.f n a.1
      at hS
    rw [hf] at hS
    have := fmult_inv_factor hp hq (bitsToNat_lt _) (bitsToNat_lt _) _ hS
    simp only [G]
    unfold plantFactor
    exact this
  have h4 : uprob (fun z : {a // fac_PrimeBlocks n a} × (Fin (fmultBlocks.eval n) ×
        ((Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) × A.Coins n)) =>
        G (bitsToNat (FunFamily.blocks 2 n z.1.1 0)) (bitsToNat (FunFamily.blocks 2 n z.1.1 1)) z.2) =
      uprob (fun z : (Primes n × Primes n) × (Fin (fmultBlocks.eval n) ×
        ((Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) × A.Coins n)) =>
        G ((z.1.1 : Fin (2 ^ n)) : ℕ) ((z.1.2 : Fin (2 ^ n)) : ℕ) z.2) := by
    refine (OneWay.uprob_congr ?_).trans
      (uprob_comp_equiv (Equiv.prodCongr (fac_goodEquiv n) (Equiv.refl _)) _)
    rintro ⟨a, c⟩
    simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id_eq]
    rw [(fac_goodEquiv_val n a).1, (fac_goodEquiv_val n a).2]
  haveI : Nonempty (Fin (fmultBlocks.eval n)) := ⟨⟨0, by rw [eval_fmultBlocks]; positivity⟩⟩
  have h5 := fac_uprob_primes_le n hn G
  have h6 : uprob (fun z : DistinctPrimes n × (Fin (fmultBlocks.eval n) ×
        ((Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) × A.Coins n)) => G z.1.p z.1.q z.2) =
      uprob (fun z : DistinctPrimes n × (Fin (fmultBlocks.eval n) ×
          ((Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) × A.Coins n)) =>
          bitsToNat (plantFactor (prodInverter A n) (modulusBits n z.1) z.2) = z.1.p ∨
            bitsToNat (plantFactor (prodInverter A n) (modulusBits n z.1) z.2) = z.1.q) := by
    apply OneWay.uprob_congr
    intro z
    simp only [G]
    rw [modulusBits_eq]
  have hm : ((fmultBlocks.eval n : ℕ) : ℝ) = 4 * (n : ℝ) ^ 3 := by
    rw [eval_fmultBlocks]; push_cast; ring
  have hm0 : (0 : ℝ) ≤ 4 * (n : ℝ) ^ 3 := by positivity
  rw [hm] at hplant
  have hchain : uprob (fun z : (Fin (2 * n) → Bool) × (Fin (fmultBlocks.eval n) ×
        ((Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) × A.Coins n)) =>
        fac_PrimeBlocks n z.1 ∧ S z) ≤ factorProb A'' n + (1 / 2 : ℝ) ^ n + 2 * n / 2 ^ n := by
    linarith
  have := mul_le_mul_of_nonneg_left hchain hm0
  linarith

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
  refine ⟨FunFamily.Easy.prod (fmult_easy H) fmultBlocks, fun A => ?_⟩
  obtain ⟨A'', hA''⟩ := exists_plantFactorer H A
  have hfac := (factoringAssumption_iff.1 hF) A''
  have hneg : Negligible fun n : ℕ => (2 : ℝ)⁻¹ ^ n + 4 * ((n : ℝ) ^ 3 * factorProb A'' n) +
      4 * ((n : ℝ) ^ 3 * (2 : ℝ)⁻¹ ^ n) + 8 * ((n : ℝ) ^ 4 * (2 : ℝ)⁻¹ ^ n) :=
    ((negligible_two_pow_neg.add ((hfac.mul_pow 3).const_mul 4)).add
      ((negligible_two_pow_neg.mul_pow 3).const_mul 4)).add
      ((negligible_two_pow_neg.mul_pow 4).const_mul 8)
  refine hneg.mono ⟨2, fun n hn => ?_⟩
  have hk := fac_strong_key A A'' n hn (hA'' n (by omega))
  have e : (1 / 2 : ℝ) ^ n + 4 * (n : ℝ) ^ 3 * (factorProb A'' n + (1 / 2 : ℝ) ^ n + 2 * n / 2 ^ n) =
      (2 : ℝ)⁻¹ ^ n + 4 * ((n : ℝ) ^ 3 * factorProb A'' n) +
        4 * ((n : ℝ) ^ 3 * (2 : ℝ)⁻¹ ^ n) + 8 * ((n : ℝ) ^ 4 * (2 : ℝ)⁻¹ ^ n) := by
    rw [inv_pow, one_div_pow]
    field_simp
    ring
  rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _)]
  exact (hk.trans_eq e).trans (le_abs_self _)

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

/-- **The fallback numeral of `SamplePrime`**: the `k`-bit numeral of `2` is `0^{k+2}` followed
by `10`, with its first two bits dropped (`0^{k−2}10` for `k ≥ 2`, `0` for `k = 1`, empty for
`k = 0`). -/
private theorem fac_natToList_two (k : ℕ) :
    natToList k 2 = (List.replicate k false ++ [true, false]).drop 2 := by
  rcases k with _ | _ | m
  · rw [natToList_zero]; rfl
  · rw [← natToList_mod_two_pow]
    have h := natToList_length_listToNat [false]
    rw [listToNat_eq] at h
    exact h
  · have hw : (List.replicate (m + 2) false ++ [true, false]).drop 2 =
        List.replicate m false ++ [true, false] := by
      rw [List.replicate_succ, List.replicate_succ]
      cases m with
      | zero => rfl
      | succ m => simp [List.replicate_succ]
    rw [hw]
    have h := natToList_length_listToNat (List.replicate m false ++ [true, false])
    rw [listToNat_append, listToNat_replicate_false, zero_mul, zero_add, listToNat_eq] at h
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil] at h
    exact h

/-- **One truncated run of `SamplePrime(n)` is polynomial-time** [PS10, Algorithm 50.16 and
Lemma 51.17] given a primality test: on `⟨u, r⟩` with `n = |u|`, the `n`-bit output
`samplePrimeL n r` (the first prime among the first `2n²` blocks of `n` bits of `r`, padded with
zeros to `2n² · n` bits, and the numeral `natToList n 2` of the prime `2` on failure) is
polynomial-time computable. Shared statement S1 of the factoring fill (decision D1 (A)): used by
`polyTimeComputable_samplePairRaw` and by `polyTimeComputable_rsaGenRaw` (`RSA.lean`).

**Proof sketch.** Use `NumberTheory.exists_samplePrime_nuppt hP` (`hP` in its form by
`primeStr_eq`) as a black box: it is a uniform machine `A` with `samplePrimeCoins` coins whose
activation on the coin list `List.ofFn r'`, `r' : Fin (2n² · n) → Bool`, is
`((samplePrime n (2n²) (chunk (2n²) n r')).map List.ofFn).getD []`. Do not re-derive its
`iterateFind` loop. (1) Pad the coins to `2n² · n` bits: `polyTimeComputable_padStr
samplePrimeCoins` maps `⟨u, r⟩` to `List.ofFn (padFin (2n² · n) r)` (`ofFn_padFin_eq_padStr`,
`eval_samplePrimeCoins`). (2) Run `A` on the layout `⟨⟨⟨1^n, []⟩, []⟩, coins⟩`, with `1^n`
computed from `u` (`polyTimeComputable_unaryPoly var`), through `NUPPT.polyTimeComputable_output`
and `NUPPT.polyTimeComputable_layout` (`NUPPT.runAtL_eq_output_layout`); its output is the
accepted block as a list, or `[]` when no block is prime. (3) For `n ≥ 1` an accepted block
has `n` bits, so the output is `[]` exactly on failure (for `n = 0` both sides are `[]`):
test emptiness against the constant `[]` (`polyTimeComputable_lenEq`) and branch
(`polyTimeComputable_ite`) between the output and the fallback numeral
`natToList n 2`, which is `0^{n−2}10` for `n ≥ 2` and the constants `[]` at `n = 0` and
`[false]` at `n = 1`: a string of unary-polynomial length computed from `1^n`
(`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`, with the two constant branches
by `polyTimeComputable_ite`). The three pieces agree with
`samplePrimeL` (`samplePrimeL`'s body, `Option.getD_map`). -/
theorem polyTimeComputable_samplePrimeL (hP : PolyTimeComputable primeStr) :
    PolyTimeComputable fun z => samplePrimeL (pairFstD z).length (pairSndD z) := by
  obtain ⟨A, hAu, -, hA⟩ := exists_samplePrime_nuppt (primeStr_eq ▸ hP)
  have hu : PolyTimeComputable fun z => List.replicate (pairFstD z).length true := by
    simpa only [PolyExpr.eval_var] using (polyTimeComputable_unaryPoly .var).comp polyTimeComputable_pairFstD
  have hout : PolyTimeComputable fun z => A.output (NUPPT.layout (List.replicate (pairFstD z).length true)
      [] [] (padStr samplePrimeCoins (pairFstD z) (pairSndD z))) :=
    A.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout hu (polyTimeComputable_const [])
      (polyTimeComputable_const []) (polyTimeComputable_padStr samplePrimeCoins))
  have hfb : PolyTimeComputable fun z =>
      (List.replicate (pairFstD z).length false ++ [true, false]).drop 2 := by
    have h := (polyTimeComputable_pairDropPoly (.const 2)).comp ((polyTimeComputable_const []).pairEncode
      ((polyTimeComputable_zerosPoly .var).append (polyTimeComputable_const [true, false])))
    simpa only [Function.comp_def, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_const,
      PolyExpr.eval_var] using h
  have htest := polyTimeComputable_lenEq.comp (hout.pairEncode (polyTimeComputable_const []))
  have h := polyTimeComputable_ite htest hfb hout
  convert h using 1
  funext z
  simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_nil,
    List.length_eq_zero_iff]
  have hpad : padStr samplePrimeCoins (pairFstD z) (pairSndD z) =
      List.ofFn (padFin (2 * (pairFstD z).length ^ 2 * (pairFstD z).length) (pairSndD z)) := by
    rw [← ofFn_padFin_eq_padStr, eval_samplePrimeCoins]
  have hrun : A.output (NUPPT.layout (List.replicate (pairFstD z).length true) [] []
      (padStr samplePrimeCoins (pairFstD z) (pairSndD z))) = A.runAtL (pairFstD z).length []
      (List.ofFn (padFin (2 * (pairFstD z).length ^ 2 * (pairFstD z).length) (pairSndD z))) := by
    rw [NUPPT.runAtL_eq_output_layout, hAu.advice_eq (pairFstD z).length, hpad]
  rw [hrun, hA]
  unfold samplePrimeL
  rcases hs : samplePrime (pairFstD z).length (2 * (pairFstD z).length ^ 2)
      (chunk (2 * (pairFstD z).length ^ 2) (pairFstD z).length
        (padFin (2 * (pairFstD z).length ^ 2 * (pairFstD z).length) (pairSndD z))) with _ | b
  · simp only [Option.map_none, Option.getD_none, decide_true, if_true]
    rw [← natToList_eq, fac_natToList_two]
  · simp only [Option.map_some, Option.getD_some]
    by_cases hb : List.ofFn b = []
    · have hn : (pairFstD z).length = 0 := by
        simpa only [List.length_ofFn, List.length_nil] using congrArg List.length hb
      rw [if_pos (by simpa using hb), hb, hn]
      rfl
    · rw [if_neg (by simpa using hb)]

/-- The `T` blocks of `n` bits of a coin string as a bijection: `fac_chunkEquiv T n r = chunk T n r`
(`chunk` is `r` read through `finProdFinEquiv`, `chunk_apply`). -/
private noncomputable def fac_chunkEquiv (T n : ℕ) : (Fin (T * n) → Bool) ≃ (Fin T → Fin n → Bool) where
  toFun := chunk T n
  invFun xs k := xs (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  left_inv r := by
    funext k
    simp only [chunk_apply, Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv xs := by
    funext t i
    simp only [chunk_apply, Equiv.symm_apply_apply]

/-- `(1 − 1/(2n))^{2n²} ≤ e^{−n} ≤ (1/2)^n` (`one_sub_one_div_pow_le_exp_neg`,
`exp_neg_le_half_pow`): the failure bound of `SamplePrime` with `2n²` trials. -/
private theorem fac_one_sub_pow_le_half_pow (n : ℕ) (hn : 2 ≤ n) :
    (1 - 1 / (2 * n : ℝ)) ^ (2 * n ^ 2) ≤ (1 / 2 : ℝ) ^ n := by
  have h := one_sub_one_div_pow_le_exp_neg (2 * n) n (by omega)
  have he : 2 * n * n = 2 * n ^ 2 := by ring
  rw [he] at h
  push_cast at h
  exact h.trans (exp_neg_le_half_pow n)

/-- **One run of `samplePrimeL` is close to a uniform prime**: for `n ≥ 2`, the value of
`samplePrimeL n` on `2n² · n` uniform coins is within `(1/2)^n` of a uniform element of `Π_n`
(steps (2)–(3) of the sketch of `statClose_samplePrimeL_pair`).

**Proof sketch.** On `List.ofFn r` the padding returns `r` (`padFin_ofFn`) and the value is
`bitsToNat ((samplePrime n (2n²) (chunk r)).getD ⟦2⟧_n)` (`bitsToNat_eq_listToNat`). The fallback
reads as the prime `2`, so `statClose_samplePrime` applies to uniform blocks, carried to `ℕ` by
`StatClose.map bitsToNat`; `chunk` is a bijection (`fac_chunkEquiv`, `comp_equiv_left`), the
uniform prime string is the uniform element of `Π_n` (`bitsEquiv`, `comp_equiv_right`), and
`(1 − 1/(2n))^{2n²} ≤ (1/2)^n` (`fac_one_sub_pow_le_half_pow`). -/
private theorem fac_statClose_samplePrimeL (n : ℕ) (hn : 2 ≤ n) :
    StatClose (fun r : Fin (2 * n ^ 2 * n) → Bool => listToNat (samplePrimeL n (List.ofFn r)))
      (fun p : Primes n => ((p.1 : Fin (2 ^ n)) : ℕ)) ((1 / 2 : ℝ) ^ n) := by
  have h2 : 2 < 2 ^ n := lt_of_le_of_lt hn n.lt_two_pow_self
  have hd : (bitsToNat (natToBits n 2)).Prime := by
    rw [bitsToNat_natToBits h2]; exact Nat.prime_two
  have h0 := ((statClose_samplePrime n (2 * n ^ 2) hn hd).map bitsToNat).comp_equiv_left
    (fac_chunkEquiv (2 * n ^ 2) n)
  let e2 : Primes n ≃ {b : Fin n → Bool // (bitsToNat b).Prime} :=
    (Equiv.subtypeEquiv (bitsEquiv n) (fun b => by rw [bitsEquiv_val])).symm
  have h1 := h0.comp_equiv_right e2
  have hY : (fun p : Primes n => bitsToNat ((e2 p : {b : Fin n → Bool // (bitsToNat b).Prime}) :
      Fin n → Bool)) = fun p : Primes n => ((p.1 : Fin (2 ^ n)) : ℕ) := by
    funext p
    rw [← bitsEquiv_val]
    show ((bitsEquiv n) ((bitsEquiv n).symm p.1)).val = _
    rw [Equiv.apply_symm_apply]
  have hX : (fun r : Fin (2 * n ^ 2 * n) → Bool => listToNat (samplePrimeL n (List.ofFn r))) =
      fun r => bitsToNat ((samplePrime n (2 * n ^ 2) (fac_chunkEquiv (2 * n ^ 2) n r)).getD
        (natToBits n 2)) := by
    funext r
    unfold samplePrimeL
    rw [padFin_ofFn, ← bitsToNat_eq_listToNat]
    rfl
  rw [hX, ← hY]
  exact h1.mono (fac_one_sub_pow_le_half_pow n hn)

/-- **Two independent runs of `SamplePrime(n)` are close to a uniform pair of distinct primes**
[PS10, Lemma 51.17 and Theorem 51.1, "sample two random prime numbers"]: for `n ≥ 2`, the
values of `samplePrimeL n` on the two halves of `2 · (2n² · n)` uniform coins are within
statistical distance `2 · (1/2)^n + 2n/2^n` of `(p, q)` for a uniform pair of distinct primes of
`Π_n`. Shared statement S2 of the factoring fill (decision D1 (A)): used by
`factoringCollection_sampleClose` and by `rsaCollection_invProbAt_le` (`RSA.lean`, step (ii)).

**Proof sketch.** Write `L = 2n² · n`. (1) The halves `(List.ofFn s).take L` and
`(List.ofFn s).drop L` are `List.ofFn` of the two halves of `s` under the splitting bijection
`(Fin (2L) → Bool) ≃ (Fin L → Bool) × (Fin L → Bool)` (`uprob_comp_equiv`), which pushes the
uniform coins to a uniform pair of independent halves. (2) On a half `r : Fin L → Bool`,
`padFin L (List.ofFn r) = r` (`padFin_ofFn`), and `chunk (2n²) n r` is `r` read through
`finProdFinEquiv` (`chunk_apply`), a bijection, so the blocks are uniform; and
`listToNat (List.ofFn b) = bitsToNat b` (`bitsToNat_eq_listToNat`). So each value is
`bitsToNat ((samplePrime n (2n²) xs).getD (natToBits n 2))` for uniform blocks `xs`. (3) The
fallback reads as the prime `2` (`bitsToNat_natToBits`, `2 < 2^n`, `Nat.prime_two`), so
`NumberTheory.statClose_samplePrime n (2n²)` applies to each run: within
`(1 − 1/(2n))^{2n²} ≤ (1/2)^n` (the bound of `uprob_samplePrime_none_le_two_pow`) of the
uniform `n`-bit prime, carried to `ℕ` by the injective `bitsToNat` (`StatClose.map`; the
uniform prime block is the uniform element of `Primes n`). (4) `StatClose.prod` puts the two
runs together: the pair is within `2 · (1/2)^n` of `(p, q)` for independent uniform
`p, q ∈ Π_n`. (5) That pair and `(z.p, z.q)` for a uniform `z : DistinctPrimes n` differ only on
the diagonal `p = q`, of probability `1/|Π_n|` (`uprob_diag`), at most `2n/2^n`
(`one_div_card_primes_le`); conclude by `StatClose.trans`. -/
theorem statClose_samplePrimeL_pair (n : ℕ) (hn : 2 ≤ n) :
    StatClose (fun s : Fin (2 * (2 * n ^ 2 * n)) → Bool =>
        (listToNat (samplePrimeL n ((List.ofFn s).take (2 * n ^ 2 * n))),
          listToNat (samplePrimeL n ((List.ofFn s).drop (2 * n ^ 2 * n)))))
      (fun z : DistinctPrimes n => (z.p, z.q))
      (2 * (1 / 2 : ℝ) ^ n + 2 * n / 2 ^ n) := by
  set L := 2 * n ^ 2 * n with hL
  let eS : (Fin L → Bool) × (Fin L → Bool) ≃ (Fin (2 * L) → Bool) :=
    (Fin.appendEquiv L L).trans (Equiv.arrowCongr (finCongr (two_mul L).symm) (Equiv.refl Bool))
  have hS : ∀ z, List.ofFn (eS z) = List.ofFn z.1 ++ List.ofFn z.2 := by
    rintro ⟨a, b⟩
    rw [← List.ofFn_fin_append]
    show List.ofFn (fun i => Fin.append a b (Fin.cast (two_mul L) i)) = _
    exact (List.ofFn_congr (two_mul L).symm (Fin.append a b)).symm
  have h1 := fac_statClose_samplePrimeL n hn
  have hp := ((h1.prod h1).comp_equiv_left eS.symm).trans (fac_statClose_diag n hn)
  have hX : (fun s : Fin (2 * L) → Bool =>
        (listToNat (samplePrimeL n ((List.ofFn s).take L)),
          listToNat (samplePrimeL n ((List.ofFn s).drop L)))) =
      fun s => (listToNat (samplePrimeL n (List.ofFn (eS.symm s).1)),
        listToNat (samplePrimeL n (List.ofFn (eS.symm s).2))) := by
    funext s
    have hs : List.ofFn s = List.ofFn (eS.symm s).1 ++ List.ofFn (eS.symm s).2 := by
      rw [← hS, Equiv.apply_symm_apply]
    rw [hs, List.take_left' (List.length_ofFn), List.drop_left' (List.length_ofFn)]
  rw [hX]
  exact hp.mono (by linarith)

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
  · exact ⟨⟨(⟨⟨listToNat a, h.2.2.2.1⟩, h.1⟩, ⟨⟨listToNat b, h.2.2.2.2⟩, h.2.1⟩), h.2.2.1⟩,
      by rw [encodeDistinctPrimes_eq, DistinctPrimes.p_eq, DistinctPrimes.q_eq]⟩
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

/-- A two-bit value `v`, read from the word `w`, as a `k`-bit numeral (`k ≥ 2`):
`natToList k v = (0^k).drop 2 ++ w`. -/
private theorem fac_natToList_small {k v : ℕ} (hk : 2 ≤ k) {w : List Bool} (hw : w.length = 2)
    (hv : listToNat w = v) : natToList k v = (List.replicate k false).drop 2 ++ w := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rw [← hv, ← hw, fac_natToList_lead, List.drop_replicate, hw]
  rfl

/-- The default pair `⟨2, 3⟩` at width `max n 2`: `⟨(0^n).drop 2 ++ 10, (0^n).drop 2 ++ 11⟩`. -/
private theorem fac_encode_default (n : ℕ) :
    encodeDistinctPrimes (max n 2) (DistinctPrimes.default (le_max_right n 2)) =
      pairEncode ((List.replicate n false).drop 2 ++ [true, false])
        ((List.replicate n false).drop 2 ++ [true, true]) := by
  have hd : (List.replicate (max n 2) false).drop 2 = (List.replicate n false).drop 2 := by
    rw [List.drop_replicate, List.drop_replicate]
    congr 1
    omega
  rw [encodeDistinctPrimes_eq, DistinctPrimes.default_p, DistinctPrimes.default_q,
    fac_natToList_small (w := [true, false]) (le_max_right n 2) rfl (by rw [listToNat_eq]; rfl),
    fac_natToList_small (w := [true, true]) (le_max_right n 2) rfl (by rw [listToNat_eq]; rfl), hd]

/-- Words of the same length are equal iff they read as the same number. -/
private theorem fac_listToNat_inj {a b : List Bool} (h : a.length = b.length) :
    listToNat a = listToNat b ↔ a = b := by
  constructor
  · intro hab
    rw [← natToList_length_listToNat a, ← natToList_length_listToNat b, hab, h]
  · rintro rfl; rfl

/-- `samplePrimeL n r` has `n` bits. -/
private theorem fac_length_samplePrimeL (n : ℕ) (r : List Bool) : (samplePrimeL n r).length = n := by
  unfold samplePrimeL
  rw [List.length_ofFn]

/-- **The sampler is polynomial-time** [PS10, Lemma 51.17] given a primality test: two
runs of the `SamplePrime` loop.

**Proof sketch.** Cut the coins at the unary length `1^{2n³}` (`polyTimeComputable_pairTakePoly`
/`_pairDropPoly samplePrimeCoins` on `⟨1^n, r⟩`); each half `a`, `b` is one run of `SamplePrime(n)`
by the shared statement S1 (`polyTimeComputable_samplePrimeL`), an `n`-bit word. The acceptance
test of `samplePairOut` uses `hP` only (this theorem has no `ArithmeticFP` argument): the two
prime tests are `hP`, and the inequality of the two values is tested by comparing the two
`n`-bit words directly (`polyTimeComputable_pairEq`, negated: words of equal length have equal
values iff they are equal, `natToList_length_listToNat`); the two range checks
`< 2^{max n 2}` are discharged from the widths, not computed (`listToNat_lt_two_pow`); the
branch is `polyTimeComputable_ite`. On acceptance `n ≥ 2` (a prime read from an `n`-bit word
forces `2 ≤ value < 2^n`), so `max n 2 = n` and the `n`-bit numerals of the two values are the
words themselves: the accepted output is `⟨a, b⟩`, no padding is needed. The default pair
`⟨2, 3⟩` at width `max n 2` is `⟨(0^n).drop 2 ++ 10, (0^n).drop 2 ++ 11⟩` for every `n`
(`encodeDistinctPrimes_eq`, `default_p`/`default_q`, leading zeros by
`natToList_length_listToNat`; `(0^{max n 2}).drop 2 = (0^n).drop 2`), so no branch on `n < 2`
is needed: `polyTimeComputable_zerosPoly`, `polyTimeComputable_pairDropPoly (const 2)` and
`PolyTimeComputable.append`; pair the results (`PolyTimeComputable.pairEncode`). -/
theorem polyTimeComputable_samplePairRaw (hP : PolyTimeComputable primeStr) :
    PolyTimeComputable samplePairRaw := by
  have hS1 := polyTimeComputable_samplePrimeL hP
  have hpc := NUPPT.polyTimeComputable_inParam.pairEncode NUPPT.polyTimeComputable_inCoins
  have ha : PolyTimeComputable fun z => samplePrimeL (NUPPT.inParam z).length
      ((NUPPT.inCoins z).take (2 * (NUPPT.inParam z).length ^ 2 * (NUPPT.inParam z).length)) := by
    have h := hS1.comp (NUPPT.polyTimeComputable_inParam.pairEncode
      ((polyTimeComputable_pairTakePoly samplePrimeCoins).comp hpc))
    simpa only [Function.comp_def, pairFstD_pairEncode, pairSndD_pairEncode,
      eval_samplePrimeCoins] using h
  have hb : PolyTimeComputable fun z => samplePrimeL (NUPPT.inParam z).length
      ((NUPPT.inCoins z).drop (2 * (NUPPT.inParam z).length ^ 2 * (NUPPT.inParam z).length)) := by
    have h := hS1.comp (NUPPT.polyTimeComputable_inParam.pairEncode
      ((polyTimeComputable_pairDropPoly samplePrimeCoins).comp hpc))
    simpa only [Function.comp_def, pairFstD_pairEncode, pairSndD_pairEncode,
      eval_samplePrimeCoins] using h
  have hpr := primeStr_eq ▸ hP
  have hpa := hpr.comp ha
  have hpb := hpr.comp hb
  have hne := polyTimeComputable_not (polyTimeComputable_pairEq.comp (ha.pairEncode hb))
  simp only [Function.comp_def, pairFstD_pairEncode, pairSndD_pairEncode] at hpa hpb hne
  have htest := polyTimeComputable_and hpa (polyTimeComputable_and hpb hne)
  have hz : PolyTimeComputable fun z =>
      (List.replicate (NUPPT.inParam z).length false).drop 2 := by
    have h := (polyTimeComputable_pairDropPoly (.const 2)).comp ((polyTimeComputable_const []).pairEncode
      ((polyTimeComputable_zerosPoly .var).comp
        (NUPPT.polyTimeComputable_inParam.pairEncode (polyTimeComputable_const []))))
    simpa only [Function.comp_def, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_const,
      PolyExpr.eval_var] using h
  have hdef := (hz.append (polyTimeComputable_const [true, false])).pairEncode
    (hz.append (polyTimeComputable_const [true, true]))
  have h := polyTimeComputable_ite htest (ha.pairEncode hb) hdef
  convert h using 1
  funext z
  unfold samplePairRaw samplePairOut
  rw [fac_encode_default]
  set n := (NUPPT.inParam z).length
  set a := samplePrimeL n ((NUPPT.inCoins z).take (2 * n ^ 2 * n))
  set b := samplePrimeL n ((NUPPT.inCoins z).drop (2 * n ^ 2 * n))
  have hla : a.length = n := fac_length_samplePrimeL _ _
  have hlb : b.length = n := fac_length_samplePrimeL _ _
  have hlta : listToNat a < 2 ^ max n 2 :=
    (listToNat_lt_two_pow a).trans_le (Nat.pow_le_pow_right (by norm_num) (hla ▸ le_max_left _ _))
  have hltb : listToNat b < 2 ^ max n 2 :=
    (listToNat_lt_two_pow b).trans_le (Nat.pow_le_pow_right (by norm_num) (hlb ▸ le_max_left _ _))
  have hiff : listToNat a ≠ listToNat b ↔ a ≠ b := (fac_listToNat_inj (hla.trans hlb.symm)).not
  by_cases hc : (listToNat a).Prime ∧ (listToNat b).Prime ∧ a ≠ b
  · have hn : 2 ≤ n := by
      by_contra hn
      have h2 : 2 ^ n ≤ 2 := by
        calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 2 := rfl
      have := listToNat_lt_two_pow a
      rw [hla] at this
      exact absurd hc.1.two_le (by omega)
    rw [if_pos ⟨hc.1, hc.2.1, hiff.2 hc.2.2, hlta, hltb⟩, if_pos (by simp [hc.1, hc.2.1, hc.2.2])]
    have hm : max n 2 = n := max_eq_left hn
    rw [hm]
    conv_lhs => rw [← hla, natToList_length_listToNat, hla, ← hlb, natToList_length_listToNat]
  · rw [if_neg (fun h' => hc ⟨h'.1, h'.2.1, hiff.1 h'.2.2.1⟩), if_neg]
    simpa only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      using hc

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
  simp [NUPPT.inParam_eq, NUPPT.advInput_eq]

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
  simp [samplePairRaw, NUPPT.inParam_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq]

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
  simp only [encodeDistinctPrimes_eq]
  rw [mulStr_natToList _ _ _ _ z.p_lt z.q_lt, two_mul]

/-- **The factoring collection** [PS10, Theorem 51.1]: indices `1^n` (`Gen(1^n) = ⟨1^n, []⟩`,
no coins, `factoringGen`), domains `D_{1^n} = {(p, q) ∈ Π_n × Π_n : p ≠ q}` encoded as `⟨p, q⟩`
with `n`-bit numerals, `f(p, q) = pq` as a `2n`-bit numeral, the sampler `factoringSampler`
(whose outputs always decode, `factoringSampler_spec`) and the evaluator `mulStr` of the
arithmetic bundle; decoding is canonical (`encodeDistinctPrimes_of_decode`).

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
  encD_decD _ _ _ h := encodeDistinctPrimes_of_decode h
  f i z := natToList (2 * max i.length 2) (z.p * z.q)
  gen := factoringGen
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  sample := factoringSampler H
  sample_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  eval z := mulStr (pairSndD z)
  eval_poly := H.mul.comp polyTimeComputable_pairSndD
  eval_spec i z := by
    simp only [pairSndD_pairEncode, encodeDistinctPrimes_eq]
    rw [mulStr_natToList _ _ _ _ z.p_lt z.q_lt, two_mul]
  sample_spec := factoringSampler_spec H

/-- **The domain of the factoring collection is `DistinctPrimes (max |i| 2)`**: the published
equivalence `(factoringCollection H).D i ≃ DistinctPrimes (max i.length 2)` (the identity). It is
the interface to the domain: elements of `D i` are read through it (`factoringCollection_f`,
`factoringCollection_encD`, `factoringCollection_decD`), so no statement needs the collection to
reduce at the type level, and uniform statements over `D i` transport along it
(`uprob_comp_equiv`, `StatClose.comp_equiv_right`). -/
def factoringCollection_domEquiv (H : ArithmeticFP) (i : List Bool) :
    (factoringCollection H).D i ≃ DistinctPrimes (max i.length 2) :=
  Equiv.refl _

/-- **The domain equivalence carries the uniform distribution**: for `P` on
`DistinctPrimes (max |i| 2)`, `Pr_{x ← D i}[P (φ x)] = Pr_y[P y]` with
`φ = factoringCollection_domEquiv H i` (`uprob_comp_equiv`), the form in which uniform
statements over the domain are read. -/
theorem factoringCollection_domEquiv_uprob (H : ArithmeticFP) (i : List Bool)
    (P : DistinctPrimes (max i.length 2) → Prop) :
    uprob (fun x : (factoringCollection H).D i => P (factoringCollection_domEquiv H i x)) =
      uprob P :=
  uprob_comp_equiv _ P

/-- The function of the factoring collection, read through the domain equivalence: with
`z = factoringCollection_domEquiv H i x`,
`(factoringCollection H).f i x = ⟦z.p · z.q⟧_{2 max |i| 2}`. -/
theorem factoringCollection_f (H : ArithmeticFP) (i : List Bool) (x : (factoringCollection H).D i) :
    (factoringCollection H).f i x = natToList (2 * max i.length 2)
      ((factoringCollection_domEquiv H i x).p * (factoringCollection_domEquiv H i x).q) := rfl

/-- The encoder of the factoring collection is `encodeDistinctPrimes`, read through the domain
equivalence: `(factoringCollection H).encD i x = encodeDistinctPrimes (max |i| 2) z` with
`z = factoringCollection_domEquiv H i x`. -/
theorem factoringCollection_encD (H : ArithmeticFP) (i : List Bool)
    (x : (factoringCollection H).D i) :
    (factoringCollection H).encD i x =
      encodeDistinctPrimes (max i.length 2) (factoringCollection_domEquiv H i x) := rfl

/-- The decoder of the factoring collection is `decodeDistinctPrimes`, carried back along the
domain equivalence: `(factoringCollection H).decD i w =
(decodeDistinctPrimes (max i.length 2) w).map (factoringCollection_domEquiv H i).symm`. -/
theorem factoringCollection_decD (H : ArithmeticFP) (i w : List Bool) :
    (factoringCollection H).decD i w =
      (decodeDistinctPrimes (max i.length 2) w).map (factoringCollection_domEquiv H i).symm := by
  show decodeDistinctPrimes (max i.length 2) w = _
  cases decodeDistinctPrimes (max i.length 2) w <;> rfl

/-- The index generator of the factoring collection is `factoringGen`. -/
theorem factoringCollection_gen (H : ArithmeticFP) : (factoringCollection H).gen = factoringGen :=
  rfl

/-- The domain sampler of the factoring collection is `factoringSampler H`. -/
theorem factoringCollection_sample (H : ArithmeticFP) :
    (factoringCollection H).sample = factoringSampler H := rfl

/-- The evaluator of the factoring collection is multiplication on the second component:
`(factoringCollection H).eval z = mulStr (pairSndD z)`. -/
theorem factoringCollection_eval (H : ArithmeticFP) (z : List Bool) :
    (factoringCollection H).eval z = mulStr (pairSndD z) := rfl

/-- The index generated by the factoring collection is `1^n`. -/
theorem factoringCollection_index (H : ArithmeticFP) (n : ℕ)
    (r : (factoringCollection H).gen.Coins n) :
    (factoringCollection H).index n r = List.replicate n true := by
  rw [Collection.index_eq]
  exact (congrArg pairFstD (factoringGen_runAt n r)).trans (pairFstD_pairEncode _ _)

/-- The decoded pair read from two numbers: the pair itself when they are distinct primes below
`2^n`, the default pair otherwise. -/
private noncomputable def fac_pairDec (n : ℕ) (hn : 2 ≤ n) (v : ℕ × ℕ) : Option (DistinctPrimes n) :=
  if h : v.1.Prime ∧ v.2.Prime ∧ v.1 ≠ v.2 ∧ v.1 < 2 ^ n ∧ v.2 < 2 ^ n then
    some ⟨(⟨⟨v.1, h.2.2.2.1⟩, h.1⟩, ⟨⟨v.2, h.2.2.2.2⟩, h.2.1⟩), h.2.2.1⟩
  else some (DistinctPrimes.default hn)

/-- Decoding the sampler's output: `decodeDistinctPrimes n (samplePairOut n hn a b)` is
`fac_pairDec` of the two numbers read from `a` and `b`. -/
private theorem fac_decode_samplePairOut (n : ℕ) (hn : 2 ≤ n) (a b : List Bool) :
    decodeDistinctPrimes n (samplePairOut n hn a b) = fac_pairDec n hn (listToNat a, listToNat b) := by
  unfold samplePairOut fac_pairDec
  split_ifs with h
  · rw [← decodeDistinctPrimes_encode n ⟨(⟨⟨listToNat a, h.2.2.2.1⟩, h.1⟩,
      ⟨⟨listToNat b, h.2.2.2.2⟩, h.2.1⟩), h.2.2.1⟩, encodeDistinctPrimes_eq,
      DistinctPrimes.p_eq, DistinctPrimes.q_eq]
  · exact decodeDistinctPrimes_encode n _

/-- `fac_pairDec` returns a pair of distinct primes on its own values. -/
private theorem fac_pairDec_pq (n : ℕ) (hn : 2 ≤ n) (z : DistinctPrimes n) :
    fac_pairDec n hn (z.p, z.q) = some z := by
  unfold fac_pairDec
  rw [dif_pos ⟨z.p_prime, z.q_prime, z.p_ne_q, z.p_lt, z.q_lt⟩]
  exact congrArg some (DistinctPrimes.ext (by rw [DistinctPrimes.p_eq]) (by rw [DistinctPrimes.q_eq]))

/-- **The decoded sampler output is close to uniform** (S2 mapped through `fac_pairDec`), stated
for a width `m = n` so that it applies at `m = max n 2`. -/
private theorem fac_statClose_decode (n m : ℕ) (hm : 2 ≤ m) (hmn : m = n) :
    StatClose (fun s : Fin (2 * (2 * n ^ 2 * n)) → Bool =>
        decodeDistinctPrimes m (samplePairOut m hm
          (samplePrimeL n ((List.ofFn s).take (2 * n ^ 2 * n)))
          (samplePrimeL n ((List.ofFn s).drop (2 * n ^ 2 * n)))))
      (fun z : DistinctPrimes m => some z) (2 * (1 / 2 : ℝ) ^ n + 2 * n / 2 ^ n) := by
  subst hmn
  have h := (statClose_samplePrimeL_pair m hm).map (fac_pairDec m hm)
  simp only [fac_pairDec_pq] at h
  simpa only [fac_decode_samplePairOut] using h

/-- The closeness bound of the factoring sampler, `1` for `n < 2` and `2(1/2)^n + 2n/2^n`
otherwise, is negligible (`negligible_two_pow_neg`, `Negligible.mul_pow`, `Negligible.add`). -/
private theorem fac_negligible_delta :
    Negligible fun n : ℕ => if n < 2 then (1 : ℝ) else 2 * (1 / 2 : ℝ) ^ n + 2 * n / 2 ^ n := by
  have h := (negligible_two_pow_neg.const_mul 2).add ((negligible_two_pow_neg.mul_pow 1).const_mul 2)
  refine h.mono ⟨2, fun n hn => ?_⟩
  rw [if_neg (by omega)]
  apply le_of_eq
  congr 1
  rw [pow_one, inv_pow, one_div_pow, one_div]
  ring

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
  refine ⟨_, fac_negligible_delta, ?_⟩
  rw [Collection.sampleClose_iff]
  intro n r
  by_cases hn : n < 2
  · rw [if_pos hn, statClose_iff]
    intro T
    rw [abs_sub_le_iff]
    constructor <;> linarith [uprob_nonneg (fun s : (factoringCollection H).sample.Coins n =>
      T ((factoringCollection H).decD ((factoringCollection H).index n r)
        ((factoringCollection H).sample.runAt n ((factoringCollection H).index n r) s))),
      uprob_le_one (fun s : (factoringCollection H).sample.Coins n =>
      T ((factoringCollection H).decD ((factoringCollection H).index n r)
        ((factoringCollection H).sample.runAt n ((factoringCollection H).index n r) s))),
      uprob_nonneg (fun x : (factoringCollection H).D ((factoringCollection H).index n r) => T (some x)),
      uprob_le_one (fun x : (factoringCollection H).D ((factoringCollection H).index n r) => T (some x))]
  rw [if_neg hn]
  push_neg at hn
  have hlen : ((factoringCollection H).index n r).length = n := by
    rw [factoringCollection_index, List.length_replicate]
  generalize (factoringCollection H).index n r = i at hlen ⊢
  subst hlen
  have hc : (factoringSampler H).coinLen i.length = 2 * (2 * i.length ^ 2 * i.length) := by
    rw [NUPPT.coinLen_eq]
    unfold factoringSampler
    rw [NUPPT.coins_ofPolyTimeUniform, PolyExpr.eval_mul, PolyExpr.eval_const, eval_samplePrimeCoins]
  rw [factoringCollection_sample]
  have h1 := (fac_statClose_decode i.length (max i.length 2) (le_max_right _ _)
    (max_eq_left hn)).map (Option.map (factoringCollection_domEquiv H i).symm)
  have h2 := (h1.comp_equiv_left
    (Equiv.arrowCongr (finCongr hc) (Equiv.refl Bool))).comp_equiv_right
      (factoringCollection_domEquiv H i)
  have hofn : ∀ s, List.ofFn (Equiv.arrowCongr (finCongr hc) (Equiv.refl Bool) s) = List.ofFn s :=
    fun s => (List.ofFn_congr hc s).symm
  simp only [Option.map_some, Equiv.symm_apply_apply] at h2
  convert h2 using 1
  · funext s
    rw [factoringCollection_decD, factoringSampler_runAt, hofn]

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
@[simp] theorem coins_collectionFactorer (A : NUPPT) :
    (collectionFactorer A).coins = A.coins := by
  unfold collectionFactorer
  exact NUPPT.coins_ofPolyTime _ _ _ _ _

/-- **The reduction runs on the coins of `A`**: the published equivalence
`(collectionFactorer A).Coins n ≃ A.Coins n` (`NUPPT.coinsCongr` along
`coins_collectionFactorer`). -/
noncomputable def collectionFactorer_coinsEquiv (A : NUPPT) (n : ℕ) :
    (collectionFactorer A).Coins n ≃ A.Coins n :=
  NUPPT.coinsCongr (coins_collectionFactorer A) n

/-- The coin equivalence keeps the coin string:
`List.ofFn (collectionFactorer_coinsEquiv A n r) = List.ofFn r`. -/
theorem collectionFactorer_coinsEquiv_ofFn (A : NUPPT) (n : ℕ)
    (r : (collectionFactorer A).Coins n) :
    List.ofFn (collectionFactorer_coinsEquiv A n r) = List.ofFn r :=
  NUPPT.coinsCongr_ofFn (coins_collectionFactorer A) n r

/-- **The activation of the reduction**: `A_fact(1^n, y; r) = fst(A(1^n, ⟨1^n, y⟩; φ r))`, the
coins read through `φ = collectionFactorer_coinsEquiv A n`. -/
theorem collectionFactorer_runAt (A : NUPPT) (n : ℕ) (y : List Bool)
    (r : (collectionFactorer A).Coins n) :
    (collectionFactorer A).runAt n y r =
      pairFstD (A.runAt n (pairEncode (List.replicate n true) y)
        (collectionFactorer_coinsEquiv A n r)) := by
  rw [NUPPT.runAt_eq, collectionFactorer_coinsEquiv, NUPPT.runAt_coinsCongr]
  unfold collectionFactorer
  rw [NUPPT.runAtL_ofPolyTime]
  simp only [NUPPT.runAtL_eq, NUPPT.layout_eq, NUPPT.inParam_eq, NUPPT.inArg_eq,
    NUPPT.inAdvice_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq, pairFstD_pairEncode,
    pairSndD_pairEncode]

/-- `f_mult` on a pair of distinct primes is their product (neither is `1`). -/
private theorem fac_fmultNat_pq {n : ℕ} (w : DistinctPrimes n) : fmultNat w.p w.q = w.p * w.q :=
  fac_fmultNat_of_prime w.p_prime w.q_prime

/-- **The reduction at a width `m = n`**: if `A`'s answer on `⟨1^n, ⟨pq⟩_{2m}⟩` decodes to a pair
of distinct primes with the same product, then `collectionFactorer A` factors `pq`; stated for a
width `m = n` so that it applies at `m = max n 2`. -/
private theorem fac_invProb_le (A : NUPPT) (n m : ℕ) (hmn : m = n) :
    uprob (fun z : DistinctPrimes m × A.Coins n => ∃ w : DistinctPrimes m,
        decodeDistinctPrimes m (A.runAt n (pairEncode (List.replicate n true)
          (natToList (2 * m) (z.1.p * z.1.q))) z.2) = some w ∧
        natToList (2 * m) (w.p * w.q) = natToList (2 * m) (z.1.p * z.1.q)) ≤
      factorProb (collectionFactorer A) n := by
  subst hmn
  rw [factorProb_eq]
  refine le_trans (uprob_mono ?_) (le_of_eq (uprob_comp_equiv (Equiv.prodCongr
    (Equiv.refl (DistinctPrimes m)) (collectionFactorer_coinsEquiv A m).symm) _))
  rintro ⟨z, r⟩ ⟨w, hdec, hmul⟩
  simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id_eq]
  have hpq : w.p * w.q = z.p * z.q := natToList_injOn w.mul_lt z.mul_lt hmul
  have hfac : w.p = z.p ∨ w.p = z.q :=
    fmultNat_eq_mul_prime z.p_prime z.q_prime ((fac_fmultNat_pq w).trans hpq)
  refine ⟨natToBits m w.p, ?_, by rwa [bitsToNat_natToBits w.p_lt]⟩
  rw [NUPPT.inverter_eq_some_iff, collectionFactorer_runAt, Equiv.apply_symm_apply, modulusBits_eq,
    ← natToList_eq, ← natToList_eq, ← encodeDistinctPrimes_of_decode hdec, encodeDistinctPrimes_eq,
    pairFstD_pairEncode]

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
`uprob_mono` with the coin types identified (`collectionFactorer_coinsEquiv`,
`uprob_comp_equiv`). -/
theorem factoringCollection_invProbAt_le (H : ArithmeticFP) (A : NUPPT) {n : ℕ} (hn : 2 ≤ n) :
    (factoringCollection H).invProbAt A n ≤ factorProb (collectionFactorer A) n := by
  haveI : Nonempty ((factoringCollection H).gen.Coins n) := ⟨fun _ => false⟩
  rw [Collection.invProbAt_eq]
  refine (OneWay.uexp_mono fun r => ?_).trans (OneWay.uexp_const _).le
  generalize hi : (factoringCollection H).index n r = i
  rw [factoringCollection_index] at hi
  subst hi
  have hm : max (List.replicate n true).length 2 = n := by
    rw [List.length_replicate]; exact max_eq_left hn
  refine le_trans (le_of_eq ?_) (fac_invProb_le A n _ hm)
  refine (OneWay.uprob_congr ?_).trans (uprob_comp_equiv (Equiv.prodCongr
    (factoringCollection_domEquiv H (List.replicate n true)) (Equiv.refl (A.Coins n))) _)
  rintro ⟨x, r⟩
  simp only [Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id_eq]
  rw [factoringCollection_f, factoringCollection_decD]
  constructor
  · rintro ⟨x', hx', hf⟩
    rw [Option.map_eq_some_iff] at hx'
    obtain ⟨w, hw, rfl⟩ := hx'
    refine ⟨w, hw, ?_⟩
    rw [factoringCollection_f, Equiv.apply_symm_apply] at hf
    exact hf
  · rintro ⟨w, hw, hf⟩
    refine ⟨(factoringCollection_domEquiv H _).symm w, by rw [hw, Option.map_some], ?_⟩
    rw [factoringCollection_f, Equiv.apply_symm_apply]
    exact hf

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
  refine ⟨factoringCollection_sampleClose H, fun A => ?_⟩
  refine ((factoringAssumption_iff.1 hF) (collectionFactorer A)).mono ⟨2, fun n hn => ?_⟩
  rw [abs_of_nonneg (Collection.invProbAt_nonneg _ _ _), abs_of_nonneg (factorProb_nonneg _ _)]
  exact factoringCollection_invProbAt_le H A hn

end TCSlib.Cryptography.Candidates
