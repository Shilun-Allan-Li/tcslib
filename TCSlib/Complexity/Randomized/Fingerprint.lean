/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.PrimeCounting
import TCSlib.Complexity.Randomized.AlgCircuit
import TCSlib.Complexity.Randomized.RandomBits
import TCSlib.Complexity.Randomized.SchwartzZippel

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fingerprinting and the randomized test for ZEROP

The polynomial identity testing algorithm of [AB09, §7.2.3, p.130]: evaluate the circuit at
a random point modulo random numbers `k`, and accept iff every residue is `0`.  Circuits
in `ZEROP` are always accepted; others are rejected with probability at least `2/3`.

## Main definitions

* `Randomized.AlgCircuit.zeroTest` — the test, on a random string.
* `Randomized.zeropVerifier` — the test as a verifier for `ZEROPᶜ` on encoded circuits.

## Main results

* `Randomized.two_pow_le_mul_primeCounting` — Chebyshev: `2^L ≤ L·(π(2^L) + 1)`.
* `Randomized.fingerprint` — `k ∈ [2^{2M}]`, `0 < |y| ≤ 2^{5M·2^M}`: `Pr[k ∤ y] ≥ 1/(4M)`.
* `Randomized.AlgCircuit.prob_eval_ne_zero` — a random point is a nonzero of `C`
  with probability `≥ 15/16` (Schwartz–Zippel).
* `Randomized.AlgCircuit.zeroTest_of_toMvPolynomial_eq_zero`,
  `Randomized.AlgCircuit.zeroTest_sound` — one-sided error `≤ 1/3`.
* `Randomized.inCoRP_ZEROP` — `ZEROP ∈ coRP` for any verifier model in which
  `zeropVerifier` is efficient.

## Divergences

* Inputs are drawn from `[2^{m+4}]` instead of `[10·2^m]`, so each costs exactly `m+4` fair
  coins; Schwartz–Zippel then gives `15/16` instead of `9/10`.
* The book proves the fingerprint bound "for sufficiently large `m`" from the Prime Number
  Theorem.  `fingerprint` proves it for `M ≥ 12` from an elementary Chebyshev bound
  (via the central binomial coefficient), under the book's `log y ≤ 5M·2^M`.
* So that this bound applies for every size `m`, the test uses `M = m + 12` (moduli from
  `[2^{2M}]`; values satisfy `|y| ≤ 2^{(m+4)2^m} ≤ 2^{5M·2^M}`) and `8M` moduli at one
  random point (the book's "repeat `O(1/δ)` times"); error `≤ 1 − (15/16)(3/4) < 1/3`.
* `inCoRP_ZEROP` takes the efficiency of `zeropVerifier` as a hypothesis; for
  `Randomized.polyTimeModel` it is `Randomized.eff_zeropVerifier`
  (`TCSlib.Complexity.Randomized.ZeroP`).
* Random bits are decoded by `Randomized.RandomBits` (`blockVal`, `randProb_blocks`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Finset
open Complexity.LogProg (bitsVal)

/-! ### A Chebyshev lower bound on the number of primes -/

/-- `4^n ≤ (2n)^{π(2n)+1}` for `n > 0`.

**Proof sketch.** `4^n ≤ 2n·C(2n, n)`, and `C(2n, n)` is the product over the primes
`p ≤ 2n` of `p^{e_p}` with `p^{e_p} ≤ 2n`, hence at most `(2n)^{π(2n)}`. -/
theorem four_pow_le_pow_primeCounting {n : ℕ} (hn : 0 < n) :
    4 ^ n ≤ (2 * n) ^ (Nat.primeCounting (2 * n) + 1) := by
  have hC : Nat.centralBinom n ≤ (2 * n) ^ Nat.primeCounting (2 * n) := by
    rw [← Nat.prod_pow_factorization_centralBinom n]
    calc ∏ p ∈ range (2 * n + 1), p ^ (Nat.centralBinom n).factorization p
        = ∏ p ∈ Nat.primesBelow (2 * n + 1), p ^ (Nat.centralBinom n).factorization p := by
          refine (Finset.prod_filter_of_ne fun p _ hp => ?_).symm
          by_contra h
          exact hp (by rw [Nat.factorization_eq_zero_of_not_prime _ h, pow_zero])
      _ ≤ ∏ _p ∈ Nat.primesBelow (2 * n + 1), 2 * n :=
          Finset.prod_le_prod' fun p _ => Nat.pow_factorization_choose_le (by omega)
      _ = (2 * n) ^ Nat.primeCounting (2 * n) := by
          rw [Finset.prod_const, Nat.primesBelow_card_eq_primeCounting']
          rfl
  calc 4 ^ n ≤ 2 * n * Nat.centralBinom n := Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
    _ ≤ 2 * n * (2 * n) ^ Nat.primeCounting (2 * n) := Nat.mul_le_mul_left _ hC
    _ = (2 * n) ^ (Nat.primeCounting (2 * n) + 1) := (pow_succ' _ _).symm

/-- **Chebyshev's bound** in base two: `2^L ≤ L·(π(2^L) + 1)` for `L ≥ 1`, i.e.
`π(N) ≥ N/log₂ N − 1` at `N = 2^L`.  (Used for [AB09, §7.2.3, p.130].) -/
theorem two_pow_le_mul_primeCounting {L : ℕ} (hL : 1 ≤ L) :
    2 ^ L ≤ L * (Nat.primeCounting (2 ^ L) + 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, L = k + 1 := ⟨L - 1, by omega⟩
  have h := four_pow_le_pow_primeCounting (n := 2 ^ k) (by positivity)
  rw [show 2 * 2 ^ k = 2 ^ (k + 1) by ring, ← pow_mul,
    show (4 : ℕ) ^ 2 ^ k = 2 ^ 2 ^ (k + 1) by rw [pow_succ, pow_mul']; norm_num] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

/-! ### The fingerprinting lemma -/

/-- A nonzero `k` has at most `log₂ k` distinct prime factors: `2^{ω(k)} ≤ k`. -/
theorem two_pow_card_primeFactors_le {k : ℕ} (hk : k ≠ 0) : 2 ^ #k.primeFactors ≤ k :=
  calc 2 ^ #k.primeFactors = ∏ _p ∈ k.primeFactors, 2 := (Finset.prod_const _).symm
    _ ≤ ∏ p ∈ k.primeFactors, p :=
        Finset.prod_le_prod' fun _ hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk) (Nat.prod_primeFactors_dvd k)

/-- At least `π(N) − B` numbers `k ∈ [N]` do not divide a nonzero `y` with `|y| ≤ 2^B`.

**Proof sketch.** `y` has at most `B` prime factors (`two_pow_card_primeFactors_le`); the
other primes `p ≤ N` do not divide `y`, and `p ↦ p − 1` injects them into the set counted. -/
theorem primeCounting_le_card_not_dvd {y : ℤ} (hy : y ≠ 0) {B : ℕ}
    (hyB : y.natAbs ≤ 2 ^ B) (N : ℕ) :
    Nat.primeCounting N ≤ #{v ∈ range N | ¬ ((v + 1 : ℕ) : ℤ) ∣ y} + B := by
  set P := Nat.primesBelow (N + 1)
  set F := y.natAbs.primeFactors
  have hy' : y.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hy
  have hP : #P = Nat.primeCounting N := Nat.primesBelow_card_eq_primeCounting' _
  have hF : #F ≤ B :=
    (Nat.pow_le_pow_iff_right (by norm_num)).mp ((two_pow_card_primeFactors_le hy').trans hyB)
  have hsd : #P ≤ #(P \ F) + #F := Finset.card_le_card_sdiff_add_card
  have hinj : #(P \ F) ≤ #{v ∈ range N | ¬ ((v + 1 : ℕ) : ℤ) ∣ y} := by
    refine Finset.card_le_card_of_injOn (fun p => p - 1) (fun p hp => ?_) (fun p hp q hq h => ?_)
    · simp only [P, F, Finset.mem_coe, mem_sdiff, Nat.mem_primesBelow, Nat.mem_primeFactors,
        not_and] at hp
      have h2 := hp.1.2.two_le
      simp only [Finset.mem_coe, mem_filter, mem_range]
      refine ⟨by omega, fun hd => ?_⟩
      rw [show p - 1 + 1 = p by omega, Int.natCast_dvd] at hd
      exact hp.2 hp.1.2 hd hy'
    · simp only [P, F, Finset.mem_coe, mem_sdiff, Nat.mem_primesBelow] at hp hq
      have := hp.1.2.two_le
      have := hq.1.2.two_le
      simp only at h
      omega
  omega

/-- `4M(1 + 5M·2^M) ≤ 4^M` for `M ≥ 12`. -/
theorem four_mul_le_four_pow {M : ℕ} (hM : 12 ≤ M) :
    4 * M * (1 + 5 * M * 2 ^ M) ≤ 2 ^ (2 * M) := by
  have h21 : 21 * M ^ 2 ≤ 2 ^ M := by
    induction M, hM using Nat.le_induction with
    | base => norm_num
    | succ M hM ih =>
      have h12 : 12 * M ≤ M * M := Nat.mul_le_mul_right M hM
      calc 21 * (M + 1) ^ 2 ≤ 2 * (21 * M ^ 2) := by nlinarith
        _ ≤ 2 * 2 ^ M := by omega
        _ = 2 ^ (M + 1) := by ring
  have hP : 1 ≤ 2 ^ M := Nat.one_le_two_pow
  rw [two_mul, pow_add]
  nlinarith [Nat.mul_le_mul_right (2 ^ M) h21]

/-- **Fingerprinting** [AB09, §7.2.3, p.130]: if `y ≠ 0` and `log₂|y| ≤ 5M·2^M`, then a
uniformly random `k ∈ [2^{2M}]` does not divide `y` with probability at least `1/(4M)`
(here for `M ≥ 12`; the book says "for sufficiently large `m`").

**Proof sketch.** At least `π(2^{2M}) − 5M·2^M` numbers in `[2^{2M}]` are primes not
dividing `y`; by Chebyshev `π(2^{2M}) ≥ 2^{2M}/(2M) − 1`, and `4M(1 + 5M·2^M) ≤ 2^{2M}`
leaves at least `2^{2M}/(4M)` of them. -/
theorem fingerprint {M : ℕ} (hM : 12 ≤ M) {y : ℤ} (hy : y ≠ 0)
    (hyB : y.natAbs ≤ 2 ^ (5 * M * 2 ^ M)) :
    1 / (4 * M : ℚ) ≤ randProb (2 * M) (fun r => ¬ ((bitsVal r + 1 : ℕ) : ℤ) ∣ y) := by
  have hb := randProb_bitsVal (2 * M) (fun v => ¬ ((v + 1 : ℕ) : ℤ) ∣ y)
  simp only at hb
  rw [hb]
  set c := #{v ∈ range (2 ^ (2 * M)) | ¬ ((v + 1 : ℕ) : ℤ) ∣ y}
  have h1 := two_pow_le_mul_primeCounting (L := 2 * M) (by omega)
  have h2 := primeCounting_le_card_not_dvd hy hyB (2 ^ (2 * M))
  have h3 := four_mul_le_four_pow hM
  have h4 : 2 * M * (Nat.primeCounting (2 ^ (2 * M)) + 1) ≤ 2 * M * (c + 5 * M * 2 ^ M + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have key : 2 ^ (2 * M) ≤ 4 * M * c := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  have : ((2 : ℚ) ^ (2 * M)) ≤ 4 * M * c := by exact_mod_cast key
  linarith

/-- [AB09, §7.2.3, p.130] amplified: `8M` independent `k`'s from `[2^{2M}]` all divide
`y ≠ 0` with probability at most `1/4`.

**Proof sketch.** The blocks are independent, so `Pr[all kⱼ ∣ y] = q^{8M}` with
`q = Pr[k ∣ y] ≤ 1 − 1/(4M)` by `fingerprint`, and `(1 − 1/(4M))^{8M} ≤ (1/2)^2 = 1/4`. -/
theorem prob_exists_not_dvd {M : ℕ} (hM : 12 ≤ M) {y : ℤ} (hy : y ≠ 0)
    (hyB : y.natAbs ≤ 2 ^ (5 * M * 2 ^ M)) :
    3 / 4 ≤ randProb (8 * M * (2 * M))
      (fun s => ¬ ∀ j : Fin (8 * M), ((blockVal (2 * M) s j + 1 : ℕ) : ℤ) ∣ y) := by
  have hfb := randProb_forall_blocks (8 * M) (2 * M) (fun v => ((v + 1 : ℕ) : ℤ) ∣ y)
  simp only at hfb
  rw [randProb_not, hfb]
  set q := randProb (2 * M) (fun r => ((bitsVal r + 1 : ℕ) : ℤ) ∣ y)
  have hq : q ≤ 1 - 1 / (4 * M : ℚ) := by
    have := fingerprint hM hy hyB
    rw [randProb_not] at this
    linarith
  have hM0 : (0 : ℚ) < M := by exact_mod_cast (show 0 < M by omega)
  have hδ0 : (0 : ℚ) ≤ 1 / (4 * M) := by positivity
  have hδ1 : 1 / (4 * M : ℚ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (12 : ℚ) ≤ M := by exact_mod_cast hM
    linarith
  have hpow := one_sub_pow_le_half_pow hδ0 hδ1 (m := 4 * M) (T := 2) (e := 8 * M)
    (by push_cast; field_simp; rfl) (by omega)
  have : q ^ (8 * M) ≤ (1 - 1 / (4 * M : ℚ)) ^ (8 * M) :=
    pow_le_pow_left₀ randProb_nonneg hq _
  linarith [show ((1 : ℚ) / 2) ^ 2 = 1 / 4 by norm_num]

/-! ### The randomized test for ZEROP -/

/-- Fair coins per input value: inputs are drawn from `[2^{m+4}]`. -/
def inputBits (m : ℕ) : ℕ := m + 4

/-- The fingerprint parameter `M = m + 12`: moduli are drawn from `[2^{2M}]`. -/
def modParam (m : ℕ) : ℕ := m + 12

/-- The number `8M` of moduli tried. -/
def numTrials (m : ℕ) : ℕ := 8 * modParam m

/-- The fair coins used by the test on an `n`-variable circuit of size `m`. -/
def testLen (n m : ℕ) : ℕ := n * inputBits m + numTrials m * (2 * modParam m)

namespace AlgCircuit

variable {n : ℕ}

/-- The random point: `aᵢ = 1 + (the i-th (m+4)-bit block of r)`, uniform in `[2^{m+4}]`. -/
def testPoint (C : AlgCircuit n) (r : List Bool) : Fin n → ℕ :=
  fun i => blockVal (inputBits C.size) r i + 1

/-- The `j`-th modulus: `1 + (the j-th 2M-bit block of s)`, uniform in `[2^{2M}]`. -/
def testModulus (C : AlgCircuit n) (s : List Bool) (j : ℕ) : ℕ :=
  blockVal (2 * modParam C.size) s j + 1

/-- The test on exactly `testLen` coins: for every trial `j`, `C(a) ≡ 0 (mod kⱼ)`, computed
by evaluating `C` in `ℤ/kⱼ`.  [AB09, §7.2.3, p.130] -/
def ZeroTestCore (C : AlgCircuit n) (r : List Bool) : Prop :=
  ∀ j : Fin (numTrials C.size),
    C.eval (fun i => (C.testPoint (r.take (n * inputBits C.size)) i :
      ZMod (C.testModulus (r.drop (n * inputBits C.size)) j))) = 0

instance (C : AlgCircuit n) : DecidablePred C.ZeroTestCore := fun r => by
  unfold ZeroTestCore
  infer_instance

/-- The ZEROP test of [AB09, §7.2.3, p.130] on a random string (extra bits ignored):
`true` = accept ("`C` computes zero"). -/
def zeroTest (C : AlgCircuit n) (r : List Bool) : Bool :=
  decide (C.ZeroTestCore (r.take (testLen n C.size)))

/-- Evaluating at natural numbers in `ℤ/k` is reducing the integer value mod `k`. -/
theorem eval_natCast_zmod (C : AlgCircuit n) (a : Fin n → ℕ) (k : ℕ) :
    C.eval (fun i => (a i : ZMod k)) = ((C.eval (fun i => (a i : ℤ)) : ℤ) : ZMod k) := by
  have h := map_eval (Int.castRingHom (ZMod k)) C (fun i => (a i : ℤ))
  simp only [eq_intCast] at h
  rw [h]
  congr 1
  funext i
  simp

/-- **Completeness**: a circuit computing the zero polynomial is always accepted. -/
theorem zeroTest_of_toMvPolynomial_eq_zero {C : AlgCircuit n} (h : C.toMvPolynomial = 0)
    (r : List Bool) : C.zeroTest r = true := by
  simp only [zeroTest, decide_eq_true_eq]
  intro j
  rw [← aeval_toMvPolynomial, h, map_zero]

/-- [AB09, §7.2.3, p.130] via Schwartz–Zippel (`Randomized.schwartz_zippel`): if `C` computes
a nonzero polynomial, its value at a uniformly random point of `[2^{m+4}]ⁿ` is nonzero with
probability at least `15/16`.

**Proof sketch.** The `n` blocks are `n` independent uniform values in `[0, 2^{m+4})`;
shifting by one is a bijection onto `Sⁿ` with `S = [1, 2^{m+4}]`, and Schwartz–Zippel with
degree `≤ 2^m` gives `1 − 2^m/2^{m+4} = 15/16`. -/
theorem prob_eval_ne_zero (C : AlgCircuit n) (h : C.toMvPolynomial ≠ 0) :
    15 / 16 ≤ randProb (n * inputBits C.size)
      (fun u => C.eval (fun i => (C.testPoint u i : ℤ)) ≠ 0) := by
  set b := inputBits C.size
  set S : Finset ℤ := Finset.Icc 1 (2 ^ b)
  have hS : #S = 2 ^ b := by
    simp only [S, Int.card_Icc, add_sub_cancel_right]
    exact_mod_cast Int.toNat_natCast (2 ^ b)
  have h2b : ((2 ^ b : ℕ) : ℤ) = 2 ^ b := by push_cast; rfl
  -- Schwartz–Zippel over `Sⁿ`, `S = [1, 2^{m+4}]`.
  have hsz := schwartz_zippel h (totalDegree_toMvPolynomial_le C) S
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, one_le_pow₀ (by norm_num)⟩⟩
  -- Shifting the block values by one is a bijection onto `Sⁿ`.
  have hbij : #{f : Fin n → Fin (2 ^ b) | C.eval (fun i => ((f i + 1 : ℕ) : ℤ)) ≠ 0} =
      #{g ∈ Fintype.piFinset fun _ : Fin n => S | MvPolynomial.eval g C.toMvPolynomial ≠ 0} := by
    refine Finset.card_bij (fun f _ i => ((f i : ℕ) : ℤ) + 1) ?_ ?_ ?_
    · intro f hf
      simp only [mem_filter, mem_univ, true_and] at hf
      simp only [mem_filter, Fintype.mem_piFinset, eval_toMvPolynomial, S, Finset.mem_Icc]
      refine ⟨fun i => ⟨by omega, ?_⟩, by simpa using hf⟩
      have := (f i).isLt
      exact_mod_cast this
    · intro f _ f' _ hff
      funext i
      exact Fin.ext (by simpa using congrFun hff i)
    · intro g hg
      simp only [mem_filter, Fintype.mem_piFinset, eval_toMvPolynomial, S,
        Finset.mem_Icc] at hg
      refine ⟨fun i => ⟨(g i - 1).toNat, ?_⟩, ?_, ?_⟩
      · have := (hg.1 i).2
        have := (hg.1 i).1
        have := Nat.one_le_two_pow (n := b)
        omega
      · simp only [mem_filter, mem_univ, true_and]
        convert hg.2 using 2
        funext i
        have := (hg.1 i).1
        push_cast
        omega
      · funext i
        have := (hg.1 i).1
        simp only
        omega
  -- `1 − 2^m/2^{m+4} = 15/16`.
  have hratio : (1 : ℚ≥0) - (2 ^ C.size : ℕ) / #S = 15 / 16 := by
    rw [hS, show b = C.size + 4 from rfl, pow_add]
    push_cast
    rw [div_mul_cancel_left₀ (pow_ne_zero _ two_ne_zero)]
    rw [tsub_eq_iff_eq_add_of_le (by exact_mod_cast (show (16 : ℚ)⁻¹ ≤ 1 by norm_num))]
    exact NNRat.coe_injective (by push_cast; norm_num)
  rw [hratio, hS] at hsz
  have hq := NNRat.coe_le_coe.mpr hsz
  push_cast at hq
  calc (15 / 16 : ℚ) ≤ _ := hq
    _ = #{f : Fin n → Fin (2 ^ b) | C.eval (fun i => ((f i + 1 : ℕ) : ℤ)) ≠ 0} /
          (2 ^ b) ^ n := by rw [hbij]
    _ = _ := (randProb_blocks n b (fun g => C.eval (fun i => ((g i + 1 : ℕ) : ℤ)) ≠ 0)).symm

/-- The test's integer values are below `2^{5M·2^M}`, `M = m + 12`: inputs are at most
`2^{m+4}`, so `|C(a)| ≤ 2^{(m+4)2^m}` by `abs_eval_le_pow`. -/
theorem natAbs_eval_testPoint_le (C : AlgCircuit n) (u : List Bool) :
    (C.eval (fun i => (C.testPoint u i : ℤ))).natAbs ≤
      2 ^ (5 * modParam C.size * 2 ^ modParam C.size) := by
  have hx : ∀ i, |((C.testPoint u i : ℕ) : ℤ)| ≤ ((2 ^ inputBits C.size : ℕ) : ℤ) := by
    intro i
    rw [Nat.abs_cast]
    exact_mod_cast blockVal_lt _ u i
  have h2 : 2 ≤ 2 ^ inputBits C.size := by
    simpa using Nat.pow_le_pow_right (n := 2) (by norm_num) (show 1 ≤ inputBits C.size by
      simp [inputBits])
  have h := abs_eval_le_pow C _ _ h2 hx
  rw [Int.abs_eq_natAbs] at h
  have h' : (C.eval (fun i => (C.testPoint u i : ℤ))).natAbs ≤
      2 ^ (inputBits C.size * 2 ^ C.size) := by
    rw [pow_mul]
    exact_mod_cast h
  refine h'.trans (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul ?_ ?_))
  · simp only [inputBits, modParam]
    omega
  · exact Nat.pow_le_pow_right (by norm_num) (by simp [modParam])

/-- **Soundness** [AB09, §7.2.3, p.130]: if `C` computes a nonzero polynomial, the test
rejects with probability at least `2/3`, on any string of at least `testLen` coins.

**Proof sketch.** Condition on the point `a` (`randProb_append_ge`): with probability
`≥ 15/16` the value `y = C(a)` is nonzero (`prob_eval_ne_zero`), and then `|y| ≤ 2^{5M·2^M}`,
so some of the `8M` moduli fails to divide `y` with probability `≥ 3/4`
(`prob_exists_not_dvd`); and `(15/16)(3/4) ≥ 2/3`. -/
theorem zeroTest_sound (C : AlgCircuit n) (h : C.toMvPolynomial ≠ 0) {N : ℕ}
    (hN : testLen n C.size ≤ N) : 2 / 3 ≤ randProb N (fun r => C.zeroTest r = false) := by
  have e1 : randProb N (fun r => C.zeroTest r = false) =
      randProb (testLen n C.size) (fun r => ¬ C.ZeroTestCore r) := by
    rw [← randProb_take hN]
    exact randProb_congr fun r => by simp [zeroTest]
  rw [e1]
  set y : List Bool → ℤ := fun u => C.eval (fun i => (C.testPoint u i : ℤ))
  have hsplit := randProb_append_ge (n * inputBits C.size) (numTrials C.size *
      (2 * modParam C.size)) (fun u => y u ≠ 0)
    (fun u s => ¬ ∀ j : Fin (numTrials C.size), ((blockVal (2 * modParam C.size) s j + 1 : ℕ) :
      ℤ) ∣ y u) (ε := 3 / 4)
    (fun u hu => prob_exists_not_dvd (by simp [modParam]) hu (natAbs_eval_testPoint_le C _))
  have hA := prob_eval_ne_zero C h
  calc (2 / 3 : ℚ) ≤ 15 / 16 * (3 / 4) := by norm_num
    _ ≤ randProb (n * inputBits C.size) (fun u => y u ≠ 0) * (3 / 4) := by gcongr
    _ ≤ _ := hsplit
    _ = _ := randProb_congr fun r => by
      simp only [ZeroTestCore, testModulus, eval_natCast_zmod, ZMod.intCast_zmod_eq_zero_iff_dvd,
        y, testPoint]

end AlgCircuit

/-! ### ZEROP ∈ coRP -/

/-- The verifier for `ZEROPᶜ`: decode the circuit; output `true` ("not in ZEROP") if the
input is not a well-formed circuit, and otherwise iff the test rejects. -/
def zeropVerifier (x r : List Bool) : Bool :=
  match AlgCircuit.decode x with
  | none => true
  | some c => if c.2.WellFormed then !(c.2.zeroTest r) else true

/-- The test's coins fit in `polyLen 2400 2 N` when `n, m ≤ N`. -/
theorem testLen_le_polyLen_of_le {n m N : ℕ} (h₁ : n ≤ N) (h₂ : m ≤ N) :
    testLen n m ≤ polyLen 2400 2 N := by
  simp only [testLen, inputBits, numTrials, modParam, polyLen]
  nlinarith [Nat.mul_le_mul h₁ (Nat.add_le_add_right h₂ 4), Nat.mul_le_mul h₂ h₂]

/-- The test's coins fit in `2400·(|x|+1)²` random bits. -/
theorem testLen_le_polyLen (c : (n : ℕ) × AlgCircuit n) :
    testLen c.1 c.2.size ≤ polyLen 2400 2 (AlgCircuit.encode c).length := by
  have h := AlgCircuit.lt_length_encode c
  exact testLen_le_polyLen_of_le (by omega) (by omega)

/-- The one-sided error profile of `zeropVerifier` [AB09, §7.2.3]: inputs outside `ZEROP`
are certified with probability `≥ 2/3`; inputs in `ZEROP` never are.

**Proof sketch.** A string that does not decode to a well-formed circuit is certified
always.  For a well-formed circuit `C` the verifier outputs the negated test, so
completeness and soundness of the test give the two clauses; the test's coins fit in
`polyLen 2400 2 |x|` (`testLen_le_polyLen`). -/
theorem zeropVerifier_spec (x : List Bool) :
    (x ∉ ZEROP → 2 / 3 ≤ randProb (polyLen 2400 2 x.length)
      (fun r => zeropVerifier x r = true)) ∧
    (x ∈ ZEROP → ∀ r : Fin (polyLen 2400 2 x.length) → Bool,
      zeropVerifier x (List.ofFn r) = false) := by
  constructor
  · intro hx
    cases hd : AlgCircuit.decode x with
    | none =>
      rw [randProb_congr (B := fun _ => True) fun r => by
        unfold zeropVerifier; rw [hd]; exact iff_of_true rfl trivial, randProb_true]
      norm_num
    | some c =>
      by_cases hw : c.2.WellFormed
      · have hz : c.2.toMvPolynomial ≠ 0 := fun hz =>
          hx ((mem_ZEROP_iff x).mpr ⟨c, hd, hw, hz⟩)
        have hlen := testLen_le_polyLen c
        rw [AlgCircuit.encode_of_decode hd] at hlen
        rw [randProb_congr (B := fun r => c.2.zeroTest r = false) fun r => by
          unfold zeropVerifier; rw [hd]; dsimp only; rw [if_pos hw]
          generalize c.2.zeroTest (List.ofFn r) = t
          cases t <;> decide]
        exact AlgCircuit.zeroTest_sound c.2 hz hlen
      · rw [randProb_congr (B := fun _ => True) fun r => by
          unfold zeropVerifier; rw [hd]; dsimp only; rw [if_neg hw]
          exact iff_of_true rfl trivial, randProb_true]
        norm_num
  · intro hx r
    obtain ⟨c, hd, hw, hz⟩ := (mem_ZEROP_iff x).mp hx
    unfold zeropVerifier
    rw [hd]
    dsimp only
    rw [if_pos hw, AlgCircuit.zeroTest_of_toMvPolynomial_eq_zero hz]
    rfl

/-- **`ZEROP ∈ coRP`** [AB09, §7.2.3], for any verifier model in which `zeropVerifier` is
efficient.  For `polyTimeModel`, the hypothesis `polyTimeModel.Eff (boolVerifier
zeropVerifier)` is discharged by the class half of this result (polynomial-time binary
arithmetic). -/
theorem inCoRP_ZEROP (E : VerifierModel) (hE : E.Eff (boolVerifier zeropVerifier)) :
    InCoRP E ZEROP :=
  ⟨zeropVerifier, 2400, 2, hE, fun x =>
    ⟨fun hx => (zeropVerifier_spec x).1 hx,
      fun hx => (zeropVerifier_spec x).2 (by by_contra h; exact hx h)⟩⟩

end Randomized
