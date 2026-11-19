/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.CoinSampling.Buckets
import TCSlib.Cryptography.LWE.Experiments
import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Coin samplers for residues and LWE seeds

Instances of the bucket sampler for the exact laws of the library's lattice layer: uniform
residues modulo any `q ≥ 1` (dyadic or not), the seeds of a finite LWE noise law, and the full
seed of an LWE challenge (matrix, secret, one noise seed per row). The LWE challenge computed
from fair coins with a default seed is close to the exact challenge, and every distinguisher's
advantage moves by at most the seed sampler's failure probability: the sampler contract that
`LWE.Family` leaves to implementations, for any modulus (`LWE.sampleFromBits` covers only
`q = 2^width`).

## Main definitions

* `CoinSampling.CoinSampler.zmod q s`: uniform residues modulo `q` from `s` coins.
* `CoinSampling.CoinSampler.noiseSeeds χ s`: seeds of a finite noise law (laws only).
* `CoinSampling.CoinSampler.LWESeed`, `.lweSeeds`: the LWE seed and its coin sampler.

## Main results

* `CoinSampling.CoinSampler.fail_zmod_le`: `≤ 2^{-t}` with `b + t` coins for `q ≤ 2^b`.
* `CoinSampling.CoinSampler.fail_lweSeeds_le`: union bound over the seed's draws.
* `CoinSampling.CoinSampler.statClose_lweSample_coins`,
  `CoinSampling.CoinSampler.distAdv_lweSample_coins_le`: the LWE challenge from fair coins.
* `CoinSampling.CoinSampler.uprob_zmod_three_four_eq_some`,
  `CoinSampling.CoinSampler.fail_zmod_three_four`: a concrete instance (`q = 3`, four coins:
  each residue with probability `5/16`, failure `1/16`).

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated 17 February
  2016, Definitions 4.2.1 (the LWE distribution) and 4.2.3 (decision-LWE).
* [Lem19] D. Lemire, *Fast Random Integer Generation in an Interval*, ACM Trans. Model. Comput.
  Simul. 29(1), 2019; arXiv:1805.10941v4, §3.2, Algorithm 4 (the bucket sampler, one round).
-/

namespace TCSlib.Cryptography.CoinSampling

namespace CoinSampler

/-- **Uniform residues modulo `q`**: the bucket sampler of `Fin q` read through Mathlib's
`ZMod.finEquiv q` [Pei16, Definition 4.2.1: the uniform matrix and secret of LWE]
[Lem19, §3.2, Algorithm 4] (one round). -/
def zmod (q : ℕ) [NeZero q] (s : ℕ) : CoinSampler (ZMod q) s :=
  (bucket q s).congr (ZMod.finEquiv q).toEquiv

/-- `(zmod q s).dec c = (bucketDec q s c).map (ZMod.finEquiv q)`. -/
theorem zmod_dec (q : ℕ) [NeZero q] (s : ℕ) (c : Fin s → Bool) :
    (zmod q s).dec c = (bucketDec q s c).map (ZMod.finEquiv q).toEquiv := by
  rw [zmod, congr_dec, bucket_dec]

/-- The residue sampler fails as the bucket sampler: `(zmod q s).fail = (2^s mod q)/2^s`
(`fail_congr`, `fail_bucket`). -/
theorem fail_zmod (q : ℕ) [NeZero q] (s : ℕ) :
    (zmod q s).fail = ((2 ^ s % q : ℕ) : ℝ) / 2 ^ s := by
  rw [zmod, fail_congr, fail_bucket]

/-- With `q ≤ 2^b`, the residue sampler with `b + t` coins fails with probability at most
`2^{-t}` (`fail_congr`, `fail_bucket_le`). -/
theorem fail_zmod_le (q : ℕ) [NeZero q] {b : ℕ} (hq : q ≤ 2 ^ b) (t : ℕ) :
    (zmod q (b + t)).fail ≤ (2 : ℝ)⁻¹ ^ t := by
  rw [zmod, fail_congr]
  exact fail_bucket_le (NeZero.pos q) hq t

/-- **Non-vacuity, success**: from four coins, each residue modulo `3` is output with
probability `⌊16/3⌋/16 = 5/16` (`uprob_bucketDec_eq_some`). Glue: a concrete check. -/
theorem uprob_zmod_three_four_eq_some (a : ZMod 3) :
    uprob (fun c => (zmod 3 4).dec c = some a) = 5 / 16 := by
  rw [OneWay.uprob_congr fun c => (zmod_dec 3 4 c).symm ▸
    option_map_equiv_eq_some_iff (ZMod.finEquiv 3).toEquiv (bucketDec 3 4 c) a,
    uprob_bucketDec_eq_some]
  norm_num

/-- **Non-vacuity, failure**: from four coins, the residue sampler modulo `3` gives up with
probability `(16 mod 3)/16 = 1/16` (`fail_zmod`), below the design bound `3/16`
(`fail_bucket_lt`). Glue: a concrete check. -/
theorem fail_zmod_three_four : (zmod 3 4).fail = 1 / 16 := by
  rw [fail_zmod]
  norm_num

/-- **Seeds of a finite LWE noise law** [Pei16, Definition 4.2.1, finite-seed specialization of
`LWE.Noise`]: the bucket sampler of `χ.Coins` through its enumeration (laws only; an efficient
noise sampler supplies a computable enumeration). -/
noncomputable def noiseSeeds (χ : LWE.Noise) (s : ℕ) : CoinSampler χ.Coins s :=
  ofEquiv (Fintype.equivFin χ.Coins) s

/-- `noiseSeeds χ s = ofEquiv (Fintype.equivFin χ.Coins) s`. -/
theorem noiseSeeds_eq (χ : LWE.Noise) (s : ℕ) :
    noiseSeeds χ s = ofEquiv (Fintype.equivFin χ.Coins) s := rfl

/-- The seed type of `LWE.sample P χ` [Pei16, Definition 4.2.1]: the matrix, one common
secret, one noise seed per row. -/
abbrev LWESeed (P : LWE.Parameters) (χ : LWE.Noise) : Type :=
  Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
    ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))

/-- `LWESeed P χ` is the seed type of `LWE.sample P χ`. -/
theorem lweSeed_eq (P : LWE.Parameters) (χ : LWE.Noise) :
    LWESeed P χ = (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) := rfl

/-- **The LWE seed from fair coins** at any modulus (dyadic or not) [Pei16, Definition 4.2.1]:
`m · n` residues for the matrix, `n` for the secret, `m` noise seeds, all independent (`pi`,
`prod`, `Matrix.of`). Complements `LWE.sampleFromBits`, exact only for `q = 2^width`. -/
noncomputable def lweSeeds (P : LWE.Parameters) (χ : LWE.Noise) (s s' : ℕ) :
    CoinSampler (LWESeed P χ)
      (P.samples * (P.dimension * s) + (P.dimension * s + P.samples * s')) :=
  ((pi P.samples (pi P.dimension (zmod P.modulus s))).congr Matrix.of).prod
    ((pi P.dimension (zmod P.modulus s)).prod (pi P.samples (noiseSeeds χ s')))

/-- `lweSeeds P χ s s'` is the product of the matrix, secret and noise-seed samplers. -/
theorem lweSeeds_eq (P : LWE.Parameters) (χ : LWE.Noise) (s s' : ℕ) :
    lweSeeds P χ s s' =
      ((pi P.samples (pi P.dimension (zmod P.modulus s))).congr Matrix.of).prod
        ((pi P.dimension (zmod P.modulus s)).prod (pi P.samples (noiseSeeds χ s'))) := rfl

/-- **Union bound for the LWE seed**: `fail ≤ (m n + n) · fail(zmod) + m · fail(noise)`
(`fail_prod_le`, `fail_pi_le`, `fail_congr`). -/
theorem fail_lweSeeds_le (P : LWE.Parameters) (χ : LWE.Noise) (s s' : ℕ) :
    (lweSeeds P χ s s').fail ≤
      (P.samples * P.dimension + P.dimension) * (zmod P.modulus s).fail +
        P.samples * (noiseSeeds χ s').fail := by
  have hz := (zmod P.modulus s).fail_nonneg
  have hA : (pi P.samples (pi P.dimension (zmod P.modulus s))).fail ≤
      P.samples * (P.dimension * (zmod P.modulus s).fail) :=
    (fail_pi_le _ _).trans (mul_le_mul_of_nonneg_left (fail_pi_le _ _) (Nat.cast_nonneg _))
  have hB := fail_pi_le P.dimension (zmod P.modulus s)
  have hC := fail_pi_le P.samples (noiseSeeds χ s')
  refine (fail_prod_le _ _).trans ?_
  rw [fail_congr]
  have hBC := fail_prod_le (pi P.dimension (zmod P.modulus s)) (pi P.samples (noiseSeeds χ s'))
  nlinarith

/-- **The LWE challenge from fair coins** (default fallback seed `d`) is `fail`-close to the
exact challenge [Pei16, Definition 4.2.1]: `statClose_getD`, post-processed by
`LWE.sample P χ` (`StatClose.map`). -/
theorem statClose_lweSample_coins (P : LWE.Parameters) (χ : LWE.Noise) (s s' : ℕ)
    [DecidableEq (LWESeed P χ)] (d : LWESeed P χ) :
    StatClose (fun c => LWE.sample P χ (((lweSeeds P χ s s').dec c).getD d)) (LWE.sample P χ)
      (lweSeeds P χ s s').fail :=
  ((lweSeeds P χ s s').statClose_getD d).map (LWE.sample P χ)

/-- **Distinguishers transfer** [Pei16, Definition 4.2.3]: any distinguisher's advantage
between the coin-implemented LWE challenge and uniform exceeds its `decisionAdvantage` by at
most the seed failure probability (`distAdv_le_of_statClose` on the real side, triangle
inequality). The form an `LWE.Family` implementation contract consumes. -/
theorem distAdv_lweSample_coins_le {ρ : Type} [Fintype ρ] [Nonempty ρ] (P : LWE.Parameters)
    (χ : LWE.Noise) (s s' : ℕ) [DecidableEq (LWESeed P χ)] (d : LWESeed P χ)
    (D : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) → ρ → Bool) :
    distAdv (fun c => LWE.sample P χ (((lweSeeds P χ s s').dec c).getD d)) id D ≤
      LWE.decisionAdvantage P χ D + (lweSeeds P χ s s').fail := by
  have h := distAdv_le_of_statClose _ _ (statClose_lweSample_coins P χ s s' d) D
  rw [LWE.decisionAdvantage_eq, distAdv_def, distAdv_def]
  rw [distAdv_def] at h
  have := abs_sub_le (acceptProb (fun c => LWE.sample P χ (((lweSeeds P χ s s').dec c).getD d)) D)
    (acceptProb (LWE.sample P χ) D) (acceptProb id D)
  linarith

end CoinSampler

end TCSlib.Cryptography.CoinSampling
