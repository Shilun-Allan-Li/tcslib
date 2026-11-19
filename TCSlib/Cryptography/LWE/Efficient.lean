/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.LWE.Assumption
import TCSlib.Cryptography.LWE.BitNoise
import TCSlib.Cryptography.CoinSampling.Contract
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Complexity.ClassP.BinaryArith.PrimeFind
import TCSlib.Complexity.Randomized.BiasedCoinHalting
import TCSlib.Complexity.Randomized.Primitives
import TCSlib.Programs.Util.List

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Efficient LWE families: a uniform parameter map and an efficient noise sampler

`LWE.Family` (`LWE/Assumption.lean`) and `LWE.Noise` carry no efficiency. Under rule 15
(efficiency is part of the definition of every primitive), every scheme instance built on LWE
requires an `EfficientFamily`: an `LWE.Family` together with

* a **uniform parameter map**: one polynomial-time string map sending `1^κ` to the parameter
  word `⟨1^n, ⟨1^m, ⦃q⦄⟩⟩` of the family's parameters (`Parameters.encode`);
* the **noise sampler's efficiency** in the contract form `CoinSampling.SamplesEfficiently`
  of `CoinSampling/Contract.lean`: its seeds are drawn by a `UniformSampler` reading a uniformly
  computable parameter word (`noiseInput`), and the scalar error is computed in polynomial time
  as a sign-magnitude word (`noiseWord`).

`DLWEAssumption` stays on the raw `Family`: consumers write `DLWEAssumption F.toFamily`.

## Main definitions

* `Parameters.encode w P`: the parameter word `⟨1^n, ⟨1^m, ⦃q⦄_{w+1}⟩⟩`.
* `noiseWord e`: the sign-magnitude word `[e < 0] :: bits |e|` of an integer error.
* `EfficientFamily`: `Family` with `params_uniform`, `noiseInput`, `noiseInput_uniform`,
  `encodeSeed` and `noise_efficient`.
* `seedWord r`: the numeral `0 :: r` of an `n`-bit seed, drawn at the bucket parameter word
  `CoinSampling.seedModulusWord n = ⦃2^n⦄_{n+1}` (`CoinSampling/Contract.lean`).
* `onesCount`, `signedDiff`, `centeredCore T`: the polynomial-time core of `centeredNoise`
  (the unary ones are `Randomized.onesW`).
* `dyadicParameters`, `dyadicFamily`, `EfficientFamily.ofBitSeeds`, `EfficientFamily.ofDyadic`:
  the polynomially scheduled dyadic families with bit-seed noise.
* `dyadicExample`: one non-vacuity instance (no hardness claimed).

## Main results

* `encode_injective`, `noiseWord_injective`: the words determine the values.
* `params_uniform_of_schedule`: the parameter map of a schedule `n = N(κ)`, `m = M(κ)`,
  `q = 2^{W(κ)}` is uniform.
* `drawSamplable_bitSeeds`, `noise_efficient_of_bitSeeds`, `noise_efficient_of_bitNoise`,
  `noise_efficient_centeredNoise`: bit-seed noise samplers are efficient (exact draws: failure 0).

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definitions 4.2.1 and 4.2.3 (the LWE distribution and decision problem).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 23.4 (one machine, uniform coins) and Definition 26.8 (non-uniform PPT).
* [Lem19] D. Lemire, *Fast Random Integer Generation in an Interval*, ACM Trans. Model. Comput.
  Simul. 29(1), 2019; arXiv:1805.10941v4, §3.2, Algorithm 4 (the bucket sampler, one round),
  as `CoinSampling/Contract.lean` cites it.

**Convention.** The structures are a repository convention (rule 15, ruling Q3 A): [Pei16] states
the families without an efficiency clause. No hardness is asserted anywhere in this file.

**The noise sampler's parameter word.** The draw half of the contract needs a `UniformSampler`
`U` with `U.Ω (y κ π) ≃ (noise κ).Coins` at the parameter word `y κ π`. No registered sampler
reads a bit-seed type from the LWE parameter word (`bucketSampler` reads its whole word as a
numeral), so the noise sampler reads its own word `noiseInput κ`, which is uniformly computable
from `1^κ` (`noiseInput_uniform`); for bit seeds it is `CoinSampling.seedModulusWord n = ⦃2^n⦄`.

**The noise output.** The core sees `1^κ`, the sampler's word and the seed, not the modulus, so
the error is written modulus-free, in sign-magnitude form (`noiseWord`); an honest algorithm
reduces it modulo `q` with `BinArith` after reading `q` from `Parameters.encode`.
-/

namespace TCSlib.Cryptography.LWE

open Complexity Turing
open TCSlib.Cryptography.NumberTheory (listToNat)

/-! ### The parameter word -/

/-- **The parameter word** of LWE parameters at modulus width `w`: the pair
`⟨1^n, ⟨1^m, ⦃q⦄_{w+1}⟩⟩` of the dimension and the sample count in unary and the modulus as an
MSB-first numeral of width `w + 1` (the width of `CoinSampling.modulusWord`, so that every
`q ≤ 2^w` is written exactly). Glue: rule 15's parameter word; [Pei16, Definition 4.2.3] fixes
the parameters, not their encoding. -/
def Parameters.encode (w : ℕ) (P : Parameters) : List Bool :=
  pairEncode (List.replicate P.dimension true)
    (pairEncode (List.replicate P.samples true) (Candidates.natToList (w + 1) P.modulus))

/-- `P.encode w = ⟨1^n, ⟨1^m, natToList (w + 1) q⟩⟩`. -/
theorem Parameters.encode_eq (w : ℕ) (P : Parameters) :
    P.encode w = pairEncode (List.replicate P.dimension true)
      (pairEncode (List.replicate P.samples true) (Candidates.natToList (w + 1) P.modulus)) :=
  rfl

/-- **The parameter word determines the parameters**: for moduli `q, q' ≤ 2^w`,
`P.encode w = P'.encode w` implies `P = P'`. Glue.

**Proof sketch.** The two projections of the pair give `1^n = 1^{n'}` and
`⟨1^m, ⦃q⦄⟩ = ⟨1^{m'}, ⦃q'⦄⟩`, hence `n = n'`, `m = m'` (lengths) and `q = q'`
(`Candidates.natToList_injOn`, as `q, q' < 2^{w+1}`). The parameters are then equal field by
field. -/
theorem Parameters.encode_injective {w : ℕ} {P P' : Parameters} (hP : P.modulus ≤ 2 ^ w)
    (hP' : P'.modulus ≤ 2 ^ w) (h : P.encode w = P'.encode w) : P = P' := by
  have hlt : ∀ q : ℕ, q ≤ 2 ^ w → q < 2 ^ (w + 1) := fun q hq =>
    hq.trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self w))
  rw [Parameters.encode_eq, Parameters.encode_eq] at h
  have h1 := congrArg pairFstD h
  have h2 := congrArg (fun z => pairFstD (pairSndD z)) h
  have h3 := congrArg (fun z => pairSndD (pairSndD z)) h
  simp only [pairFstD_pairEncode, pairSndD_pairEncode] at h1 h2 h3
  have hn := congrArg List.length h1
  have hm := congrArg List.length h2
  rw [List.length_replicate, List.length_replicate] at hn hm
  have hq := Candidates.natToList_injOn (hlt _ hP) (hlt _ hP') h3
  obtain ⟨n, m, q, h2q⟩ := P
  obtain ⟨n', m', q', h2q'⟩ := P'
  dsimp only at hn hm hq
  subst hn hm hq
  rfl

/-- The first component of the parameter word is `1^n`. -/
theorem Parameters.pairFstD_encode (w : ℕ) (P : Parameters) :
    pairFstD (P.encode w) = List.replicate P.dimension true := by
  rw [Parameters.encode_eq, pairFstD_pairEncode]

/-- The second component of the parameter word starts with `1^m`. -/
theorem Parameters.pairFstD_pairSndD_encode (w : ℕ) (P : Parameters) :
    pairFstD (pairSndD (P.encode w)) = List.replicate P.samples true := by
  rw [Parameters.encode_eq, pairSndD_pairEncode, pairFstD_pairEncode]

/-- The last component of the parameter word is the numeral `⦃q⦄_{w+1}`. -/
theorem Parameters.pairSndD_pairSndD_encode (w : ℕ) (P : Parameters) :
    pairSndD (pairSndD (P.encode w)) = Candidates.natToList (w + 1) P.modulus := by
  rw [Parameters.encode_eq, pairSndD_pairEncode, pairSndD_pairEncode]

/-- **The modulus of a family as a bounded modulus**: `q(κ)` with `0 < q(κ) ≤ 2^{b(κ)}` for the
residue width `b = F.residueBits` (`Family.modulus_le_pow`), the public input of
`CoinSampling.samplesEfficiently_residue`. Glue. -/
def Family.boundedModulus (F : Family) (κ : ℕ) :
    CoinSampling.BoundedModulus F.residueBits κ :=
  ⟨⟨(F.parameters κ).modulus, Nat.pos_of_ne_zero (NeZero.ne _)⟩, F.modulus_le_pow κ⟩

/-- `(F.boundedModulus κ : ℕ) = q(κ)`. -/
theorem Family.boundedModulus_val (F : Family) (κ : ℕ) :
    ((F.boundedModulus κ).1 : ℕ) = (F.parameters κ).modulus := rfl

/-- **The modulus component is the residue sampler's word**: the last component of the parameter
word at width `b(κ)` is `CoinSampling.modulusWord b κ` of the family's modulus, the word on which
`CoinSampling.samplesEfficiently_residue` samples uniform residues. Glue. -/
theorem Family.pairSndD_pairSndD_encode (F : Family) (κ : ℕ) :
    pairSndD (pairSndD ((F.parameters κ).encode (F.residueBits.eval κ))) =
      CoinSampling.modulusWord F.residueBits κ (F.boundedModulus κ) := by
  rw [Parameters.pairSndD_pairSndD_encode, CoinSampling.modulusWord_eq,
    Family.boundedModulus_val]

/-! ### The noise word -/

/-- **The noise word**: the sign-magnitude word `[e < 0] :: bits |e|` of an integer error, the
magnitude little-endian (`Nat.bits`, the format of `Complexity.BinArith`). Glue: the encoded
output of the noise sampler. -/
def noiseWord (e : ℤ) : List Bool := decide (e < 0) :: Nat.bits e.natAbs

/-- `noiseWord e = decide (e < 0) :: Nat.bits |e|`. -/
theorem noiseWord_eq (e : ℤ) : noiseWord e = decide (e < 0) :: Nat.bits e.natAbs := rfl

/-- **The noise word determines the error**: `noiseWord` is injective. Glue.

**Proof sketch.** Equal words have equal heads (signs) and equal tails; the tails are the
binary words of `|e|` and `|e'|`, so `|e| = |e'|` (`LogProg.bits_injective`). Integers with the
same absolute value and the same sign are equal. -/
theorem noiseWord_injective : Function.Injective noiseWord := by
  intro a b h
  rw [noiseWord_eq, noiseWord_eq, List.cons.injEq] at h
  obtain ⟨hs, hm⟩ := h
  have habs : a.natAbs = b.natAbs := LogProg.bits_injective hm
  have hsign : (a < 0 ↔ b < 0) := by
    constructor
    · intro ha; exact of_decide_eq_true (hs ▸ decide_eq_true ha)
    · intro hb; exact of_decide_eq_true (hs.symm ▸ decide_eq_true hb)
  rcases Int.natAbs_eq_natAbs_iff.1 habs with hab | hab
  · exact hab
  · omega

/-! ### The efficient family -/

/-- **An efficient LWE family** (rule 15, ruling Q3 A): an LWE family [Pei16, Definition 4.2.3]
with

* `params_uniform`: one polynomial-time map `f` with `f (1^κ) = (parameters κ).encode (b(κ))`,
  `b = residueBits` (uniform: no advice, no κ-indexed program [PS10, Definition 23.4]);
* `noiseInput`, `noiseInput_uniform`: the noise sampler's parameter word, computed from `1^κ` by
  one polynomial-time map;
* `encodeSeed`, `noise_efficient`: the noise sampler `(noise κ).sample` applied to one uniform
  seed is efficient in the contract form `CoinSampling.SamplesEfficiently`, with the seed written
  by `encodeSeed κ` and the error by `noiseWord`.

Glue: rule 15's efficiency-in-the-definition form; [Pei16] states the families without an
efficiency clause. No hardness is asserted: `DLWEAssumption F.toFamily` is a separate hypothesis.
-/
structure EfficientFamily extends Family where
  /-- The parameter word at the residue width is uniformly computable from `1^κ`. -/
  params_uniform : ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ κ, f (List.replicate κ true) = (parameters κ).encode (residueBits.eval κ)
  /-- The parameter word read by the noise sampler. -/
  noiseInput : ℕ → List Bool
  /-- The noise sampler's parameter word is uniformly computable from `1^κ`. -/
  noiseInput_uniform : ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ κ, f (List.replicate κ true) = noiseInput κ
  /-- The encoding of a noise seed. -/
  encodeSeed : ∀ κ, (noise κ).Coins → List Bool
  /-- The noise sampler is efficient in the contract form, with output `noiseWord`. -/
  noise_efficient : CoinSampling.SamplesEfficiently (P := fun _ => Unit)
    (Draw := fun κ _ => (noise κ).Coins) (β := fun _ _ => ℤ)
    (fun κ _ => noiseInput κ) (fun κ _ => encodeSeed κ) (fun _ _ e => noiseWord e)
    (fun κ _ => (noise κ).sample)

/-! ### Uniform schedules -/

/-- **A polynomial dyadic schedule has a uniform parameter map**: if `n(κ) = N(κ)`,
`m(κ) = M(κ)` and `q(κ) = 2^{W(κ)}`, one polynomial-time map sends `1^κ` to
`(P κ).encode (W(κ))`. Glue.

**Proof sketch.** The map writes `⟨1^{N(|x|)}, ⟨1^{M(|x|)}, 1 0^{W(|x|)}⟩⟩`: the unary words
by `polyTimeComputable_unaryPoly`, the numeral of `2^{W}` (`CoinSampling.natToList_two_pow`) by
`CoinSampling.polyTimeComputable_twoPowWord`, the pairs by `PolyTimeComputable.pairEncode`. On
`1^κ` the length is `κ`. -/
theorem params_uniform_of_schedule (N M W : PolyExpr) (P : ℕ → Parameters)
    (hn : ∀ κ, (P κ).dimension = N.eval κ) (hm : ∀ κ, (P κ).samples = M.eval κ)
    (hq : ∀ κ, (P κ).modulus = 2 ^ W.eval κ) :
    ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ κ, f (List.replicate κ true) = (P κ).encode (W.eval κ) := by
  refine ⟨fun x => pairEncode (List.replicate (N.eval x.length) true)
    (pairEncode (List.replicate (M.eval x.length) true)
      (true :: List.replicate (W.eval x.length) false)),
    (polyTimeComputable_unaryPoly N).pairEncode
      ((polyTimeComputable_unaryPoly M).pairEncode (CoinSampling.polyTimeComputable_twoPowWord W)),
    fun κ => ?_⟩
  dsimp only
  rw [List.length_replicate, Parameters.encode_eq, hn, hm, hq, CoinSampling.natToList_two_pow]

/-! ### Dyadic families -/

/-- **Dyadic parameters** of a schedule: `n = N(κ)`, `m = M(κ)`, `q = 2^{W(κ)}`, for `W ≥ 1`
(so `q ≥ 2`). Glue: the power-of-two moduli of the exact fair-bit route
(`LWE/Assumption.lean`, scope note). -/
def dyadicParameters (N M W : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ) (κ : ℕ) : Parameters where
  dimension := N.eval κ
  samples := M.eval κ
  modulus := 2 ^ W.eval κ
  modulus_ge_two := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ W.eval κ := Nat.pow_le_pow_right (by norm_num) (hW κ)

/-- The dimension of `dyadicParameters N M W hW κ` is `N(κ)`. -/
theorem dyadicParameters_dimension (N M W : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ) (κ : ℕ) :
    (dyadicParameters N M W hW κ).dimension = N.eval κ := rfl

/-- The sample count of `dyadicParameters N M W hW κ` is `M(κ)`. -/
theorem dyadicParameters_samples (N M W : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ) (κ : ℕ) :
    (dyadicParameters N M W hW κ).samples = M.eval κ := rfl

/-- The modulus of `dyadicParameters N M W hW κ` is `2^{W(κ)}`. -/
theorem dyadicParameters_modulus (N M W : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ) (κ : ℕ) :
    (dyadicParameters N M W hW κ).modulus = 2 ^ W.eval κ := rfl

/-- **The dyadic LWE family** of a schedule `(N, M, W)` with noise `χ`: parameters
`dyadicParameters N M W hW`, bounds `N`, `M` and residue width `W` (so `q = 2^W` fits exactly)
[Pei16, Definition 4.2.3, power-of-two moduli]. -/
def dyadicFamily (N M W : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ) (χ : ℕ → Noise) : Family where
  parameters := dyadicParameters N M W hW
  noise := χ
  dimensionBound := N
  samplesBound := M
  residueBits := W
  dimension_le κ := (dyadicParameters_dimension N M W hW κ).le
  samples_le κ := (dyadicParameters_samples N M W hW κ).le
  modulus_le_pow κ := (dyadicParameters_modulus N M W hW κ).le

/-- The parameters of `dyadicFamily N M W hW χ` are `dyadicParameters N M W hW`. -/
theorem dyadicFamily_parameters (N M W : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ)
    (χ : ℕ → Noise) : (dyadicFamily N M W hW χ).parameters = dyadicParameters N M W hW := rfl

/-- The noise of `dyadicFamily N M W hW χ` is `χ`. -/
theorem dyadicFamily_noise (N M W : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ) (χ : ℕ → Noise) :
    (dyadicFamily N M W hW χ).noise = χ := rfl

/-- The residue width of `dyadicFamily N M W hW χ` is `W`. -/
theorem dyadicFamily_residueBits (N M W : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ)
    (χ : ℕ → Noise) : (dyadicFamily N M W hW χ).residueBits = W := rfl

/-- The dimension bound of `dyadicFamily N M W hW χ` is `N`. -/
theorem dyadicFamily_dimensionBound (N M W : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ)
    (χ : ℕ → Noise) : (dyadicFamily N M W hW χ).dimensionBound = N := rfl

/-- The sample bound of `dyadicFamily N M W hW χ` is `M`. -/
theorem dyadicFamily_samplesBound (N M W : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ)
    (χ : ℕ → Noise) : (dyadicFamily N M W hW χ).samplesBound = M := rfl

/-- **The dyadic family's parameter map is uniform** (`params_uniform_of_schedule`). Glue. -/
theorem dyadicFamily_params_uniform (N M W : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ)
    (χ : ℕ → Noise) :
    ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ κ, f (List.replicate κ true) = ((dyadicFamily N M W hW χ).parameters κ).encode
        ((dyadicFamily N M W hW χ).residueBits.eval κ) := by
  rw [dyadicFamily_parameters, dyadicFamily_residueBits]
  exact params_uniform_of_schedule N M W _ (dyadicParameters_dimension N M W hW)
    (dyadicParameters_samples N M W hW) (dyadicParameters_modulus N M W hW)

/-! ### Bit-seed noise -/

/-- **The seed word of a polynomial seed length is uniform**: if `n(κ) = t(κ)`, one
polynomial-time map sends `1^κ` to `CoinSampling.seedModulusWord (n κ)`
(`CoinSampling.polyTimeComputable_twoPowWord`). Glue. -/
theorem seedModulusWord_uniform (t : PolyExpr) (n : ℕ → ℕ) (hn : ∀ κ, n κ = t.eval κ) :
    ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ κ, f (List.replicate κ true) = CoinSampling.seedModulusWord (n κ) :=
  ⟨_, CoinSampling.polyTimeComputable_twoPowWord t, fun κ => by
    rw [List.length_replicate, CoinSampling.seedModulusWord_eq_cons, hn]⟩

/-- **The numeral of a seed**: the `n`-bit seed `r` as the `(n+1)`-bit numeral `0 :: r` of its
value `bitsToNat r` (the encoding `bucketSampler` writes at the word
`CoinSampling.seedModulusWord n`). Glue. -/
def seedWord {n : ℕ} (r : Fin n → Bool) : List Bool := false :: List.ofFn r

/-- `seedWord r = false :: List.ofFn r`. -/
theorem seedWord_eq {n : ℕ} (r : Fin n → Bool) : seedWord r = false :: List.ofFn r := rfl

/-- The `(n+1)`-bit numeral of `bitsToNat r` is `seedWord r`. Glue
(`Candidates.natToList_length_listToNat`, `NumberTheory.listToNat_cons`,
`NumberTheory.bitsToNat_eq_listToNat`). -/
theorem natToList_bitsToNat {n : ℕ} (r : Fin n → Bool) :
    Candidates.natToList (n + 1) (bitsToNat r) = seedWord r := by
  have h := Candidates.natToList_length_listToNat (false :: List.ofFn r)
  rw [List.length_cons, List.length_ofFn, NumberTheory.listToNat_cons,
    if_neg Bool.false_ne_true, zero_mul, zero_add, ← NumberTheory.bitsToNat_eq_listToNat] at h
  rw [h, seedWord_eq]

/-- **The seed modulus** `2^{n(κ)}` as a bounded modulus of width `t(κ) = n(κ)`. Glue. -/
def seedModulus (t : PolyExpr) (n : ℕ → ℕ) (hn : ∀ κ, n κ = t.eval κ) (κ : ℕ) :
    CoinSampling.BoundedModulus t κ :=
  ⟨⟨2 ^ n κ, Nat.two_pow_pos _⟩, (Nat.pow_le_pow_right (by norm_num) (hn κ).le)⟩

/-- `(seedModulus t n hn κ : ℕ) = 2^{n(κ)}`. -/
theorem seedModulus_val (t : PolyExpr) (n : ℕ → ℕ) (hn : ∀ κ, n κ = t.eval κ) (κ : ℕ) :
    ((seedModulus t n hn κ).1 : ℕ) = 2 ^ n κ := rfl

/-- The residue sampler's word of the seed modulus is `CoinSampling.seedModulusWord (n κ)`
(`CoinSampling.modulusWord_eq`). Glue. -/
theorem modulusWord_seedModulus (t : PolyExpr) (n : ℕ → ℕ) (hn : ∀ κ, n κ = t.eval κ)
    (κ : ℕ) :
    CoinSampling.modulusWord t κ (seedModulus t n hn κ) = CoinSampling.seedModulusWord (n κ) := by
  rw [CoinSampling.modulusWord_eq, seedModulus_val, CoinSampling.seedModulusWord_eq, hn]

/-- **Bit seeds are drawn by the bucket sampler**: for noise laws whose seed types are
`n(κ)`-bit words (`hc`), with `n(κ) = t(κ)`, the seeds, written as `seedWord`, are
`DrawSamplable` at the word `CoinSampling.seedModulusWord (n κ)` [Lem19, §3.2, Algorithm 4; PS10,
Definition 23.4].

**Proof sketch.** This is `CoinSampling.drawSamplable_residue t` (uniform `ZMod q` by
`bucketSampler`, failure at most `2^{-κ}`) at the modulus `q = 2^{n(κ)}`
(`CoinSampling.drawSamplable_restrict`, `modulusWord_seedModulus`), transported along
`ZMod (2^n) ≃ Fin (2^n) ≃ (Fin n → Bool) ≃ Coins` (`ZMod.finEquiv`, `bitsEquiv`, `Equiv.cast`;
`DrawSamplable.congr`). The encodings agree: `residueEnc` writes `a : Fin (2^n)` as `⦃a⦄_{n+1}`
(`CoinSampling.residueEnc_eq`), and `a = bitsToNat r` for the seed `r` (`bitsEquiv_val`), whose
numeral is `seedWord r` (`natToList_bitsToNat`). -/
theorem drawSamplable_bitSeeds (t : PolyExpr) (n : ℕ → ℕ) (hn : ∀ κ, n κ = t.eval κ)
    (χ : ℕ → Noise) (hc : ∀ κ, (χ κ).Coins = (Fin (n κ) → Bool)) :
    CoinSampling.DrawSamplable (P := fun _ => Unit) (Draw := fun κ _ => (χ κ).Coins)
      (fun κ _ => CoinSampling.seedModulusWord (n κ)) (fun κ _ c => seedWord (cast (hc κ) c)) := by
  have h := (CoinSampling.drawSamplable_restrict (CoinSampling.drawSamplable_residue t)
    (seedModulus t n hn)).congr
    (Draw' := fun κ _ => (χ κ).Coins) (encDraw' := fun κ _ c => seedWord (cast (hc κ) c))
    (fun κ _ => (ZMod.finEquiv _).symm.toEquiv.trans
      ((bitsEquiv (n κ)).symm.trans (Equiv.cast (hc κ).symm))) fun κ _ d => by
      dsimp only
      rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.cast_apply, cast_cast, cast_eq,
        CoinSampling.residueEnc_eq, show t.eval κ + 1 = n κ + 1 by rw [hn],
        ← natToList_bitsToNat]
      congr 1
      rw [← bitsEquiv_val]
      exact congrArg Fin.val ((bitsEquiv (n κ)).apply_symm_apply _)
  have hy : (fun κ (_ : Unit) => CoinSampling.modulusWord t κ (seedModulus t n hn κ)) =
      fun κ _ => CoinSampling.seedModulusWord (n κ) := by
    funext κ _
    exact modulusWord_seedModulus t n hn κ
  rw [hy] at h
  exact h

/-- **Bit-seed noise is efficient** given a polynomial-time core: if the seed types are
`n(κ)`-bit words (`hc`), `n(κ) = t(κ)`, and one polynomial-time `g` writes the error on
`⟨1^κ, r⟩`, `g ⟨1^κ, r⟩ = noiseWord ((χ κ).sample c)` for the seed `c` with bits `r`, then the
noise sampler is efficient in the contract form [PS10, Definition 23.4]. Glue.

**Proof sketch.** The draw half is `drawSamplable_bitSeeds`. The core half reads `1^κ` and the
seed word `0 :: r` from `⟨1^κ, ⟨y, 0 :: r⟩⟩` (`NUPPT.advInput_eq`, the pair projections,
`polyTimeComputable_tail`) and applies `g`. -/
theorem noise_efficient_of_bitSeeds (t : PolyExpr) (n : ℕ → ℕ) (hn : ∀ κ, n κ = t.eval κ)
    (χ : ℕ → Noise) (hc : ∀ κ, (χ κ).Coins = (Fin (n κ) → Bool)) {g : List Bool → List Bool}
    (hg : PolyTimeComputable g)
    (hgf : ∀ κ c, g (pairEncode (List.replicate κ true) (List.ofFn (cast (hc κ) c))) =
      noiseWord ((χ κ).sample c)) :
    CoinSampling.SamplesEfficiently (P := fun _ => Unit) (Draw := fun κ _ => (χ κ).Coins)
      (β := fun _ _ => ℤ) (fun κ _ => CoinSampling.seedModulusWord (n κ))
      (fun κ _ c => seedWord (cast (hc κ) c)) (fun _ _ e => noiseWord e)
      (fun κ _ => (χ κ).sample) := by
  refine .intro (drawSamplable_bitSeeds t n hn χ hc)
    ((CoinSampling.coreComputable_iff _ _ _ _).2
      ⟨fun z => g (pairEncode (pairFstD z) ((pairSndD (pairSndD z)).drop 1)),
        hg.comp' (polyTimeComputable_pairFstD.pairEncode
          (polyTimeComputable_tail.comp' (polyTimeComputable_pairSndD.comp'
            polyTimeComputable_pairSndD))),
        fun κ _ c => ?_⟩)
  dsimp only
  rw [NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode,
    seedWord_eq, List.drop_one, List.tail_cons, hgf]

/-- **Bit noise is efficient**: the bit-seed noise `bitNoise (n κ) (f κ)` (`LWE/BitNoise.lean`)
with `n(κ) = t(κ)` and a polynomial-time `g` writing `noiseWord (f κ r)` on `⟨1^κ, r⟩` is
efficient in the contract form, its seeds drawn from fair coins (`noise_efficient_of_bitSeeds`,
`bitNoise_Coins`, `bitNoise_sample_cast`). Glue. -/
theorem noise_efficient_of_bitNoise (t : PolyExpr) (n : ℕ → ℕ) (hn : ∀ κ, n κ = t.eval κ)
    (f : ∀ κ, (Fin (n κ) → Bool) → ℤ)
    {g : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hgf : ∀ κ r, g (pairEncode (List.replicate κ true) (List.ofFn r)) = noiseWord (f κ r)) :
    CoinSampling.SamplesEfficiently (P := fun _ => Unit)
      (Draw := fun κ _ => (bitNoise (n κ) (f κ)).Coins) (β := fun _ _ => ℤ)
      (fun κ _ => CoinSampling.seedModulusWord (n κ))
      (fun κ _ c => seedWord (cast (bitNoise_Coins (n κ) (f κ)) c)) (fun _ _ e => noiseWord e)
      (fun κ _ => (bitNoise (n κ) (f κ)).sample) :=
  noise_efficient_of_bitSeeds t n hn (fun κ => bitNoise (n κ) (f κ))
    (fun κ => bitNoise_Coins (n κ) (f κ)) hg fun κ c => by
      rw [hgf, bitNoise_sample_cast]

/-! ### The core of the centered noise -/

/-- **The number of ones of a word, in binary**: `bits (#1 w)`, by the counting loop
`BinArith.countLoop` on the unary ones `Randomized.onesW w` (`Complexity/Randomized/
BiasedCoinHalting.lean`). Glue. -/
def onesCount (w : List Bool) : List Bool := pairFstD (BinArith.countLoop (Randomized.onesW w))

/-- `onesCount w = Nat.bits (#1 w)` (`BinArith.countLoop_eq`, `Randomized.length_onesW`). -/
theorem onesCount_eq (w : List Bool) : onesCount w = Nat.bits (w.count true) := by
  rw [onesCount, BinArith.countLoop_eq, pairFstD_pairEncode, Randomized.length_onesW]

/-- `onesCount` is polynomial-time (`Randomized.polyTimeComputable_onesW_snd` on `⟨[], w⟩`,
`BinArith.polyTimeComputable_countLoop`). -/
theorem polyTimeComputable_onesCount : PolyTimeComputable onesCount := by
  have h : PolyTimeComputable fun w => Randomized.onesW (pairSndD (pairEncode [] w)) :=
    Randomized.polyTimeComputable_onesW_snd.comp'
      ((polyTimeComputable_const []).pairEncode polyTimeComputable_id)
  refine (polyTimeComputable_pairFstD.comp' (BinArith.polyTimeComputable_countLoop.comp' h)).congr
    fun w => ?_
  dsimp only
  rw [pairSndD_pairEncode, onesCount]

/-- **The signed difference of two binary numbers**: on `⟨A, B⟩`, `0 :: (A ∸ B)` if `B ≤ A` and
`1 :: (B ∸ A)` otherwise (`BinArith.le`, `BinArith.sub`). Glue. -/
def signedDiff (z : List Bool) : List Bool :=
  if BinArith.le (pairEncode (pairSndD z) (pairFstD z)) then false :: BinArith.sub z
  else true :: BinArith.sub (pairEncode (pairSndD z) (pairFstD z))

/-- The defining equation of `signedDiff`. -/
theorem signedDiff_eq (z : List Bool) :
    signedDiff z = if BinArith.le (pairEncode (pairSndD z) (pairFstD z)) then
      false :: BinArith.sub z else true :: BinArith.sub (pairEncode (pairSndD z) (pairFstD z)) :=
  rfl

/-- **`signedDiff` writes the difference**: `signedDiff ⟨bits a, bits b⟩ = noiseWord (a − b)`
(`BinArith.le_pairEncode`, `BinArith.sub_pairEncode`). Glue. -/
theorem signedDiff_bits (a b : ℕ) :
    signedDiff (pairEncode (Nat.bits a) (Nat.bits b)) = noiseWord ((a : ℤ) - b) := by
  rw [signedDiff_eq, pairFstD_pairEncode, pairSndD_pairEncode, BinArith.le_pairEncode,
    noiseWord_eq]
  by_cases h : b ≤ a
  · rw [if_pos (decide_eq_true h), BinArith.sub_pairEncode,
      decide_eq_false (by omega : ¬ ((a : ℤ) - b < 0))]
    congr 2
    omega
  · rw [if_neg (by rw [decide_eq_false h]; exact Bool.false_ne_true), BinArith.sub_pairEncode,
      decide_eq_true (by omega : ((a : ℤ) - b < 0))]
    congr 2
    omega

/-- `signedDiff` is polynomial-time (`polyTimeComputable_ite`, `BinArith.polyTimeComputable_le`,
`BinArith.polyTimeComputable_sub`, `BinArith.polyTimeComputable_cons`). -/
theorem polyTimeComputable_signedDiff : PolyTimeComputable signedDiff := by
  have hsw : PolyTimeComputable fun z => pairEncode (pairSndD z) (pairFstD z) :=
    polyTimeComputable_pairSndD.pairEncode polyTimeComputable_pairFstD
  exact polyTimeComputable_ite (BinArith.polyTimeComputable_le.comp' hsw)
    (BinArith.polyTimeComputable_cons (p := fun _ => false) (polyTimeComputable_const [false])
      BinArith.polyTimeComputable_sub)
    (BinArith.polyTimeComputable_cons (p := fun _ => true) (polyTimeComputable_const [true])
      (BinArith.polyTimeComputable_sub.comp' hsw))

/-- **The core of `centeredNoise (T κ)`** on `⟨1^κ, r⟩`: split `r` after `T(κ)` bits, count the
ones of both halves in binary and write their signed difference. Glue. -/
def centeredCore (T : PolyExpr) (z : List Bool) : List Bool :=
  signedDiff (pairEncode (onesCount ((pairSndD z).take (T.eval (pairFstD z).length)))
    (onesCount ((pairSndD z).drop (T.eval (pairFstD z).length))))

/-- The defining equation of `centeredCore`. -/
theorem centeredCore_eq (T : PolyExpr) (z : List Bool) :
    centeredCore T z = signedDiff (pairEncode
      (onesCount ((pairSndD z).take (T.eval (pairFstD z).length)))
      (onesCount ((pairSndD z).drop (T.eval (pairFstD z).length)))) := rfl

/-- `centeredCore T` is polynomial-time (`polyTimeComputable_pairTakePoly`,
`polyTimeComputable_pairDropPoly`, `polyTimeComputable_onesCount`,
`polyTimeComputable_signedDiff`). -/
theorem polyTimeComputable_centeredCore (T : PolyExpr) : PolyTimeComputable (centeredCore T) :=
  polyTimeComputable_signedDiff.comp'
    ((polyTimeComputable_onesCount.comp' (polyTimeComputable_pairTakePoly T)).pairEncode
      (polyTimeComputable_onesCount.comp' (polyTimeComputable_pairDropPoly T)))

/-- The number of ones of `List.ofFn g` is `Σ_i [g i]`, from `List.count_ofFn`
(`Programs/Util/List.lean`) and `Finset.card_filter`. Glue. -/
theorem count_true_ofFn_eq_sum {k : ℕ} (g : Fin k → Bool) :
    (List.ofFn g).count true = ∑ i, (g i).toNat := by
  rw [List.count_ofFn, Finset.card_filter]
  exact Finset.sum_congr rfl fun i _ => by cases g i <;> rfl

/-- **`centeredCore` computes the centered value**: on `⟨1^κ, r⟩` with `r` of `T(κ) + T(κ)`
bits, `centeredCore T` writes `noiseWord (centeredValue (T κ) r)`. Glue.

**Proof sketch.** `List.ofFn r` is the first block followed by the second (`List.ofFn_add`), so
taking and dropping `T(κ)` bits gives the two blocks; their numbers of ones are the two sums of
`centeredValue_eq` (`onesCount_eq`, `count_true_ofFn_eq_sum`), and `signedDiff_bits` writes their
difference. -/
theorem centeredCore_ofFn (T : PolyExpr) (κ : ℕ) (r : Fin (T.eval κ + T.eval κ) → Bool) :
    centeredCore T (pairEncode (List.replicate κ true) (List.ofFn r)) =
      noiseWord (centeredValue (T.eval κ) r) := by
  have hsplit := List.ofFn_add (f := r)
  have hl : ∀ g : Fin (T.eval κ) → Bool, (List.ofFn g).length = T.eval κ := fun g =>
    List.length_ofFn
  rw [centeredCore_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
    hsplit, List.take_left' (hl _), List.drop_left' (hl _), onesCount_eq, onesCount_eq,
    count_true_ofFn_eq_sum, count_true_ofFn_eq_sum, signedDiff_bits, centeredValue_eq]
  push_cast
  rfl

/-- **The centered noise is efficient**: `centeredNoise (T κ)` (`LWE/BitNoise.lean`), with
`2 T(κ)` fair seed bits drawn by the bucket sampler and the core `centeredCore T`, is efficient
in the contract form [PS10, Definition 23.4] (`noise_efficient_of_bitSeeds`,
`centeredCore_ofFn`, `centeredNoise_sample_cast`). Glue. -/
theorem noise_efficient_centeredNoise (T : PolyExpr) :
    CoinSampling.SamplesEfficiently (P := fun _ => Unit)
      (Draw := fun κ _ => (centeredNoise (T.eval κ)).Coins) (β := fun _ _ => ℤ)
      (fun κ _ => CoinSampling.seedModulusWord (T.eval κ + T.eval κ))
      (fun κ _ c => seedWord (cast (centeredNoise_Coins (T.eval κ)) c))
      (fun _ _ e => noiseWord e) (fun κ _ => (centeredNoise (T.eval κ)).sample) :=
  noise_efficient_of_bitSeeds (T.add T) (fun κ => T.eval κ + T.eval κ)
    (fun κ => (PolyExpr.eval_add T T κ).symm) (fun κ => centeredNoise (T.eval κ))
    (fun κ => centeredNoise_Coins (T.eval κ)) (polyTimeComputable_centeredCore T)
    fun κ c => by rw [centeredCore_ofFn, centeredNoise_sample_cast]

/-! ### Constructors -/

/-- **An efficient family from bit-seed noise**: a family `F` with a uniform parameter map whose
noise seeds are `n(κ)`-bit words (`hc`), `n(κ) = t(κ)`, and a polynomial-time core `g` of the
noise (`noise_efficient_of_bitSeeds`), with noise word `CoinSampling.seedModulusWord (n κ)` and
seeds written as `seedWord`. Glue. -/
def EfficientFamily.ofBitSeeds (F : Family)
    (hparams : ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ κ, f (List.replicate κ true) = (F.parameters κ).encode (F.residueBits.eval κ))
    (t : PolyExpr) (n : ℕ → ℕ) (hn : ∀ κ, n κ = t.eval κ)
    (hc : ∀ κ, (F.noise κ).Coins = (Fin (n κ) → Bool)) {g : List Bool → List Bool}
    (hg : PolyTimeComputable g)
    (hgf : ∀ κ c, g (pairEncode (List.replicate κ true) (List.ofFn (cast (hc κ) c))) =
      noiseWord ((F.noise κ).sample c)) : EfficientFamily where
  toFamily := F
  params_uniform := hparams
  noiseInput κ := CoinSampling.seedModulusWord (n κ)
  noiseInput_uniform := seedModulusWord_uniform t n hn
  encodeSeed κ c := seedWord (cast (hc κ) c)
  noise_efficient := noise_efficient_of_bitSeeds t n hn F.noise hc hg hgf

/-- The family of `EfficientFamily.ofBitSeeds F …` is `F`. -/
theorem EfficientFamily.ofBitSeeds_toFamily (F : Family)
    (hparams : ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ κ, f (List.replicate κ true) = (F.parameters κ).encode (F.residueBits.eval κ))
    (t : PolyExpr) (n : ℕ → ℕ) (hn : ∀ κ, n κ = t.eval κ)
    (hc : ∀ κ, (F.noise κ).Coins = (Fin (n κ) → Bool)) {g : List Bool → List Bool}
    (hg : PolyTimeComputable g)
    (hgf : ∀ κ c, g (pairEncode (List.replicate κ true) (List.ofFn (cast (hc κ) c))) =
      noiseWord ((F.noise κ).sample c)) :
    (EfficientFamily.ofBitSeeds F hparams t n hn hc hg hgf).toFamily = F := rfl

/-- The noise word of `EfficientFamily.ofBitSeeds F …` is `CoinSampling.seedModulusWord (n κ)`. -/
theorem EfficientFamily.ofBitSeeds_noiseInput (F : Family)
    (hparams : ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ κ, f (List.replicate κ true) = (F.parameters κ).encode (F.residueBits.eval κ))
    (t : PolyExpr) (n : ℕ → ℕ) (hn : ∀ κ, n κ = t.eval κ)
    (hc : ∀ κ, (F.noise κ).Coins = (Fin (n κ) → Bool)) {g : List Bool → List Bool}
    (hg : PolyTimeComputable g)
    (hgf : ∀ κ c, g (pairEncode (List.replicate κ true) (List.ofFn (cast (hc κ) c))) =
      noiseWord ((F.noise κ).sample c)) (κ : ℕ) :
    (EfficientFamily.ofBitSeeds F hparams t n hn hc hg hgf).noiseInput κ =
      CoinSampling.seedModulusWord (n κ) := rfl

/-- The seed encoding of `EfficientFamily.ofBitSeeds F …` is `seedWord ∘ cast`. -/
theorem EfficientFamily.ofBitSeeds_encodeSeed (F : Family)
    (hparams : ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ κ, f (List.replicate κ true) = (F.parameters κ).encode (F.residueBits.eval κ))
    (t : PolyExpr) (n : ℕ → ℕ) (hn : ∀ κ, n κ = t.eval κ)
    (hc : ∀ κ, (F.noise κ).Coins = (Fin (n κ) → Bool)) {g : List Bool → List Bool}
    (hg : PolyTimeComputable g)
    (hgf : ∀ κ c, g (pairEncode (List.replicate κ true) (List.ofFn (cast (hc κ) c))) =
      noiseWord ((F.noise κ).sample c)) (κ : ℕ) (c : (F.noise κ).Coins) :
    (EfficientFamily.ofBitSeeds F hparams t n hn hc hg hgf).encodeSeed κ c =
      seedWord (cast (hc κ) c) := rfl

/-- **The dyadic efficient family with centered noise**: the schedule `n = N(κ)`, `m = M(κ)`,
`q = 2^{W(κ)}` (`dyadicFamily`) with noise `centeredNoise (T κ)`, its parameter map
(`dyadicFamily_params_uniform`) and its noise sampler (`centeredCore T`,
`centeredNoise_sample_cast`) proved efficient. No hardness is claimed. Glue. -/
def EfficientFamily.ofDyadic (N M W T : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ) :
    EfficientFamily :=
  EfficientFamily.ofBitSeeds (dyadicFamily N M W hW fun κ => centeredNoise (T.eval κ))
    (dyadicFamily_params_uniform N M W hW _) (T.add T) (fun κ => T.eval κ + T.eval κ)
    (fun κ => (PolyExpr.eval_add T T κ).symm) (fun κ => centeredNoise_Coins (T.eval κ))
    (polyTimeComputable_centeredCore T) fun κ c =>
      (centeredCore_ofFn T κ _).trans
        (congrArg noiseWord (centeredNoise_sample_cast (T.eval κ) c).symm)

/-- The family of `EfficientFamily.ofDyadic N M W T hW` is the dyadic family with noise
`centeredNoise (T κ)`. -/
theorem EfficientFamily.ofDyadic_toFamily (N M W T : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ) :
    (EfficientFamily.ofDyadic N M W T hW).toFamily =
      dyadicFamily N M W hW fun κ => centeredNoise (T.eval κ) := rfl

/-- The noise word of `EfficientFamily.ofDyadic N M W T hW` is
`CoinSampling.seedModulusWord (2 T(κ))`. -/
theorem EfficientFamily.ofDyadic_noiseInput (N M W T : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ)
    (κ : ℕ) :
    (EfficientFamily.ofDyadic N M W T hW).noiseInput κ =
      CoinSampling.seedModulusWord (T.eval κ + T.eval κ) := rfl

/-! ### Non-vacuity -/

/-- **A non-vacuity instance** of `EfficientFamily`: `n = κ + 1`, `m = 2(κ + 1)²`,
`q = 2^{κ+1}` and the centered noise `χ = centeredNoise 1`, the difference of two fair bits
(`EfficientFamily.ofDyadic`). Its parameter map and its noise sampler are proved efficient.
**No hardness is claimed**: this instance only shows that the structure is inhabited;
`DLWEAssumption dyadicExample.toFamily` is not asserted. Glue. -/
def dyadicExample : EfficientFamily :=
  EfficientFamily.ofDyadic (.add .var (.const 1)) (.mul (.const 2) (.pow (.add .var (.const 1)) 2))
    (.add .var (.const 1)) (.const 1)
    (fun κ => by
      rw [PolyExpr.eval_add, PolyExpr.eval_const]
      exact Nat.le_add_left 1 _)

/-- The parameters of `dyadicExample` at `κ`: dimension `κ + 1`, `2(κ + 1)²` samples and
modulus `2^{κ+1}`. -/
theorem dyadicExample_parameters (κ : ℕ) :
    (dyadicExample.parameters κ).dimension = κ + 1 ∧
      (dyadicExample.parameters κ).samples = 2 * (κ + 1) ^ 2 ∧
      (dyadicExample.parameters κ).modulus = 2 ^ (κ + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · show (PolyExpr.add .var (.const 1)).eval κ = κ + 1
    rw [PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
  · show (PolyExpr.mul (.const 2) (.pow (.add .var (.const 1)) 2)).eval κ = 2 * (κ + 1) ^ 2
    rw [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_pow, PolyExpr.eval_add,
      PolyExpr.eval_var, PolyExpr.eval_const]
  · show 2 ^ (PolyExpr.add .var (.const 1)).eval κ = 2 ^ (κ + 1)
    rw [PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]

/-- The noise of `dyadicExample` is `centeredNoise 1` at every `κ`. -/
theorem dyadicExample_noise (κ : ℕ) : dyadicExample.noise κ = centeredNoise 1 := by
  show centeredNoise ((PolyExpr.const 1).eval κ) = centeredNoise 1
  rw [PolyExpr.eval_const]

end TCSlib.Cryptography.LWE
