/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
-- ════════════════════════════════════════════════════════════════════════════════════════════
-- DRAFT FOR REVIEW: `briefs/io-components/sampler-bridge/Skeleton.lean` (design r1).
-- Statements only, proofs `sorry` (definitional readers by `rfl`). NOT checked by Lean: no
-- Lean slot was used. One file stands in for the eight proposed modules; the banners
-- `-- ═══ module …` mark where each would be cut. Imports are the union of theirs.
-- Names are proposals (design-r1.md §4); every one is open to review.
-- ════════════════════════════════════════════════════════════════════════════════════════════
import TCSlib.Cryptography.Asymptotic.Sampling           -- StatClose, uniformFromBits, rejectionSample
import TCSlib.Cryptography.Asymptotic.SamplingFinDist   -- statClose_iff_epsClose_map (interop)
import TCSlib.Cryptography.Asymptotic.ReductionSupport  -- Negligible.polyExpr_mul
import TCSlib.Cryptography.Games.Hopping                -- ProbComp, simulate, AllOutputs, accept
import TCSlib.Cryptography.Games.Bridges.Experiments    -- Bridge.expect_sample_eq_uexp
import TCSlib.Cryptography.Foundations.Subexponential   -- branch foundations/subexp (draft PR #374)
import TCSlib.Cryptography.LWE.Experiments              -- LWE.Noise, LWE.sample, decisionAdvantage
import TCSlib.Cryptography.Encoding.BinaryArith         -- toLE / fromLEPoly (MSB <-> LE adapters)
import TCSlib.Complexity.ClassP.BinaryArith.Div         -- BinArith.div, mod (and add, sub, lt, mul)
import TCSlib.Complexity.Randomized.Closure             -- NUPPT.layout, inArg, inCoins
import TCSlib.InformationTheory.Extractors              -- EpsClose (interop)
import Mathlib.Data.ZMod.Basic                          -- ZMod.finEquiv
import Mathlib.Data.Int.CardIntervalMod                 -- Nat.count_modEq_card (bucket fibres)
import Mathlib.Algebra.BigOperators.Fin                 -- finSigmaFinEquiv
import Mathlib.Logic.Equiv.Fin.Basic                    -- finProdFinEquiv

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Coin samplers: exact non-dyadic laws from fair coins, with perfect correctness kept

(Module docstring of the facade `TCSlib/Cryptography/CoinSampling.lean`; each module below
carries its own in the real layout.)

Experiments in the library are stated with **exact** laws: a uniform draw
`Games.ProbComp.sample Ω` of a finite type (uniform `ℤ_p` for a prime `p`, the seeds of
`LWE.Noise`, the LPN seed `Fin W × ℤ_p`) and its pushforwards. Honest algorithms and machines
only have fair coins, and `|Ω|` is not a power of two. This development connects the two
while keeping every *every-outcome* property (perfect correctness, encodings injective on
reachable objects, the sPRG complexity predicate) exact:

* **per sampler** (`CoinSampler Ω s`): a decoder from `s` fair coins to `Option Ω`, `none` meaning
  "give up", that is *exact on success*; its failure probability `fail` is derived. The
  canonical instance is the bucket sampler `bucket N s` of the design sketch (one draw
  `x < 2^s`, accepted iff `x < q·N` with `q = ⌊2^s/N⌋`, output `x mod N`), with
  `fail = (2^s mod N)/2^s < N/2^s`; the library's existing rejection sampler is an instance;
* **per experiment** (`Games.ProbComp.Close`): statistical closeness of computations, closed
  under sequencing and oracle simulation, so replacing exact draws by coin draws anywhere in a
  game moves every acceptance probability by at most the summed failure probabilities;
* **correctness** (`Games.OracleComp.OutputsSubset`): with a default value as the fallback, the
  coin version's possible outputs are possible outputs of the exact version, so every
  `AllOutputs` property transfers unchanged; a custom fallback branch is handled by
  `CoinSampler.allOutputs_draw_bind`;
* **asymptotics** (`drawSlack`): `q(κ)` draws with `t(κ) ≥ κ` slack bits each cost
  `q(κ)·2^{-t(κ)}`, negligible and `SubexpSmall c` for every `c < 1`;
* **efficiency** (`UniformSampler`): one polynomial-time string map on the NUPPT layout, the
  modulus read from the input, coins as the coin slot, built from the proved
  `Complexity.BinArith` arithmetic; its machine is `NUPPT.ofPolyTimeUniform`, uniform by
  construction (no advice, no κ-indexed family of programs, no hard-wired modulus).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1 and Definition 23.4: probabilistic algorithms on uniform coins; Lemma 51.17: rejection
  sampling is uniform conditioned on success; Definition 181.1: `ε`-closeness.)
* [Sho04] V. Shoup, *Sequences of games: a tool for taming complexity in security proofs*, IACR
  ePrint 2004/332, revision of 18 January 2006, §1.1 (statistical hops; the difference lemma).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, Lemma 3.1 (statistical distance bounds every advantage).
* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from Well-Founded
  Assumptions*, J. ACM 73(1), Article 1, February 2026, Definition 2.1 (subexponential
  indistinguishability) — the consumer of `subexpSmall_drawSlack`.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated 17 February 2016,
  Definitions 4.2.1 and 4.2.3 (the LWE instances).
* [Lem19] D. Lemire, *Fast Random Integer Generation in an Interval*, ACM Trans. Model. Comput.
  Simul. 29(1), 2019 — **candidate** citation for the single-draw "reject the top `2^s mod N`
  values, reduce mod `N`" sampler; to be confirmed (and ingested) before landing. Without it the
  bucket sampler is a library construction, design by Seyoon (records `IOComponentsPlan.md`,
  § Deferred library work, 2026-11-18).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge University
  Press, 2009, §7.2 (the binary-arithmetic machines of `Complexity.BinArith`).
-/

-- ═══ module TCSlib/Cryptography/CoinSampling/Basic.lean ═══════════════════════════════════════

namespace TCSlib.Cryptography.CoinSampling

open Finset

/-- **A coin sampler** of the finite type `Ω` from `s` fair coins: a decoder `dec` from `s`-bit
coin strings to `Option Ω`, where `none` means that the sampler gives up, which is **exact on
success**: any two elements of `Ω` are decoded with the same probability, so that conditioned on
success the output is exactly uniform on `Ω`. This is the property the library already proves
for its rejection-type samplers (`rejectionSample_uniform_of_some`, `firstHit_uniform_of_some`,
`permFromCoins_uniform_of_some`, `samplePrime_uniform_of_some`) and the hypothesis `huni` of
`statClose_getD_of_uniform_of_some` [PS10, Lemma 51.17]. The failure probability is the derived
quantity `fail`. A non-uniform exact law is the pushforward of a uniform seed (`RatSeed`,
`LWE.Noise.Coins`), the library's convention for exact laws, so uniform targets suffice. -/
structure CoinSampler (Ω : Type) [Fintype Ω] (s : ℕ) where
  /-- The decoder: an element of `Ω`, or `none` when the sampler gives up. -/
  dec : (Fin s → Bool) → Option Ω
  /-- Exact on success: any two elements of `Ω` are decoded with the same probability. -/
  uniform_of_some : ∀ a a' : Ω,
    uprob (fun c => dec c = some a) = uprob (fun c => dec c = some a')

namespace CoinSampler

variable {Ω Ω' : Type} [Fintype Ω] [Fintype Ω'] {s s' : ℕ}

/-- The **failure probability** of `S`: the probability over `s` uniform coins that the decoder
gives up, `fail S = Pr_c[dec c = none]`. -/
noncomputable def fail (S : CoinSampler Ω s) : ℝ :=
  uprob fun c : Fin s → Bool => S.dec c = none

/-- `S.fail = Pr_c[S.dec c = none]`. -/
theorem fail_eq (S : CoinSampler Ω s) :
    S.fail = uprob fun c : Fin s → Bool => S.dec c = none := rfl

/-- A failure probability is nonnegative: `0 ≤ S.fail` (`uprob_nonneg`). -/
theorem fail_nonneg (S : CoinSampler Ω s) : 0 ≤ S.fail := by
  sorry

/-- A failure probability is at most one: `S.fail ≤ 1` (`uprob_le_one`). -/
theorem fail_le_one (S : CoinSampler Ω s) : S.fail ≤ 1 := by
  sorry

/-- **The exact conditional law**: every element `a` of the nonempty type `Ω` is decoded with
probability `(1 − fail)/|Ω|`, `Pr_c[dec c = some a] = (1 − S.fail)/|Ω|`. [PS10, Lemma 51.17]
in the abstract form of the library's lemma C4.

**Proof sketch.** The `|Ω| + 1` events `{dec = some a}` and `{dec = none}` partition the coins
(`uprob_comp_eq_sum_fiber`, `Fintype.sum_option`), and the first `|Ω|` have one common value
(`uniform_of_some`), so `|Ω| · Pr[dec = some a] + fail = 1`. -/
theorem uprob_dec_eq_some [Nonempty Ω] (S : CoinSampler Ω s) (a : Ω) :
    uprob (fun c => S.dec c = some a) = (1 - S.fail) / Fintype.card Ω := by
  sorry

/-- **The mixture identity**: averaging any `F : Option Ω → ℝ` over the decoded coins is the
mixture of `F none` with weight `fail` and of the uniform average of `F ∘ some` with weight
`1 − fail`: `𝔼_c F(dec c) = fail · F(none) + (1 − fail) · 𝔼_{a ← Ω} F(some a)`. This exact
identity is the whole statistical content of "exact on success, fallback on failure".

**Proof sketch.** Group the coin sum by the value of `dec` (`uprob_comp_eq_sum_fiber`, summed
over `Option Ω` with `Fintype.sum_option`) and substitute `uprob_dec_eq_some`. The same
fibre decomposition is the step `hdec` of `statClose_getD_of_uniform_of_some`; the proposed dedup
(design §9, Q8) proves it once, here or beside that lemma, and derives both from it. -/
theorem uexp_comp_dec [Nonempty Ω] (S : CoinSampler Ω s) (F : Option Ω → ℝ) :
    uexp (fun c => F (S.dec c)) = S.fail * F none + (1 - S.fail) * uexp (fun a => F (some a)) := by
  sorry

/-- **The decoder is `fail`-close to the exact draw, failures included**: as samplers of
`Option Ω`, the coin decoder and `some` of a uniform element are `S.fail`-close,
`StatClose S.dec some S.fail` [PS10, Definition 181.1]. This is the `Option` form of
`statClose_getD_of_uniform_of_some` (which is its image under `getD d`), needed when the
fallback is a branch rather than a default value.

**Proof sketch.** For a test set `T` of `Option Ω`, the mixture identity with `F` the indicator
of `T` gives `Pr[T(dec c)] − Pr[T(some a)] = fail · (1_T(none) − Pr_a[T(some a)])`, of absolute
value at most `fail` (both indicator values lie in `[0, 1]`). -/
theorem statClose_some [Nonempty Ω] (S : CoinSampler Ω s) :
    StatClose S.dec (some : Ω → Option Ω) S.fail := by
  sorry

/-- **With a default value the decoder is `fail`-close to uniform**:
`StatClose (fun c => (dec c).getD d) id S.fail`. The existing abstract lemma C4,
`statClose_getD_of_uniform_of_some`, applied as it stands (no re-proof). -/
theorem statClose_getD [DecidableEq Ω] (S : CoinSampler Ω s) (d : Ω) :
    StatClose (fun c => (S.dec c).getD d) (id : Ω → Ω) S.fail :=
  statClose_getD_of_uniform_of_some S.dec S.uniform_of_some (S.fail_eq).ge d

/-- **Transport along a bijection** `e : Ω ≃ Ω'`: decode with `S`, then apply `e`. Exact on
success because `e` is a bijection; the failure event is unchanged. -/
def congr (S : CoinSampler Ω s) (e : Ω ≃ Ω') : CoinSampler Ω' s where
  dec c := (S.dec c).map e
  uniform_of_some a a' := by
    sorry

/-- `(S.congr e).dec c = (S.dec c).map e`. -/
theorem congr_dec (S : CoinSampler Ω s) (e : Ω ≃ Ω') (c : Fin s → Bool) :
    (S.congr e).dec c = (S.dec c).map e := rfl

/-- Transport keeps the failure probability: `(S.congr e).fail = S.fail` (`Option.map_eq_none`). -/
theorem fail_congr (S : CoinSampler Ω s) (e : Ω ≃ Ω') : (S.congr e).fail = S.fail := by
  sorry

/-- **Coins read through a bijection** `e` of coin strings: `(S.reindex e).dec c = S.dec (e c)`.
Exact on success and with the same failure probability, since a bijection of the coin space
preserves `uprob` (`uprob_comp_equiv`). -/
def reindex (S : CoinSampler Ω s) (e : (Fin s' → Bool) ≃ (Fin s → Bool)) : CoinSampler Ω s' where
  dec c := S.dec (e c)
  uniform_of_some a a' := by
    sorry

/-- `(S.reindex e).dec c = S.dec (e c)`. -/
theorem reindex_dec (S : CoinSampler Ω s) (e : (Fin s' → Bool) ≃ (Fin s → Bool))
    (c : Fin s' → Bool) : (S.reindex e).dec c = S.dec (e c) := rfl

/-- Reindexing keeps the failure probability: `(S.reindex e).fail = S.fail`
(`uprob_comp_equiv`). -/
theorem fail_reindex (S : CoinSampler Ω s) (e : (Fin s' → Bool) ≃ (Fin s → Bool)) :
    (S.reindex e).fail = S.fail := by
  sorry

/-- Block `j` of a string of `n · s` coins: the coins at the positions
`finProdFinEquiv (j, i) = i + s·j`, `i < s`. -/
def block {n : ℕ} (c : Fin (n * s) → Bool) (j : Fin n) : Fin s → Bool :=
  fun i => c (finProdFinEquiv (j, i))

/-- `block c j i = c (finProdFinEquiv (j, i))`. -/
theorem block_apply {n : ℕ} (c : Fin (n * s) → Bool) (j : Fin n) (i : Fin s) :
    block c j i = c (finProdFinEquiv (j, i)) := rfl

/-- **`n` independent draws**: decode each of the `n` blocks of `n · s` coins with `S`; the
result is `some` of the tuple when every block succeeds, `none` otherwise. Exact on success on
`Fin n → Ω` (the blocks are independent and each is exact on success). -/
def pi (n : ℕ) (S : CoinSampler Ω s) : CoinSampler (Fin n → Ω) (n * s) where
  dec c := if h : ∀ j, (S.dec (block c j)).isSome then
      some fun j => (S.dec (block c j)).get (h j) else none
  uniform_of_some f f' := by
    sorry

/-- The `n`-draw sampler succeeds with the tuple `f` exactly when every block decodes to its
coordinate: `(pi n S).dec c = some f ↔ ∀ j, S.dec (block c j) = some (f j)`. -/
theorem pi_dec_eq_some_iff (n : ℕ) (S : CoinSampler Ω s) (c : Fin (n * s) → Bool)
    (f : Fin n → Ω) : (pi n S).dec c = some f ↔ ∀ j, S.dec (block c j) = some (f j) := by
  sorry

/-- The `n`-draw sampler gives up exactly when some block does:
`(pi n S).dec c = none ↔ ∃ j, S.dec (block c j) = none`. -/
theorem pi_dec_eq_none_iff (n : ℕ) (S : CoinSampler Ω s) (c : Fin (n * s) → Bool) :
    (pi n S).dec c = none ↔ ∃ j, S.dec (block c j) = none := by
  sorry

/-- **Union bound for independent draws**: `(pi n S).fail ≤ n · S.fail`.

**Proof sketch.** `pi_dec_eq_none_iff` and `uprob_exists_le`; each block event has probability
`S.fail`, since the block map pushes uniform coins to uniform blocks (`uprob_comp_equiv` along
`Equiv.arrowCongr finProdFinEquiv` and `Equiv.curry`, then `uprob_fst`-style marginalisation). -/
theorem fail_pi_le (n : ℕ) (S : CoinSampler Ω s) : (pi n S).fail ≤ n * S.fail := by
  sorry

/-- **Two independent draws**: the first `s` coins decoded by `S`, the last `s'` by `S'`;
`some (a, b)` when both succeed. Exact on success on `Ω × Ω'`. -/
def prod (S : CoinSampler Ω s) (S' : CoinSampler Ω' s') : CoinSampler (Ω × Ω') (s + s') where
  dec c := (S.dec fun i => c (Fin.castAdd s' i)).bind fun a =>
    (S'.dec fun i => c (Fin.natAdd s i)).map fun b => (a, b)
  uniform_of_some p p' := by
    sorry

/-- `(S.prod S').dec c` decodes the two coin blocks and pairs the results. -/
theorem prod_dec (S : CoinSampler Ω s) (S' : CoinSampler Ω' s') (c : Fin (s + s') → Bool) :
    (S.prod S').dec c = (S.dec fun i => c (Fin.castAdd s' i)).bind fun a =>
      (S'.dec fun i => c (Fin.natAdd s i)).map fun b => (a, b) := rfl

/-- Union bound for two draws: `(S.prod S').fail ≤ S.fail + S'.fail` (`uprob_or_le`). -/
theorem fail_prod_le (S : CoinSampler Ω s) (S' : CoinSampler Ω' s') :
    (S.prod S').fail ≤ S.fail + S'.fail := by
  sorry

/-- **The library's rejection sampler as a coin sampler**: `rejectionSample m k T` (`T` trials of
`k` bits, the first value below `m`) on the `T` blocks of `T · k` coins. Exact on success is the
existing `rejectionSample_uniform_of_some` (moved along the block bijection) [PS10, Lemma 51.17].
Reuse, not a new sampler. -/
def ofRejection (m k T : ℕ) (hm : 0 < m) (hk : m ≤ 2 ^ k) : CoinSampler (Fin m) (T * k) where
  dec c := rejectionSample m k T (block c)
  uniform_of_some a a' := by
    sorry

/-- `(ofRejection m k T hm hk).dec c = rejectionSample m k T (block c)`. -/
theorem ofRejection_dec (m k T : ℕ) (hm : 0 < m) (hk : m ≤ 2 ^ k) (c : Fin (T * k) → Bool) :
    (ofRejection m k T hm hk).dec c = rejectionSample m k T (block c) := rfl

/-- The rejection sampler fails with probability `(1 − m/2^k)^T`: the existing
`uprob_rejectionSample_none`, moved along the block bijection. -/
theorem fail_ofRejection (m k T : ℕ) (hm : 0 < m) (hk : m ≤ 2 ^ k) :
    (ofRejection m k T hm hk).fail = (1 - (m : ℝ) / 2 ^ k) ^ T := by
  sorry

/-- **Every-outcome properties survive a default fallback** (seed-function form, for algorithms
written as functions of their exact seed, such as `Regev.keygen`): if `P (f a)` holds for every
seed `a`, it holds for `f ((dec c).getD d)` at every coin string `c`. -/
theorem forall_comp_getD (S : CoinSampler Ω s) {β : Type} {P : β → Prop} (f : Ω → β) (d : Ω)
    (h : ∀ a, P (f a)) (c : Fin s → Bool) : P (f ((S.dec c).getD d)) :=
  h _

/-- **Every-outcome properties survive a fallback branch that is correct by construction**: if
`P (f a)` holds for every seed `a` and `P fb` holds for the fallback `fb`, then
`P ((dec c).elim fb f)` holds at every coin string `c`. -/
theorem forall_comp_elim (S : CoinSampler Ω s) {β : Type} {P : β → Prop} (f : Ω → β) (fb : β)
    (h : ∀ a, P (f a)) (hfb : P fb) (c : Fin s → Bool) : P ((S.dec c).elim fb f) := by
  sorry

end CoinSampler

-- ═══ module TCSlib/Cryptography/CoinSampling/Buckets.lean ══════════════════════════════════════

/-- **The bucket decoder** (Seyoon's sketch): read the `s` coins as a number `x < 2^s`
(`bitsToNat`, as `uniformFromBits` does); with `q = ⌊2^s/N⌋`, accept iff `x < q·N` and output
`x mod N`, the second coordinate of `finProdFinEquiv.symm x : Fin q × Fin N`. Each residue has
exactly `q` preimages below `q·N` (equal buckets), so the output is exactly uniform on success;
the leftover `2^s mod N` values give up. One rejection trial (`uniformFromBits`) at the threshold
`q·N`, followed by a reduction. [Lem19] (candidate), library construction otherwise. -/
def bucketDec (N s : ℕ) (c : Fin s → Bool) : Option (Fin N) :=
  (uniformFromBits (2 ^ s / N * N) s c).map fun x => (finProdFinEquiv.symm x).2

/-- `bucketDec N s c` is the one-trial rejection read `uniformFromBits (⌊2^s/N⌋·N) s c`,
reduced modulo `N` through `finProdFinEquiv.symm`. -/
theorem bucketDec_eq (N s : ℕ) (c : Fin s → Bool) :
    bucketDec N s c =
      (uniformFromBits (2 ^ s / N * N) s c).map fun x => (finProdFinEquiv.symm x).2 := rfl

/-- The bucket decoder outputs `a` exactly when the coins read below `⌊2^s/N⌋·N` and are
congruent to `a` mod `N`: `bucketDec N s c = some a ↔ x < ⌊2^s/N⌋·N ∧ x % N = a` with
`x = bitsToNat c`. -/
theorem bucketDec_eq_some_iff (N s : ℕ) (c : Fin s → Bool) (a : Fin N) :
    bucketDec N s c = some a ↔ bitsToNat c < 2 ^ s / N * N ∧ bitsToNat c % N = a := by
  sorry

/-- The bucket decoder gives up exactly when the coins read at least `⌊2^s/N⌋·N`. -/
theorem bucketDec_eq_none_iff (N s : ℕ) (c : Fin s → Bool) :
    bucketDec N s c = none ↔ 2 ^ s / N * N ≤ bitsToNat c := by
  sorry

/-- **Equal buckets**: every residue is output with probability `⌊2^s/N⌋ / 2^s`.

**Proof sketch.** By `bucketDec_eq_some_iff` the event is the union over the `q = ⌊2^s/N⌋`
values `x < q·N` with `x % N = a` (the fibre of `a` under `Prod.snd ∘ finProdFinEquiv.symm`, of
size `q`; or `Nat.count_modEq_card` with `q·N % N = 0`) of `{uniformFromBits = some x}`, each of
probability `1/2^s` (`uprob_uniformFromBits_eq_some`, valid as `q·N ≤ 2^s`,
`Nat.div_mul_le_self`). -/
theorem uprob_bucketDec_eq_some (N s : ℕ) (a : Fin N) :
    uprob (fun c => bucketDec N s c = some a) = ((2 ^ s / N : ℕ) : ℝ) / 2 ^ s := by
  sorry

/-- **The bucket sampler** of `Fin N` from `s` coins: `bucketDec N s`, exact on success by
`uprob_bucketDec_eq_some`. -/
def bucket (N s : ℕ) : CoinSampler (Fin N) s where
  dec := bucketDec N s
  uniform_of_some a a' := by rw [uprob_bucketDec_eq_some, uprob_bucketDec_eq_some]

/-- `(bucket N s).dec = bucketDec N s`. -/
theorem bucket_dec (N s : ℕ) : (bucket N s).dec = bucketDec N s := rfl

/-- **The bucket failure probability, exactly**: `(bucket N s).fail = (2^s mod N)/2^s`
(also for `N = 0`, where it is `1`).

**Proof sketch.** `uprob_uniformFromBits_none` gives `1 − ⌊2^s/N⌋·N/2^s`, and
`2^s = ⌊2^s/N⌋·N + 2^s mod N` (`Nat.div_add_mod`). -/
theorem fail_bucket (N s : ℕ) : (bucket N s).fail = ((2 ^ s % N : ℕ) : ℝ) / 2 ^ s := by
  sorry

/-- **The design sketch's bound**: for `0 < N`, the bucket sampler fails with probability
`< N/2^s` (`2^s mod N < N`). -/
theorem fail_bucket_lt {N : ℕ} (hN : 0 < N) (s : ℕ) : (bucket N s).fail < N / 2 ^ s := by
  sorry

/-- **Slack bits**: if `0 < N ≤ 2^b`, the bucket sampler with `b + t` coins fails with
probability at most `2^{-t}`: `(bucket N (b + t)).fail ≤ (2⁻¹)^t`. (`fail_bucket_lt` and
`N/2^{b+t} ≤ 2^{-t}`.) -/
theorem fail_bucket_le {N b : ℕ} (hN0 : 0 < N) (hN : N ≤ 2 ^ b) (t : ℕ) :
    (bucket N (b + t)).fail ≤ (2 : ℝ)⁻¹ ^ t := by
  sorry

/-- **Uniform on any finite type through an enumeration** `e : Ω ≃ Fin N`: the bucket sampler
of `Fin N`, transported along `e.symm`. Efficient decoding needs a computable `e`
(`ZMod.finEquiv`, `finProdFinEquiv`, `finSigmaFinEquiv`); `Fintype.equivFin` serves laws only. -/
def ofEquiv {Ω : Type} [Fintype Ω] {N : ℕ} (e : Ω ≃ Fin N) (s : ℕ) : CoinSampler Ω s :=
  (bucket N s).congr e.symm

/-- `(ofEquiv e s).dec c = (bucketDec N s c).map e.symm`. -/
theorem ofEquiv_dec {Ω : Type} [Fintype Ω] {N : ℕ} (e : Ω ≃ Fin N) (s : ℕ) (c : Fin s → Bool) :
    (ofEquiv e s).dec c = (bucketDec N s c).map e.symm := rfl

/-- `(ofEquiv e s).fail = (bucket N s).fail` (`CoinSampler.fail_congr`). -/
theorem fail_ofEquiv {Ω : Type} [Fintype Ω] {N : ℕ} (e : Ω ≃ Fin N) (s : ℕ) :
    (ofEquiv e s).fail = (bucket N s).fail := by
  sorry

/-- **The seed type of a rational law** with integer weights `w : α → ℕ`: one element per unit
of weight, `Σ a, Fin (w a)`. Its uniform law pushed along `Sigma.fst` is the law
`a ↦ w a / Σ_b w b` (`uprob_ratSeed_fst`): the "weighted buckets" of the design sketch. -/
abbrev RatSeed {α : Type} (w : α → ℕ) : Type := Σ a, Fin (w a)

/-- `RatSeed w = Σ a, Fin (w a)`. -/
theorem ratSeed_eq {α : Type} (w : α → ℕ) : RatSeed w = (Σ a, Fin (w a)) := rfl

/-- **The rational law of a seed**: a uniform seed of `RatSeed w` has first coordinate `a` with
probability `w a / Σ_b w b`.

**Proof sketch.** The fibre of `a` under `Sigma.fst` has `w a` elements and the type has
`Σ_b w b` (`Fintype.card_sigma`); `uprob_eq_card_filter`. -/
theorem uprob_ratSeed_fst {α : Type} [Fintype α] [DecidableEq α] (w : α → ℕ) (a : α) :
    uprob (fun x : RatSeed w => x.1 = a) = (w a : ℝ) / ∑ b, w b := by
  sorry

/-- **Weighted buckets** for weights indexed by `Fin m`: the bucket sampler of
`Fin (Σ_i w i)` read through Mathlib's `finSigmaFinEquiv` (cumulative buckets: value `i` owns
the `w i` consecutive indices after `Σ_{i' < i} w i'`). -/
def weighted {m : ℕ} (w : Fin m → ℕ) (s : ℕ) : CoinSampler (RatSeed w) s :=
  ofEquiv finSigmaFinEquiv s

/-- `weighted w s = ofEquiv finSigmaFinEquiv s`. -/
theorem weighted_eq {m : ℕ} (w : Fin m → ℕ) (s : ℕ) :
    weighted w s = ofEquiv finSigmaFinEquiv s := rfl

end TCSlib.Cryptography.CoinSampling

-- ═══ module TCSlib/Cryptography/Games/Closeness.lean ═══════════════════════════════════════════

namespace TCSlib.Cryptography.Games

open TCSlib.InformationTheory

variable {ι : Type} {α β σ : Type}

namespace ProbComp

/-- **Statistical closeness of computations**: `c₁` and `c₂` are `ε`-close when every function of
the output with values in `[0, 1]` has expectations differing by at most `ε`,
`|𝔼_{c₁} g − 𝔼_{c₂} g| ≤ ε`; for a finite output type this is `EpsClose ε` of the output
distributions (`close_iff_epsClose_dist`). [PS10, Definition 181.1] for computations, with
`[0, 1]`-valued tests in place of distinguishers so that it is closed under sequencing
(`Close.bind_left`). -/
def Close (ε : ℝ) (c₁ c₂ : ProbComp α) : Prop :=
  ∀ g : α → ℝ, (∀ a, 0 ≤ g a ∧ g a ≤ 1) → |expect c₁ g - expect c₂ g| ≤ ε

/-- `Close ε c₁ c₂ ↔ ∀ g ∈ [0,1]^α, |𝔼_{c₁} g − 𝔼_{c₂} g| ≤ ε`. -/
theorem close_iff (ε : ℝ) (c₁ c₂ : ProbComp α) :
    Close ε c₁ c₂ ↔ ∀ g : α → ℝ, (∀ a, 0 ≤ g a ∧ g a ≤ 1) →
      |expect c₁ g - expect c₂ g| ≤ ε := Iff.rfl

/-- A closeness bound is nonnegative (test `g = 0`). -/
theorem Close.nonneg {ε : ℝ} {c₁ c₂ : ProbComp α} (h : Close ε c₁ c₂) : 0 ≤ ε := by
  sorry

/-- Every computation is `0`-close to itself. -/
theorem Close.refl (c : ProbComp α) : Close 0 c c := by
  sorry

/-- Closeness is symmetric. -/
theorem Close.symm {ε : ℝ} {c₁ c₂ : ProbComp α} (h : Close ε c₁ c₂) : Close ε c₂ c₁ := by
  sorry

/-- A closeness bound may be weakened. -/
theorem Close.mono {ε ε' : ℝ} {c₁ c₂ : ProbComp α} (h : Close ε c₁ c₂) (hε : ε ≤ ε') :
    Close ε' c₁ c₂ := by
  sorry

/-- Closeness bounds add along a chain (triangle inequality): the statistical hops of
[Sho04, §1.1] compose. -/
theorem Close.trans {ε ε' : ℝ} {c₁ c₂ c₃ : ProbComp α} (h : Close ε c₁ c₂)
    (h' : Close ε' c₂ c₃) : Close (ε + ε') c₁ c₃ := by
  sorry

/-- Computations with the same expectations are `0`-close; with `expect_simulate_congr` and
`expect_simulate_rel` this is how exact identities enter a chain of hops. -/
theorem close_of_expect_eq {c₁ c₂ : ProbComp α} (h : ∀ g, expect c₁ g = expect c₂ g) :
    Close 0 c₁ c₂ := by
  sorry

/-- **Sequencing on the left**: if `c₁` and `c₂` are `ε`-close, so are `c₁ >>= f` and `c₂ >>= f`.

**Proof sketch.** `expect_bind`: the test `a ↦ 𝔼_{f a} g` has values in `[0, 1]`
(`expect_nonneg`, `expect_mono`, `expect_const`). -/
theorem Close.bind_left {ε : ℝ} {c₁ c₂ : ProbComp α} (h : Close ε c₁ c₂) (f : α → ProbComp β) :
    Close ε (c₁.bind f) (c₂.bind f) := by
  sorry

/-- **Sequencing on the right**: if `f₁ a` and `f₂ a` are `ε`-close for every `a`, so are
`c >>= f₁` and `c >>= f₂` (`expect_bind`, `abs_expect_sub_le`). -/
theorem Close.bind_right {ε : ℝ} (c : ProbComp α) {f₁ f₂ : α → ProbComp β}
    (h : ∀ a, Close ε (f₁ a) (f₂ a)) : Close ε (c.bind f₁) (c.bind f₂) := by
  sorry

/-- **Sequencing**: `ε`-close first steps and `ε'`-close continuations give `(ε + ε')`-close
sequences (`bind_left`, `bind_right`, `trans`). -/
theorem Close.bind {ε ε' : ℝ} {c₁ c₂ : ProbComp α} {f₁ f₂ : α → ProbComp β}
    (h : Close ε c₁ c₂) (h' : ∀ a, Close ε' (f₁ a) (f₂ a)) :
    Close (ε + ε') (c₁.bind f₁) (c₂.bind f₂) := by
  sorry

/-- Post-processing keeps closeness: `Close ε (h <$> c₁) (h <$> c₂)` (`expect_map`). -/
theorem Close.map {ε : ℝ} {c₁ c₂ : ProbComp α} (h : Close ε c₁ c₂) (k : α → β) :
    Close ε (k <$> c₁) (k <$> c₂) := by
  sorry

/-- Events move by at most `ε`: `|Pr_{c₁}[p] − Pr_{c₂}[p]| ≤ ε` (the indicator is a test). -/
theorem Close.abs_prob_sub_le {ε : ℝ} {c₁ c₂ : ProbComp α} (h : Close ε c₁ c₂) (p : α → Prop) :
    |prob c₁ p - prob c₂ p| ≤ ε := by
  sorry

/-- **Oracle simulation**: if every call of `impl₀` is `ε`-close to the same call of `impl₁`,
then for a computation with at most `m` queries the two simulations are `m · ε`-close. The
`ε = 0` case is `expect_simulate_congr`.

**Proof sketch.** Induction on the computation with its budget, as in `prob_bad_le`: at a
query, `Close.bind` with the call (`ε`) and the continuations (`(m − 1) · ε`, induction). -/
theorem Close.simulate {spec : OracleSpec ι} {impl₀ impl₁ : QueryImpl spec σ unifSpec} {ε : ℝ}
    (h : ∀ i x s, Close ε (impl₀ i x s) (impl₁ i x s)) (c : OracleComp spec α) (m : ℕ)
    (hc : c.CostBoundedBy (fun _ => 1) m) (s : σ) :
    Close (m * ε) (Games.simulate impl₀ c s) (Games.simulate impl₁ c s) := by
  sorry

-- interop (optional in the first PR; design §4.3)
/-- **Closeness of computations is closeness of their output laws** on a finite output type:
`Close ε c₁ c₂ ↔ EpsClose ε (dist c₁) (dist c₂)` [PS10, Definition 181.1].

**Proof sketch.** (→) a distinguisher's indicator is a test. (←) write `𝔼_c g` as
`Σ_a dist c a · g a` (a reader `expect_eq_sum_dist`, new) and bound
`|Σ_a (p a − q a) g a| ≤ statDist p q` for `g ∈ [0, 1]` (the `[0, 1]`-weight form of
`abs_probTrue_sub_le_statDist`, new), then `epsClose_iff_statDist_le`. -/
theorem close_iff_epsClose_dist [Fintype α] [DecidableEq α] {ε : ℝ} (c₁ c₂ : ProbComp α) :
    Close ε c₁ c₂ ↔ EpsClose ε (dist c₁) (dist c₂) := by
  sorry

end ProbComp

/-- Acceptance probabilities of `ε`-close games differ by at most `ε`. -/
theorem ProbComp.Close.abs_accept_sub_le {ε : ℝ} {G₁ G₂ : ProbComp Bool}
    (h : ProbComp.Close ε G₁ G₂) : |accept G₁ - accept G₂| ≤ ε := by
  sorry

/-- **Advantage transfer**: replacing each of two games by an `ε_b`-close one changes the
distinguishing advantage by at most `ε₀ + ε₁`: `advantage G₀' G₁' ≤ advantage G₀ G₁ + ε₀ + ε₁`
[Gar26, Lemma 3.1]. -/
theorem advantage_le_of_close {ε₀ ε₁ : ℝ} {G₀ G₁ G₀' G₁' : ProbComp Bool}
    (h₀ : ProbComp.Close ε₀ G₀' G₀) (h₁ : ProbComp.Close ε₁ G₁' G₁) :
    advantage G₀' G₁' ≤ advantage G₀ G₁ + ε₀ + ε₁ := by
  sorry

namespace OracleComp

variable {spec : OracleSpec ι}

/-- **Output inclusion**: every possible output of `c₁` is a possible output of `c₂`, read
through predicates: whatever holds at all outputs of `c₂` holds at all outputs of `c₁`. The
relation along which perfect correctness and every other `AllOutputs` property transfer. -/
def OutputsSubset (c₁ c₂ : OracleComp spec α) : Prop :=
  ∀ P : α → Prop, c₂.AllOutputs P → c₁.AllOutputs P

/-- `OutputsSubset c₁ c₂ ↔ ∀ P, c₂.AllOutputs P → c₁.AllOutputs P`. -/
theorem outputsSubset_iff (c₁ c₂ : OracleComp spec α) :
    OutputsSubset c₁ c₂ ↔ ∀ P : α → Prop, c₂.AllOutputs P → c₁.AllOutputs P := Iff.rfl

/-- Possible outputs of a sequence, in both directions: `(c >>= f).AllOutputs Q` iff every
possible output `a` of `c` has `(f a).AllOutputs Q`. (The `←` direction is `AllOutputs.bind`;
`→` is a new induction on `c`.) -/
theorem allOutputs_bind_iff {c : OracleComp spec α} {f : α → OracleComp spec β}
    {Q : β → Prop} : (c.bind f).AllOutputs Q ↔ c.AllOutputs fun a => (f a).AllOutputs Q := by
  sorry

/-- Output inclusion is reflexive. -/
theorem OutputsSubset.refl (c : OracleComp spec α) : OutputsSubset c c := fun _ h => h

/-- Output inclusion is transitive. -/
theorem OutputsSubset.trans {c₁ c₂ c₃ : OracleComp spec α} (h : OutputsSubset c₁ c₂)
    (h' : OutputsSubset c₂ c₃) : OutputsSubset c₁ c₃ := fun P hP => h P (h' P hP)

/-- **Sequencing**: included first steps and included continuations give included sequences.

**Proof sketch.** `allOutputs_bind_iff` on `c₂ >>= f₂`, then `h` with the predicate
`a ↦ (f₂ a).AllOutputs P`, then `h'` pointwise and `AllOutputs.bind`. -/
theorem OutputsSubset.bind {c₁ c₂ : OracleComp spec α} {f₁ f₂ : α → OracleComp spec β}
    (h : OutputsSubset c₁ c₂) (h' : ∀ a, OutputsSubset (f₁ a) (f₂ a)) :
    OutputsSubset (c₁.bind f₁) (c₂.bind f₂) := by
  sorry

/-- **Oracle simulation**: implementations whose every call is output-included give
output-included simulations (induction on the computation, `OutputsSubset.bind`). -/
theorem OutputsSubset.simulate {spec' : OracleSpec ι} {impl₀ impl₁ : QueryImpl spec' σ unifSpec}
    (h : ∀ i x s, OutputsSubset (impl₀ i x s) (impl₁ i x s)) (c : OracleComp spec' α) (s : σ) :
    OutputsSubset (Games.simulate impl₀ c s) (Games.simulate impl₁ c s) := by
  sorry

end OracleComp

end TCSlib.Cryptography.Games

-- ═══ module TCSlib/Cryptography/CoinSampling/Transfer.lean ═════════════════════════════════════

namespace TCSlib.Cryptography.CoinSampling

open TCSlib.Cryptography.Games

namespace CoinSampler

variable {Ω β : Type} [Fintype Ω] {s : ℕ}

/-- **A draw through the sampler**: `s` uniform coins, decoded; `none` when it gives up. -/
noncomputable def draw (S : CoinSampler Ω s) : ProbComp (Option Ω) :=
  S.dec <$> ProbComp.sample (Fin s → Bool)

/-- `S.draw = S.dec <$> sample (Fin s → Bool)`. -/
theorem draw_eq (S : CoinSampler Ω s) :
    S.draw = S.dec <$> ProbComp.sample (Fin s → Bool) := rfl

/-- **A draw with the default fallback** `d`: the decoded value, or `d` when the sampler gives
up. The standard fallback (design §4.4): `d` is a legitimate exact outcome, so no format
changes and every `AllOutputs` property transfers (`outputsSubset_drawD`). -/
noncomputable def drawD (S : CoinSampler Ω s) (d : Ω) : ProbComp Ω :=
  (fun c => (S.dec c).getD d) <$> ProbComp.sample (Fin s → Bool)

/-- `S.drawD d = (fun c => (S.dec c).getD d) <$> sample (Fin s → Bool)`. -/
theorem drawD_eq (S : CoinSampler Ω s) (d : Ω) :
    S.drawD d = (fun c => (S.dec c).getD d) <$> ProbComp.sample (Fin s → Bool) := rfl

/-- **The mixture identity for games**: for every `F : Option Ω → ℝ`,
`𝔼_{S.draw} F = fail · F(none) + (1 − fail) · 𝔼_{a ← Ω} F(some a)`
(`expect_map`, `Bridge.expect_sample_eq_uexp`, `uexp_comp_dec`). -/
theorem expect_draw [Nonempty Ω] (S : CoinSampler Ω s) (F : Option Ω → ℝ) :
    ProbComp.expect S.draw F =
      S.fail * F none + (1 - S.fail) * ProbComp.expect (ProbComp.sample Ω) (fun a => F (some a)) := by
  sorry

/-- **One draw, any fallback branch**: a game that draws through `S` and continues with `K`
(`K none` is the fallback) is `fail`-close to the game that draws exactly and continues with
`K ∘ some`.

**Proof sketch.** `expect_bind`, then `expect_draw` with `F o = 𝔼_{K o} g ∈ [0, 1]`: the
difference is `fail · (F none − 𝔼_a F(some a))`, of absolute value at most `fail`. -/
theorem close_draw_bind [Nonempty Ω] (S : CoinSampler Ω s) (K : Option Ω → ProbComp β) :
    ProbComp.Close S.fail (S.draw.bind K) ((ProbComp.sample Ω).bind fun a => K (some a)) := by
  sorry

/-- **One draw, default fallback**: `S.drawD d >>= k` is `fail`-close to `sample Ω >>= k`
(`close_draw_bind` with `K o = k (o.getD d)`). -/
theorem close_drawD_bind [Nonempty Ω] (S : CoinSampler Ω s) (d : Ω) (k : Ω → ProbComp β) :
    ProbComp.Close S.fail ((S.drawD d).bind k) ((ProbComp.sample Ω).bind k) := by
  sorry

/-- **A fresh draw per oracle query**: an oracle whose every call draws through `S` (body `K`,
fallback `K … none`) is, over a computation with at most `m` queries, `m · fail`-close to the
oracle that draws exactly (`ProbComp.Close.simulate` with `close_draw_bind`). This is the
per-experiment summed failure bound for draws made inside oracles (keys per `KeyGen` query). -/
theorem close_simulate_draw [Nonempty Ω] {ι σ α : Type} {spec : OracleSpec ι}
    (S : CoinSampler Ω s) (K : ∀ i, spec.dom i → σ → Option Ω → ProbComp (spec.rng i × σ))
    (c : OracleComp spec α) (m : ℕ) (hc : c.CostBoundedBy (fun _ => 1) m) (st : σ) :
    ProbComp.Close (m * S.fail)
      (Games.simulate (fun i x st' => S.draw.bind (K i x st')) c st)
      (Games.simulate (fun i x st' => (ProbComp.sample Ω).bind fun a => K i x st' (some a)) c st) := by
  sorry

/-- **The possible outputs of an exact draw are all values**:
`(sample T).AllOutputs P ↔ ∀ t, P t` (`sample_eq`, `allOutputs_query`, and surjectivity of
the enumeration `(Fintype.equivFin T).symm`). -/
theorem allOutputs_sample_iff {T : Type} [Fintype T] [Nonempty T] {P : T → Prop} :
    (ProbComp.sample T).AllOutputs P ↔ ∀ t, P t := by
  sorry

/-- **A default fallback only shrinks the possible outputs**: every possible output of
`S.drawD d` is a possible output of `sample Ω` (it is an element of `Ω`; `allOutputs_sample_iff`).
With `OracleComp.OutputsSubset.bind` and `.simulate`, a scheme whose exact draws are replaced by
default-fallback coin draws keeps **every** `AllOutputs` property: perfect correctness
(`IBEScheme.Correct`, the FE `Correct`), the reachable-encoding injectivity fields, and the
sPRG predicate `SPRG.HasComplexity`. -/
theorem outputsSubset_drawD (S : CoinSampler Ω s) (d : Ω) [Nonempty Ω] :
    OracleComp.OutputsSubset (S.drawD d) (ProbComp.sample Ω) := by
  sorry

/-- **A fallback branch that is correct by construction keeps correctness**: if every
continuation `K (some a)` and the fallback `K none` satisfy `P` at all outputs, so does the
coin draw followed by `K` (`allOutputs_true`, `AllOutputs.bind`). The form for fallbacks that
change the output format, such as sending in the clear. -/
theorem allOutputs_draw_bind (S : CoinSampler Ω s) {K : Option Ω → ProbComp β} {P : β → Prop}
    (hsome : ∀ a, (K (some a)).AllOutputs P) (hnone : (K none).AllOutputs P) :
    (S.draw.bind K).AllOutputs P := by
  sorry

end CoinSampler

-- ═══ module TCSlib/Cryptography/CoinSampling/Asymptotic.lean ═══════════════════════════════════
-- (the only module importing Foundations.Subexponential: draft PR #374)

open Complexity

/-- **The slack of `q(κ)` coin draws with `t(κ)` slack bits each**: `q(κ) · 2^{-t(κ)}`. By
`fail_bucket_le`, a bucket draw of a modulus `N ≤ 2^b` with `b + t` coins costs at most
`2^{-t}`, so the summed failure bound of a game making at most `q(κ)` draws is
`drawSlack q t κ`. -/
noncomputable def drawSlack (q t : PolyExpr) (κ : ℕ) : ℝ := (q.eval κ : ℝ) * (2 : ℝ)⁻¹ ^ t.eval κ

/-- `drawSlack q t κ = q(κ) · (2⁻¹)^{t(κ)}`. -/
theorem drawSlack_eq (q t : PolyExpr) (κ : ℕ) :
    drawSlack q t κ = (q.eval κ : ℝ) * (2 : ℝ)⁻¹ ^ t.eval κ := rfl

/-- **The slack is negligible** when `t(κ) ≥ κ`: `negligible_two_pow_neg`, moved to `t` by
monotonicity (`Negligible.mono`), times the polynomial `q` (`Negligible.polyExpr_mul`). -/
theorem negligible_drawSlack (q t : PolyExpr) (ht : ∀ κ, κ ≤ t.eval κ) :
    Negligible (drawSlack q t) := by
  sorry

/-- **The slack is subexponentially small** for every exponent `c < 1` when `t(κ) ≥ κ`
[JLS26, Definition 2.1]: `subexpSmall_two_pow_neg` (exponent `1`), moved to `t`
(`SubexpSmall.mono`), times the normal-form majorant `C(κ+1)^d` of `q` (`PolyExpr.eval_le`,
`SubexpSmall.mul_pow`, `SubexpSmall.const_mul`, each lowering the exponent strictly). -/
theorem subexpSmall_drawSlack (q t : PolyExpr) (ht : ∀ κ, κ ≤ t.eval κ) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) : SubexpSmall c (drawSlack q t) := by
  sorry

/-- **Per-draw bound along a modulus schedule**: if `0 < N(κ) ≤ 2^{b(κ)}`, the bucket sampler
with `b(κ) + t(κ)` coins fails with probability at most `2^{-t(κ)}` (`fail_bucket_le`). The
modulus is a value here (a law parameter), not a hard-wired program constant: the program reads
it from its input (`bucketSampler`). -/
theorem fail_bucket_schedule_le (N : ℕ → ℕ) (b t : PolyExpr) (hN0 : ∀ κ, 0 < N κ)
    (hN : ∀ κ, N κ ≤ 2 ^ b.eval κ) (κ : ℕ) :
    (bucket (N κ) ((b.add t).eval κ)).fail ≤ (2 : ℝ)⁻¹ ^ t.eval κ := by
  sorry

-- ═══ module TCSlib/Cryptography/CoinSampling/Instances.lean ════════════════════════════════════

namespace CoinSampler

/-- **Uniform residues modulo `q`**: the bucket sampler of `Fin q` read through Mathlib's
`ZMod.finEquiv q` [Pei16, Definition 4.2.3: the uniform matrix and secret of LWE]. -/
def zmod (q : ℕ) [NeZero q] (s : ℕ) : CoinSampler (ZMod q) s :=
  (bucket q s).congr (ZMod.finEquiv q).toEquiv

/-- `(zmod q s).dec c = (bucketDec q s c).map (ZMod.finEquiv q)`. -/
theorem zmod_dec (q : ℕ) [NeZero q] (s : ℕ) (c : Fin s → Bool) :
    (zmod q s).dec c = (bucketDec q s c).map (ZMod.finEquiv q).toEquiv := rfl

/-- With `q ≤ 2^b`, the residue sampler with `b + t` coins fails with probability at most
`2^{-t}` (`fail_congr`, `fail_bucket_le`). -/
theorem fail_zmod_le (q : ℕ) [NeZero q] {b : ℕ} (hq : q ≤ 2 ^ b) (t : ℕ) :
    (zmod q (b + t)).fail ≤ (2 : ℝ)⁻¹ ^ t := by
  sorry

/-- **Seeds of a finite LWE noise law** [Pei16, Definition 4.2.1, finite-seed specialization of
`LWE.Noise`]: the bucket sampler of `χ.Coins` through its enumeration (laws only; an efficient
noise sampler supplies a computable enumeration, as `bitNoise` needs none). -/
noncomputable def noiseSeeds (χ : LWE.Noise) (s : ℕ) : CoinSampler χ.Coins s :=
  ofEquiv (Fintype.equivFin χ.Coins) s

/-- The seed type of `LWE.sample P χ`: the matrix, one common secret, one noise seed per row. -/
abbrev LWESeed (P : LWE.Parameters) (χ : LWE.Noise) : Type :=
  Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
    ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))

/-- `LWESeed P χ` is the seed type of `LWE.sample P χ`. -/
theorem lweSeed_eq (P : LWE.Parameters) (χ : LWE.Noise) :
    LWESeed P χ = (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) := rfl

/-- **The LWE seed from fair coins** at any modulus (dyadic or not): `m · n` residues for the
matrix, `n` for the secret, `m` noise seeds, all independent (`pi`, `prod`, `Matrix.of`).
Complements `LWE.sampleFromBits`, exact only for `q = 2^width`. -/
noncomputable def lweSeeds (P : LWE.Parameters) (χ : LWE.Noise) (s s' : ℕ) :
    CoinSampler (LWESeed P χ)
      (P.samples * (P.dimension * s) + (P.dimension * s + P.samples * s')) :=
  ((pi P.samples (pi P.dimension (zmod P.modulus s))).congr Matrix.of).prod
    ((pi P.dimension (zmod P.modulus s)).prod (pi P.samples (noiseSeeds χ s')))

/-- Union bound for the LWE seed: `fail ≤ (m n + n) · fail(zmod) + m · fail(noise)`
(`fail_prod_le`, `fail_pi_le`, `fail_congr`). -/
theorem fail_lweSeeds_le (P : LWE.Parameters) (χ : LWE.Noise) (s s' : ℕ) :
    (lweSeeds P χ s s').fail ≤
      (P.samples * P.dimension + P.dimension) * (zmod P.modulus s).fail +
        P.samples * (noiseSeeds χ s').fail := by
  sorry

/-- **The LWE challenge from fair coins** (default fallback `d`) is `fail`-close to the exact
challenge: `statClose_getD`, post-processed by `LWE.sample P χ` (`StatClose.map`). -/
theorem statClose_lweSample_coins (P : LWE.Parameters) (χ : LWE.Noise) (s s' : ℕ)
    [DecidableEq (LWESeed P χ)] (d : LWESeed P χ) :
    StatClose (fun c => LWE.sample P χ (((lweSeeds P χ s s').dec c).getD d)) (LWE.sample P χ)
      (lweSeeds P χ s s').fail := by
  sorry

/-- **Distinguishers transfer**: any distinguisher's advantage between the coin-implemented LWE
challenge and uniform exceeds its `decisionAdvantage` by at most the seed failure probability
(`StatClose.abs_uprob_sub_le_prod` on the real side, `distAdv_def`, `acceptProb_def`). The form a
`LWE.Family` implementation contract consumes. -/
theorem distAdv_lweSample_coins_le {ρ : Type} [Fintype ρ] [Nonempty ρ] (P : LWE.Parameters)
    (χ : LWE.Noise) (s s' : ℕ) [DecidableEq (LWESeed P χ)] (d : LWESeed P χ)
    (D : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) → ρ → Bool) :
    distAdv (fun c => LWE.sample P χ (((lweSeeds P χ s s').dec c).getD d)) id D ≤
      LWE.decisionAdvantage P χ D + (lweSeeds P χ s s').fail := by
  sorry

end CoinSampler

-- ═══ module TCSlib/Cryptography/CoinSampling/Efficiency.lean ═══════════════════════════════════
-- Turing-machine model (Seyoon, 2026-11-18 update): the proved `Complexity.BinArith` arithmetic and
-- the `PolyTimeComputable` pairing calculus; no word-RAM chain, so no `sorryAx` from it.

open TCSlib.Cryptography.NumberTheory (listToNat)

/-- **Encoding an outcome or a failure**: `[]` for `none` (gave up), `true :: enc a` for `some a`
(the convention of host H15's `rejectBlocksL` contract: rejection is the empty word). -/
def encodeOption {Ω : Type} (enc : Ω → List Bool) : Option Ω → List Bool
  | none => []
  | some a => true :: enc a

/-- `encodeOption enc none = []`. -/
theorem encodeOption_none {Ω : Type} (enc : Ω → List Bool) : encodeOption enc none = [] := rfl

/-- `encodeOption enc (some a) = true :: enc a`. -/
theorem encodeOption_some {Ω : Type} (enc : Ω → List Bool) (a : Ω) :
    encodeOption enc (some a) = true :: enc a := rfl

/-- **A uniform sampler** (the efficiency contract of a sampler, binding uniformity rule): a
family of finite types `Ω y` indexed by the **parameter word** `y` that the machine reads from its
input (for buckets, the numeral of the modulus `N`), an encoding of their elements, for every
coin count `s` a coin sampler of `Ω y` reading exactly `s` coins, and **one** polynomial-time
string map `raw` that, on the NUPPT layout `⟨⟨⟨1^κ, y⟩, α⟩, r⟩`, writes the encoded decoded
outcome of the coins `r`. There is no κ-indexed family of programs and no hard-wired modulus:
`κ` only fixes the number of coins (`toNUPPT`), and the machine built from `raw` has empty
advice. [PS10, Definition 23.4] (a PPT: one machine, uniform coins). -/
structure UniformSampler where
  /-- The finite type sampled at the parameter word `y`. -/
  Ω : List Bool → Type
  /-- Each sampled type is finite. -/
  [fintype : ∀ y, Fintype (Ω y)]
  /-- The encoding of a sampled element at the parameter `y`. -/
  enc : (y : List Bool) → Ω y → List Bool
  /-- The coin sampler of `Ω y` reading `s` coins. -/
  sampler : (y : List Bool) → (s : ℕ) → CoinSampler (Ω y) s
  /-- The string map computed by the machine. -/
  raw : List Bool → List Bool
  /-- On every layout, `raw` writes the encoded outcome of the coins (any advice slot). -/
  raw_layout : ∀ (κ : ℕ) (y α : List Bool) (s : ℕ) (c : Fin s → Bool),
    raw (NUPPT.layout (List.replicate κ true) y α (List.ofFn c)) =
      encodeOption (enc y) ((sampler y s).dec c)
  /-- The string map is polynomial-time (Turing-machine model). -/
  polyTime : PolyTimeComputable raw

attribute [instance] UniformSampler.fintype

namespace UniformSampler

/-- **The sampler's machine** with `coins(κ)` coins: `NUPPT.ofPolyTimeUniform`, a PPT (empty
advice) [PS10, Definition 23.4]. -/
noncomputable def toNUPPT (U : UniformSampler) (coins : PolyExpr) : NUPPT :=
  NUPPT.ofPolyTimeUniform U.polyTime coins

/-- The sampler's machine is uniform (`NUPPT.ofPolyTimeUniform_uniform`). -/
theorem toNUPPT_uniform (U : UniformSampler) (coins : PolyExpr) : (U.toNUPPT coins).Uniform :=
  NUPPT.ofPolyTimeUniform_uniform _ _

/-- The sampler's machine reads `coins(κ)` coins (`NUPPT.coins_ofPolyTimeUniform`). -/
theorem toNUPPT_coins (U : UniformSampler) (coins : PolyExpr) :
    (U.toNUPPT coins).coins = coins := rfl

/-- **The run of the sampler's machine** on the parameter `y` at `κ` with coins `r` writes the
encoded outcome of the coin sampler `sampler y (coins κ)` on `r`
(`NUPPT.runAt_eq`, `runAtL_ofPolyTimeUniform`, `raw_layout`,
`coinsEquiv_ofPolyTimeUniform_ofFn`). -/
theorem toNUPPT_runAt (U : UniformSampler) (coins : PolyExpr) (κ : ℕ) (y : List Bool)
    (r : (U.toNUPPT coins).Coins κ) :
    (U.toNUPPT coins).runAt κ y r =
      encodeOption (U.enc y) ((U.sampler y (coins.eval κ)).dec
        (NUPPT.coinsEquiv_ofPolyTimeUniform U.polyTime coins κ r)) := by
  sorry

/-- **The machine's output law is the coin draw's**: averaging any `g` over the machine's coins
is averaging `g ∘ encodeOption` over `(sampler y (coins κ)).draw`; with `expect_draw` it is the
exact law up to the failure term (`toNUPPT_runAt`, `ProbComp.expect_sample_equiv`). -/
theorem expect_toNUPPT_runAt (U : UniformSampler) (coins : PolyExpr) (κ : ℕ) (y : List Bool)
    (g : List Bool → ℝ) :
    ProbComp.expect (ProbComp.sample ((U.toNUPPT coins).Coins κ))
        (fun r => g ((U.toNUPPT coins).runAt κ y r)) =
      ProbComp.expect (U.sampler y (coins.eval κ)).draw
        (fun o => g (encodeOption (U.enc y) o)) := by
  sorry

end UniformSampler

/-- **The raw bucket decoder** on the layout `⟨⟨⟨1^κ, ⦃N⦄⟩, α⟩, r⟩`: with `N` the number read
from the argument (MSB first, `listToNat`), `s = |r|` and `x` the number read from the coins,
accept iff `x < ⌊2^s/N⌋·N` and write `true` followed by `x mod N` as a numeral of the
argument's width; write `[]` otherwise. The modulus is input, never hard-wired. -/
def bucketRaw (z : List Bool) : List Bool :=
  if listToNat (NUPPT.inCoins z) <
      2 ^ (NUPPT.inCoins z).length / listToNat (NUPPT.inArg z) * listToNat (NUPPT.inArg z) then
    true :: Candidates.natToList (NUPPT.inArg z).length
      (listToNat (NUPPT.inCoins z) % listToNat (NUPPT.inArg z))
  else []

/-- The defining equation of `bucketRaw` (read through `NUPPT.inArg`, `NUPPT.inCoins`). -/
theorem bucketRaw_eq (z : List Bool) :
    bucketRaw z =
      if listToNat (NUPPT.inCoins z) <
          2 ^ (NUPPT.inCoins z).length / listToNat (NUPPT.inArg z) * listToNat (NUPPT.inArg z) then
        true :: Candidates.natToList (NUPPT.inArg z).length
          (listToNat (NUPPT.inCoins z) % listToNat (NUPPT.inArg z))
      else [] := rfl

/-- **The raw decoder computes the bucket sampler**: on the layout with argument `y` and coins
`c`, `bucketRaw` writes `encodeOption` of `(bucket ⟦y⟧ s).dec c`, elements written as numerals of
width `|y|` (`NUPPT.inArg_layout`, `NUPPT.inCoins_layout`, `bitsToNat_eq_listToNat`,
`bucketDec_eq_some_iff`, `bucketDec_eq_none_iff`). -/
theorem bucketRaw_layout (κ : ℕ) (y α : List Bool) (s : ℕ) (c : Fin s → Bool) :
    bucketRaw (NUPPT.layout (List.replicate κ true) y α (List.ofFn c)) =
      encodeOption (fun a : Fin (listToNat y) => Candidates.natToList y.length a)
        ((bucket (listToNat y) s).dec c) := by
  sorry

/-- **The bucket decoder is polynomial-time** in the Turing-machine model, from the proved binary
arithmetic of [AB09, §7.2].

**Proof sketch.** Inputs by the layout projections (`NUPPT.polyTimeComputable_inArg`,
`polyTimeComputable_inCoins`); MSB words to little-endian `Nat.bits` words by
`Encoding.BinaryArith.toLE` (`bitsVal_toLE`, `polyTimeComputable_toLE`); `2^s` as the word
`0^s 1` (`EnsembleLemmas.polyTimeComputable_zeros`, `PolyTimeComputable.append`); the threshold
`2^s − (2^s mod N) = ⌊2^s/N⌋·N` by `Complexity.BinArith.mod` and `sub` (or `div` and `mul`); the
test by `BinArith.lt`; the residue by `BinArith.mod`; back to a width-`|y|` MSB numeral by
`Encoding.BinaryArith.fromLEPoly`; the branch by `polyTimeComputable_ite` and the flag by
`polyTimeComputable_cons`. No host, no loop of our own. -/
theorem polyTimeComputable_bucketRaw : PolyTimeComputable bucketRaw := by
  sorry

/-- **The uniform bucket sampler**: parameter word `y` = the numeral of the modulus,
`Ω y = Fin ⟦y⟧`, elements written at width `|y|`, the bucket sampler at every coin count, and the
raw decoder `bucketRaw`. Its machine `bucketSampler.toNUPPT coins` is one PPT for every modulus
and every `κ`. -/
def bucketSampler : UniformSampler where
  Ω y := Fin (listToNat y)
  enc y a := Candidates.natToList y.length a
  sampler y s := bucket (listToNat y) s
  raw := bucketRaw
  raw_layout κ y α s c := bucketRaw_layout κ y α s c
  polyTime := polyTimeComputable_bucketRaw

/-- `bucketSampler.sampler y s = bucket ⟦y⟧ s`. -/
theorem bucketSampler_sampler (y : List Bool) (s : ℕ) :
    bucketSampler.sampler y s = bucket (listToNat y) s := rfl

/-- `bucketSampler.raw = bucketRaw`. -/
theorem bucketSampler_raw : bucketSampler.raw = bucketRaw := rfl

end TCSlib.Cryptography.CoinSampling
