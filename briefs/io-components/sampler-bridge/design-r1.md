# Sampler bridge, design r1: exact non-dyadic laws from fair coins, with perfect correctness kept

**Status.** Design note for review by Seyoon (records branch `cryptography/pass-shelat-ch2-4`,
written on top of `cb1b0b8a`). Static reading only: no Lean was run. The proposed declarations,
with full statements and `sorry` proofs, are in `Skeleton.lean` (this folder; a draft, not a
checked file). Everything marked *proposed* is open; §0 is binding.

| Pin | Value |
|---|---|
| Rulings | `IOComponentsPlan.md` § *Deferred library work* and decision-log rows of 2026-11-18 (records `343923ef`, `cb1b0b8a`); coordinator relay of 2026-11-18 (TM model, uniformity), §0 |
| Subexponential API | branch `foundations/subexp`, head `cbce64d1`, draft PR #374 (`SubexpSmall`, `SubexpHard`) |
| Consumers read | sPRG pack (`briefs/io-components/sprg/design-r1.md` §0 S2, §4.3, §4.8), PHFE pack (`…/phfe/design-r1.md` §0.3) |

## 0. Rulings in force (binding)

- **R1 Build it in-house, in parallel, as soon as possible** (Seyoon, 2026-11-18). The sPRG and
  PHFE jobs state their samplers as exact laws and prove efficiency only for the deterministic
  algorithms; the bridge closes that gap. Reusable across campaigns.
- **R2 The sketch** (Seyoon): draw `x` uniform in `[0, M)`, `M = 2^k ≫ N`; map the first `q·N`
  values (`q = ⌊M/N⌋`) onto the domain in equal buckets, so the output is exactly uniform given
  success; on the leftover the algorithm gives up by a fallback that keeps correctness exact
  (e.g. sends in the clear); failure `< N/M`, so security moves by at most that. Rational laws
  by weighted buckets.
- **R3 Efficiency in the Turing-machine model now** (Seyoon, relayed 2026-11-18, superseding the
  word-RAM route for the bridge): the existing tooling `Complexity.PolyTimeComputable`,
  `NUPPT.ofPolyTimeUniform` / `exists_uniform_computes`, and `Complexity/ClassP/BinaryArith`
  (`add`, `sub`, `mul`, `div`, `mod`, `lt`, `le`, `powMod`, all proved). Aim: a fully
  `sorry`-free bridge.
- **R4 Uniformity is binding.** Samplers are honest algorithms, so their efficiency is uniform:
  `PolyTimeComputable` of the coins → output map **with the modulus read from the input**, or
  `∃ A, A.Uniform ∧ A.Computes f` for deterministic parts. Never a bare `∃ A : NUPPT, A.Computes
  f` (advice makes it hold for uncomputable `f`, `PPT.lean` docstring at `Computes`); no κ-indexed
  family of programs; no hard-wired `p(κ)`. (Deterministic generation of a κ-bit prime in
  poly(κ) time is not known; `BinaryArith/PrimeFind` only finds `O(log n)`-bit primes from a
  unary input.)
- **R5** The library's subexponential notion is the Foundations API (`SubexpSmall`); no new one.
- **R6** Duplication rule: an undisclosed re-proof of a public TCSlib or Mathlib lemma, inline
  re-derivations included, is a major (`policy.md` §1 *Duplication*).

## 1. The problem

The library states every non-dyadic law exactly: `Games.ProbComp.sample Ω` for a finite `Ω`
(uniform `ℤ_p`, `{x : G // x ≠ 1}`, `G_T`, the LPN seed `Fin W × ℤ_p`, uniform functions
`Fin m → Fin B`) and its pushforwards, or a seed function on a finite seed type (`LWE.Noise`,
`Regev.keygen`). `ProbComp`'s oracle answers a uniform element of `Fin (m+1)` for *any* `m`, so a
`ProbComp` game is not a fair-coin object. Machines have fair coins only. Three things must be
connected, for any game and any scheme:

1. **Law**: a fair-coin implementation of each exact draw whose effect on every game is bounded by
   an explicit failure term, summed over the draws.
2. **Correctness**: every *every-outcome* property of the exact scheme (perfect correctness
   `IBEScheme.Correct`, the FE `Correct`, the reachable-encoding injectivity fields `encPP_inj` …,
   the sPRG `HasComplexity`, Regev/GSW every-seed correctness) holds **exactly** for the coin
   implementation, not up to the failure term.
3. **Efficiency**: one uniform polynomial-time machine per sampler, parameters (the modulus) on
   its input, composable into the honest algorithms' machines.

Plus the asymptotics: the summed failure term is `Negligible` and, with enough slack bits,
`SubexpSmall`, so it fits the explicit-slack theorems of the sPRG and PHFE jobs (sPRG S8).

## 2. What exists, and how far it goes

| Piece (file:line) | What it gives | What it does not give |
|---|---|---|
| `StatClose X Y δ` (`Asymptotic/Sampling.lean:126`) with `.map` :203, `.prod` :291, `.trans` :196, `.mono` :165, `.of_uprob_ne` :176, `.abs_uprob_sub_le_prod` :266, `distAdv_le_of_statClose` :278, `uexp_le_of_statClose` :313 | closeness of **seed-function** samplers, and its transfer to `uprob`/`distAdv` experiments with auxiliary coins | no `ProbComp` form: games are computations with `bind` and oracles, not seed functions |
| `statClose_getD_of_uniform_of_some` (`Sampling.lean:913`) | **the abstract statistical part**: a sampler `Ω → Option γ` uniform on success with `Pr[none] ≤ f`, made total by a default, is `f`-close to uniform | only the `getD` (default) form; the `Option` form (fallback *branch*) is not derivable from it (`getD` forgets `none`) |
| `uniformFromBits` :487, `uprob_uniformFromBits_eq_some` :515, `uprob_uniformFromBits_none` :529; `rejectionSample` :732, `rejectionSample_uniform_of_some` :769, `uprob_rejectionSample_none` :797, `statClose_rejectionSample` :862 | one rejection trial, and `T` trials, uniform on success, exact failure `(1 − m/2^k)^T` | `T`-trial samplers with `k = size m`: `T·size(m)` coins for failure `2^{-T}`; no single-draw low-failure sampler |
| `pushesUniform_of_card_fiber` :350, `uprob_comp_eq_sum_fiber` :536, `bitsToNat` :393, `bitsEquiv` :451 | equal fibres push uniform to uniform; fibre decomposition | — (reused) |
| `Candidates.rejectBlocksL` (`Candidates/Concrete.lean:545`), `statClose_rejectBlocksL` :878, host H15 `polyTimeComputable_rejectBlocksL` :814; `Candidates.sampleBelowL` (`Candidates/DiscreteLog.lean:578`), `statClose_sampleBelowL` :618, `expSampler` (with the assumed bundle `ArithmeticFP`) | list-coin block rejection with its closeness and its poly-time host; the DL domain sampler | its uniformity on success is not published (only closeness, via private block lemmas); `n·n` coins; `expSampler`'s efficiency is relative to `ArithmeticFP` |
| `BB1Machine.blockLen` (`…/BonehBoyenMachine/Draws.lean:131`), `draw` :142, `order_le_two_pow` :156, `statClose_draw` :168, `abs_expect_draws_sub_le` :448 | for BB1's reduction: an exponent of `ℤ_p` from `n·n` coins, `n = κ + wG + 1`, fallback `0`, `(1/2)^n`-close; `cap` draws vs ideal on a `{0,1}`-valued test | BB1-specific (group, width); `{0,1}`-valued tests in seed form; `(κ + wG)²` coins per exponent (κ = 128, wG = 256: 148,225 coins vs 384 for a bucket with failure `≤ 2^{-128}`) |
| `OneWay.statClose_pi` (`Asymptotic/OneWayLemmas.lean:276`) | `N` independent close draws are `N·δ`-close | — (reused for coordinatewise defaults). Note: two more copies exist, `GIZK.statClose_pi` (`ZeroKnowledge/GraphIsomorphismZK/Closeness.lean:165`) and `GI.statClose_pi` (`…/GraphIsomorphism/SoundnessRep.lean:279`); Stage 2 seals them (S2-SL-427/457) but does not merge them |
| `permFromCoins_uniform_of_some` (`Asymptotic/Permutations.lean:353`), `samplePrime_uniform_of_some` (`NumberTheory/Primality.lean:573`), `firstHit_uniform_of_some` (`Sampling.lean:605`) | more samplers already proved exact on success | — (each is an instance of the proposed contract) |
| `statClose_iff_epsClose_map` (`Asymptotic/SamplingFinDist.lean:62`); `FinDist` (`InformationTheory/FinDist.lean:52`), `.map` :105, `.uniform` :92; `EpsClose` (`InformationTheory/Extractors.lean:62`), `abs_probTrue_sub_le_statDist` :75; `statDist` (`StatisticalDistance.lean:47`) | seed closeness = closeness of laws; statistical distance | no closeness of `ProbComp` computations |
| `ProbComp.sample` (`Games/Probability.lean:93`), `expect` :107, `prob` :113, `expect_bind` :128, `dist` :280, `abs_expect_sub_le` :393; `accept`/`advantage` (`Games/Advantage.lean:63/72`), `advantage_triangle` :103; `Bridge.prob_sample_eq_uprob` (`Games/Bridges/Experiments.lean:66`), `Bridge.expect_sample_eq_uexp` :74 | exact semantics of games; the bridge `sample` ↔ `uprob`/`uexp` | no statistical hop for computations |
| `identical_until_bad` (`Games/Hopping.lean:306`), `expect_simulate_congr` :384, `prob_bad_le` :403; `expect_simulate_rel` (`Games/Relational.lean:85`); `freshImpl`/`expect_simulate_tapeImpl` (`Games/Tapes.lean:125/209`) | exact-law simulation congruence; bad-event hops; coins in advance | identical-until-bad needs equal sub-laws on good successors, but a coin draw puts mass `1 − fail` there and the exact draw mass `1`: it needs a coupled intermediate game; no `ε`-congruence for simulation. `Tapes` is avoided (Stage 2 S2-DL-10 restates `extTape`) |
| `OracleComp.AllOutputs` (`Games/OracleComp.lean:292`), `AllOutputs.bind` :324, `allOutputs_true` :309 | the correctness form of `IBEScheme.Correct` and the FE/sPRG predicates | no converse of `AllOutputs.bind`, no `(sample T).AllOutputs P ↔ ∀ t, P t`, no output-inclusion relation |
| `LWE.Noise` (`LWE/Noise.lean:41`), `bitNoise` (`LWE/BitNoise.lean:40`), `LWE.sample` (`LWE/Basic.lean:101`), `LWE.Family` (`LWE/Assumption.lean:65`), `LWE.sampleFromBits` / `_law` (`LWE/Sampling.lean:48/68`), `Encoding.DyadicUniform.bitsToResidue_bijective` :60 | exact laws; exact fair-bit LWE **only for `q = 2^width`**; `Family` asks for samplers as separate contracts ("non-dyadic laws require a separate implemented sampler or approximation transfer") | nothing for odd or prime `q`, or for non-dyadic noise seeds |
| `Negligible` (`Foundations/Negligible.lean:57`), `negligible_two_pow_neg` :153, `Negligible.polyExpr_mul` (`Asymptotic/ReductionSupport.lean:267`); `SubexpSmall` (subexp branch :71), `.mul_pow` :204, `.const_mul` :190, `subexpSmall_two_pow_neg` :258 | the asymptotic closure needed | — (reused) |
| `NUPPT.ofPolyTimeUniform` (`Complexity/Randomized/PPT.lean:406`), `_uniform`, `coinsEquiv_ofPolyTimeUniform`, `runAtL_ofPolyTimeUniform` :437, `exists_uniform_computes` :448; `NUPPT.layout`, `inArg`, `inCoins` (`Randomized/Closure.lean:111–123`); `BinArith.add/sub/lt/le` (`ClassP/BinaryArith/AddSub.lean:141–239`), `mul` (`Mul.lean:110/217`), `div`/`mod` (`Div.lean:52/55`, proofs :230/:245), `powMod` (`ModPow.lean:52/214`); `Encoding.BinaryArith.toLE`/`fromLEPoly` (MSB ↔ LE adapters, proved) | everything an efficient bucket decoder needs, in the TM model | no sampler is built on them yet |

**Answer to "does `statClose_draw` already give the statistical part?"** For BB1's reduction,
yes: `statClose_draw` + `OneWay.statClose_pi` + `abs_expect_draws_sub_le` is the statistical
transfer for one specific sampler with a default fallback and `{0,1}`-valued tests; and
`statClose_getD_of_uniform_of_some` is the same fact in abstract form. What is missing:

- **(M1)** a single-draw sampler with failure `< N/2^s` (R2), quadratically cheaper in coins than
  the `T`-trial ones, and one contract shared by all samplers exact on success;
- **(M2)** the `Option` form of the statistical fact (fallback branches, not only defaults), as an
  *exact mixture identity* from which both forms follow;
- **(M3)** an experiment-level transfer for `ProbComp` games: closeness of computations, closed
  under `bind` and oracle simulation, so that draws anywhere in a game (honest algorithms,
  per-query oracle draws) sum their failure terms;
- **(M4)** the correctness transfer: output inclusion, under which every `AllOutputs` property
  carries over *exactly*;
- **(M5)** the asymptotic packaging (`Negligible`, `SubexpSmall`) of `q(κ)·2^{-t(κ)}`;
- **(M6)** a uniform efficient decoder with the modulus as input, `sorry`-free in the TM model;
- **(M7)** non-dyadic LWE seeds from fair coins (`LWE.Family`'s missing contract).

## 3. Consumers and what each gains

| Consumer | How it samples today | Gain from the bridge |
|---|---|---|
| **sPRG** (job `io-sprg`, JLS26 §4) | `idSamp'`, `sdSamp'` are `ProbComp`s drawing `sample (Fin m → Fin B)`, `sample (Fin κ → (Fin ℓ → ZMod p) × (Fin n → Fin W × ZMod p))`, `Matrix … (ZMod p)`; reductions hardwire `ω*` and never sample (sPRG design §4.8) | honest samplers from fair coins: `HasComplexity` (an `AllOutputs` predicate on `sdSamp`) transfers **exactly** by output inclusion; security moves by `drawSlack`, `SubexpSmall c` for all `c < 1`, absorbed by the subexponential corollary; the LPN seed `Fin W × ZMod p` is one bucket of `W·p` |
| **PHFE** (job `io-phfe`, Wee20) | Setup/Enc draw `ZMod p`, `{x : G // x ≠ 1}`, `G_T`; reductions use `BB1Machine.draw` | honest algorithms from coins with `FEScheme.Correct` kept; reductions may use `zmod p (size p + κ)` (`size p + κ` coins vs `(κ + wG)²`); `{x // x ≠ 1}` via `ofEquiv` with a generator-based enumeration (consumer side) |
| **BB1 / IBE** (`IdentityBased/BonehBoyen.lean`) | `setup`/`keyGen`/`encrypt` draw `ZMod p`, `{x // x ≠ 1}`, `G` exactly; `bb1_correct` is `AllOutputs` | a coin-implemented BB1 is correct by `OutputsSubset` without re-running `bb1_correct`'s proof; the `encPP_inj`/`encSK_inj`/`encCT_inj` fields transfer the same way; IND-sID-CPA moves by `(draws)·2^{-t}` (`close_simulate_draw` for `KeyGen` queries). `BB1Machine.draw` stays (no retrofit, Q9) |
| **Pairing assumptions** (`Pairing/Assumptions.lean`) | exact `dbdhGame`/`bdhGame` | none needed: assumptions stay exact laws; only honest algorithms and reductions sample |
| **Regev PKE/SKE, GSW** (`Encryption/*/Regev`, `Homomorphic/GSW`) | seed functions: `keygen` on (matrix, secret over `ZMod q`, `χ.Coins` seeds); every-seed correctness (`decrypt_keygen_encrypt`); `uprob`/`distAdv` experiments | keygen for **any** `q ≥ 2` (prime or odd, not only `2^width`) from fair coins: correctness by `forall_comp_getD` (default seed), security by `statClose_lweSample_coins` / `distAdv_lweSample_coins_le`; encryption coins are already bits |
| **LWE** (`LWE/Assumption.lean`) | `Family` asserts no sampler; `sampleFromBits` exact only for dyadic `q` | the missing contract: `lweSeeds`, `fail_lweSeeds_le`, the challenge transfer; non-dyadic `Noise` seeds via `noiseSeeds` |

**Consumer-side consequence of R4.** The sPRG and PHFE packs fix a prime schedule `p(κ)` (Q-S2).
Under R4 an honest machine may not compute or hard-wire `p(κ)`: the modulus must reach every
sampler through its input. For PHFE it arrives with the group description from the generator; for
the sPRG it must be an input of `IdSamp′`/`SdSamp′`'s machines (e.g. part of the index or of public
parameters). Q10 asks how.

## 4. Proposed formulation (recommended)

Eight modules (`Skeleton.lean` has every declaration). Namespaces: `TCSlib.Cryptography.CoinSampling`
(new area) and `TCSlib.Cryptography.Games` (two generic relations, Q7).

### 4.1 Per sampler: `CoinSampler Ω s` (`CoinSampling/Basic.lean`)

```lean
structure CoinSampler (Ω : Type) [Fintype Ω] (s : ℕ) where
  dec : (Fin s → Bool) → Option Ω                       -- none = give up
  uniform_of_some : ∀ a a' : Ω, uprob (dec · = some a) = uprob (dec · = some a')
noncomputable def CoinSampler.fail (S) : ℝ := uprob (S.dec · = none)   -- derived, not a field
```

- The contract is exactly the hypothesis `huni` of `statClose_getD_of_uniform_of_some` and the
  shape of the four existing `*_uniform_of_some` lemmas: the bridge adds no new notion of a
  sampler, it names the one the library already proves.
- The coin count is a type index, so a sampler meets machine coins `Fin (coins.eval κ) → Bool`
  without casts. Laws are uniform on `Ω`; other exact laws are pushforwards of a uniform seed
  (the library's convention: `LWE.Noise`, the sPRG's `lpnNoise`), so uniform targets suffice
  (option (i-b) in §5).
- Derived facts: `uprob_dec_eq_some` (conditional law `(1 − fail)/|Ω|`), **the mixture identity**
  `uexp_comp_dec` (`𝔼_c F(dec c) = fail·F(none) + (1 − fail)·𝔼_a F(some a)`, the whole statistical
  content), `statClose_some` (M2), `statClose_getD` (= the existing lemma, applied, not re-proved).
- Combinators: `congr` (along `Ω ≃ Ω'`), `reindex` (coin bijection), `pi n` and `prod` (independent
  draws, `fail_pi_le : fail ≤ n·fail`, `fail_prod_le`, union bounds by `uprob_exists_le`,
  `uprob_or_le`), `ofRejection` (the existing `rejectionSample` as an instance).
- Seed-form correctness: `forall_comp_getD`, `forall_comp_elim` (for seed-function schemes).

### 4.2 Buckets and rational laws (`CoinSampling/Buckets.lean`)

`bucketDec N s c := (uniformFromBits (⌊2^s/N⌋·N) s c).map (fun x => (finProdFinEquiv.symm x).2)`:
Seyoon's sketch as **one existing rejection trial at threshold `q·N` followed by `x mod N`**.
Exactness from `uprob_uniformFromBits_eq_some` and the fibre count `q` (Mathlib's
`finProdFinEquiv`, or `Nat.count_modEq_card`); `fail_bucket : fail = (2^s mod N)/2^s` (exact),
`fail_bucket_lt : < N/2^s` (the sketch), `fail_bucket_le : 0 < N ≤ 2^b → fail(bucket N (b+t)) ≤ 2^{-t}`.
`x mod N` (residue classes as buckets) rather than `⌊x/q⌋` (contiguous buckets): the law is the
same; `mod` needs only `N`, while `⌊x/q⌋` needs `q` too (Q4).

Weighted buckets (v): `RatSeed w := Σ a, Fin (w a)`; `uprob_ratSeed_fst` gives the law
`w a / Σ w`; `weighted w s := ofEquiv finSigmaFinEquiv s` (Mathlib's cumulative enumeration).
Examples: `𝒟_{1/W}(p)` is the pushforward of `Fin W × ZMod p` (one bucket of `W·p`, split by
`finProdFinEquiv`); `Bernoulli(ℓ^{-δ})` must first be rounded to a rational rate (the sPRG's
convention C6 does so: rate `1/W`); irrational rates are out of scope for an exact bridge.

### 4.3 Per experiment: `ProbComp.Close` (`Games/Closeness.lean`)

```lean
def ProbComp.Close (ε : ℝ) (c₁ c₂ : ProbComp α) : Prop :=
  ∀ g : α → ℝ, (∀ a, 0 ≤ g a ∧ g a ≤ 1) → |expect c₁ g - expect c₂ g| ≤ ε
```

`[0,1]`-valued tests (not events) make it closed under `bind` (`Close.bind_left/_right/bind`),
with `refl/symm/mono/trans/map`, `abs_prob_sub_le`, `abs_accept_sub_le`, `advantage_le_of_close`,
and **`Close.simulate`**: per-call `ε`-closeness gives `m·ε` for `m` queries (`ε = 0` is
`expect_simulate_congr`). Interop (optional in the first PR): `close_iff_epsClose_dist` (finite
outputs) ties it to `EpsClose`, which `statClose_iff_epsClose_map` ties to `StatClose`; it needs two
small new readers (`expect` as a sum over `dist`; `|Σ (p−q)·g| ≤ statDist` for `g ∈ [0,1]`).

Transfer (`CoinSampling/Transfer.lean`): `draw S := S.dec <$> sample (Fin s → Bool)`,
`drawD S d` (default fallback), `expect_draw` (the mixture identity for games), and the atoms

- `close_draw_bind : Close S.fail (S.draw >>= K) (sample Ω >>= K ∘ some)` (any fallback `K none`),
- `close_drawD_bind : Close S.fail (S.drawD d >>= k) (sample Ω >>= k)`,
- `close_simulate_draw`: a fresh coin draw per oracle query, `m` queries, `m · fail`.

So **(ii)**: replacing exact draws by coin draws anywhere in a game changes its acceptance
probability by at most the summed failure probabilities (chain by `Close.bind`, oracles by
`Close.simulate`, finish with `abs_accept_sub_le` or `advantage_le_of_close`).

### 4.4 Correctness: output inclusion (`Games/Closeness.lean`, `Transfer.lean`)

```lean
def OracleComp.OutputsSubset (c₁ c₂ : OracleComp spec α) : Prop :=
  ∀ P, c₂.AllOutputs P → c₁.AllOutputs P
```

with `allOutputs_bind_iff` (new converse of `AllOutputs.bind`), `refl/trans/bind/simulate`,
`allOutputs_sample_iff : (sample T).AllOutputs P ↔ ∀ t, P t`, and the atom
`outputsSubset_drawD : OutputsSubset (S.drawD d) (sample Ω)`. **(iii)**: a scheme whose exact draws
are replaced by default-fallback coin draws has possible outputs among the exact scheme's, so
**every** `AllOutputs` property transfers without re-proof. The fallback "correct by construction"
(Seyoon's "send in the clear", which changes the output format) is `allOutputs_draw_bind` (both
branches satisfy `P`). A default `d ∈ Ω` is always a legitimate exact outcome under the
pushforward-of-uniform convention, so the default is the standard fallback; the branch form is for
defaults that are not efficiently computable (Q2).

### 4.5 Composition and asymptotics (iv) (`CoinSampling/Asymptotic.lean`)

Per draw: `bucket N (b + t)` with `0 < N ≤ 2^b` fails with probability `≤ 2^{-t}`. A game with at
most `q(κ)` draws (straight-line or per query) is `drawSlack q t κ = q(κ)·2^{-t(κ)}`-close to the
exact game. With `t(κ) ≥ κ` (recommended default: `s = b + κ` coins per draw):
`negligible_drawSlack` (`negligible_two_pow_neg`, `Negligible.mono`, `Negligible.polyExpr_mul`) and
`subexpSmall_drawSlack` for every `0 < c < 1` (`subexpSmall_two_pow_neg`, `SubexpSmall.mono`,
`.mul_pow`, `.const_mul`). For `SubexpSmall 1` exactly, take `t = κ + size q` (Q5). The sPRG's
subexponential corollary (an exponent below 1 anyway) absorbs the term with `SubexpSmall.add` after
`mono_exponent`. Only this module imports `Foundations.Subexponential` (PR #374), so the rest can
land first.

### 4.6 Efficiency (vi): `UniformSampler` (`CoinSampling/Efficiency.lean`), TM model (R3), uniform (R4)

```lean
structure UniformSampler where
  Ω : List Bool → Type; [fintype : ∀ y, Fintype (Ω y)]
  enc : (y : List Bool) → Ω y → List Bool
  sampler : (y : List Bool) → (s : ℕ) → CoinSampler (Ω y) s
  raw : List Bool → List Bool
  raw_layout : ∀ κ y α s (c : Fin s → Bool),
    raw (NUPPT.layout (List.replicate κ true) y α (List.ofFn c)) = encodeOption (enc y) ((sampler y s).dec c)
  polyTime : PolyTimeComputable raw
```

- **One** string map for every κ, every parameter word `y` (the modulus' numeral) and every coin
  count; κ only fixes the coin count through `toNUPPT coins := NUPPT.ofPolyTimeUniform polyTime
  coins`, which is uniform (`toNUPPT_uniform`). No κ-indexed programs, no advice, no hard-wired
  modulus. `toNUPPT_runAt` and `expect_toNUPPT_runAt` connect the machine's output law to
  `(sampler y (coins κ)).draw`, hence (with §4.3) to the exact law.
- `Computes` is the deterministic form (output independent of coins) and does not fit samplers;
  the sampler form is `PolyTimeComputable raw` on the layout with coins, as R4 allows.
- The instance `bucketSampler`: `bucketRaw` reads `N` from `NUPPT.inArg`, `x` and `s` from
  `NUPPT.inCoins`, tests `x < 2^s − (2^s mod N)` and writes `true :: ⦃x mod N⦄_{|y|}` or `[]` (H15's
  rejection convention). `polyTimeComputable_bucketRaw` is assembled from proved pieces only:
  layout projections, `toLE`/`fromLEPoly`, `0^s1` for `2^s` (`polyTimeComputable_zeros`,
  `PolyTimeComputable.append`), `BinArith.mod`, `sub`, `lt`, `polyTimeComputable_ite`. No host and
  no loop of our own.
- **Consumers** compose: an honest algorithm's raw map calls `bucketRaw` (or its own
  `UniformSampler.raw`) on a sub-layout carrying its modulus, branches on the flag (fallback:
  write the default seed's encoding), and feeds the deterministic core; vectors of draws decode
  coin blocks with `Complexity.BinArith.mapW` (proved map host, `ClassP/BinaryArith/Words.lean:221`).
  The machine-level run lemma then reads "output = encoding of `alg ((dec block).getD d)`", and
  `close_drawD_bind`/`outputsSubset_drawD` finish security and correctness.
- Word RAM (`Programs/WordRAM`, `coin`): not used now (R3). If wanted later, a program with the same
  `raw` semantics plugs in through Seyoon's RAM ⇒ `PolyTimeComputable` bridge (names unknown;
  its BPP mode takes the coins as a second input, machine-library-design §15c), replacing only
  `polyTimeComputable_bucketRaw`'s proof.
- Axiom check at the gate: the TM tooling's import closure contains 17 `sorry`s in 7 modules
  (`ClassP/TimeConstructible` 2, `TuringMachine/Build/Loop` 5, `/Build/Primitives` 3,
  `/Build/Wrappers` 2, `/Composition` 3, `/Encoding` 1, `/Simulation` 1); whether
  `polyTimeComputable_mod` and friends reach them is a `#print axioms` question, not settled
  statically. "Sorry-free" is to be certified by that check.

### 4.7 Instances (`CoinSampling/Instances.lean`)

`zmod q s` (bucket through `ZMod.finEquiv`), `fail_zmod_le`; `noiseSeeds χ s` (laws only; an
efficient noise sampler supplies a computable enumeration); `LWESeed`, `lweSeeds` (`m·n + n`
residues, `m` seeds), `fail_lweSeeds_le`, `statClose_lweSample_coins`,
`distAdv_lweSample_coins_le` (the `LWE.Family` contract, M7). Consumer-specific samplers (the LPN
seed, `{x : G // x ≠ 1}`) stay in their consumers.

## 5. Options considered

**Per sampler** — (i-a, recommended) uniform target + pushforwards, contract `uniform_of_some`;
(i-b) target `μ : FinDist α` with `Pr[dec = some a] = (1 − fail)·μ a`: covers rational laws
directly, but games cannot `sample` a `FinDist` (they sample types), so it adds a second law
language; (i-c) failure bound as a structure field (`failBound`, `fail_le`) instead of the derived
`fail`: convenient, but the exact `fail` is computable for buckets and composes by union bounds.

**Per experiment** — (A, recommended) `ProbComp.Close` with congruences (§4.3); (B) three fixed
lemmas without a relation: one draw (`|𝔼 − 𝔼| ≤ fail` via `expect_draw`), a vector of draws
(`OneWay.statClose_pi` + a `[0,1]`-function form of `StatClose`), a fresh draw per query (via
`Games.Tapes`' coins in advance, which Stage 2 restates): smaller, but every multi-algorithm game
repeats the hybrid by hand; (C) a generic compiler `ProbComp.viaCoins t c` replacing *every* uniform
query `sampleFin m` of a computation by a `size(m+1)+t`-coin bucket draw with default `0`, with two
theorems: `Close (q·2^{-t}) (c.viaCoins t) c` for `q` queries and `OutputsSubset (c.viaCoins t) c`.
Elegant (one statement per game), and dyadic queries cost 0, but a game built from coin algorithms is
not syntactically `G.viaCoins`, so (A)'s congruences are needed anyway; (C) is a later convenience.

**Fallback** — (a, recommended) default value `getD d`: exact correctness by output inclusion, no
format change; (b) `Option` continuation at every call site; (c) sum-typed outputs
(`Out ⊕ Clear`, "send in the clear") as the standard. (b) and (c) are available through
`close_draw_bind` and `allOutputs_draw_bind`.

**Decoder's give-up** — (1, recommended) `Option Ω`; (2) a sum `Ω ⊕ Fail` (no information to carry);
(3) total decoder plus a separate `ok` flag (two maps to keep consistent).

## 6. Duplication sweep (R6)

**Reused, not re-proved:** `statClose_getD_of_uniform_of_some` (applied as `statClose_getD`),
`uniformFromBits` + `uprob_uniformFromBits_eq_some/_none` (inside the bucket),
`rejectionSample_uniform_of_some`, `uprob_rejectionSample_none` (`ofRejection`),
`uprob_comp_eq_sum_fiber`, `uprob_exists_le`, `uprob_or_le`, `uprob_comp_equiv`,
`StatClose.map/.trans/.abs_uprob_sub_le_prod`, `OneWay.statClose_pi`, `distAdv_def`,
`Bridge.expect_sample_eq_uexp`, `expect_bind`, `expect_map`, `abs_expect_sub_le`,
`AllOutputs.bind`, `allOutputs_true`, `expect_simulate_congr` (the `ε = 0` case),
`negligible_two_pow_neg`, `Negligible.polyExpr_mul`, `SubexpSmall.*`, `NUPPT.ofPolyTimeUniform`
and readers, `BinArith.*`, `Encoding.BinaryArith.toLE/fromLEPoly`, `polyTimeComputable_zeros`,
Mathlib's `finProdFinEquiv`, `finSigmaFinEquiv`, `ZMod.finEquiv`, `Nat.count_modEq_card`,
`Fintype.sum_option`.

**New, with why nothing covers it:** the contract `CoinSampler` (names the existing `huni` shape);
`bucketDec`/`bucket` (no single-trial reduce-mod sampler exists); the mixture identity
`uexp_comp_dec` and `statClose_some` (see the disclosed overlap below); `ProbComp.Close` and its
congruences (no closeness of computations exists; `EpsClose` needs finite outputs and no `bind`,
`StatClose` needs seed functions); `OutputsSubset`, `allOutputs_bind_iff`, `allOutputs_sample_iff`
(searched `Games/` on every branch: none); `drawSlack` lemmas; `UniformSampler`, `bucketRaw`;
`lweSeeds`.

**Disclosed overlap (must be ruled, Q8):** the mixture identity's proof is the fibre decomposition
`hdec` inside `statClose_getD_of_uniform_of_some`'s proof. Proposed: prove `uexp_comp_dec` once in
`Asymptotic/Sampling.lean` beside that lemma (no Stage 2 row touches the file) and re-derive
`statClose_getD_of_uniform_of_some` from it (a proof-level change of an existing theorem); or prove
it in the new area and record the overlap in the dedup queue.

**Noticed, not ours:** three `statClose_pi` copies (§2); BB1's `draw` is an instance of the
contract once `rejectBlocksL`'s uniformity on success is published (backlog row, Q9).

## 7. Layout, imports, size

| Module | Content | Lines (est.) |
|---|---|---|
| `TCSlib/Cryptography/CoinSampling.lean` | facade (`## Contents`), one line in `TCSlib.lean` | 40 |
| `CoinSampling/Basic.lean` | contract, `fail`, conditional law, mixture identity, `StatClose` forms, `congr`/`reindex`/`pi`/`prod`, `ofRejection`, seed-form correctness | 350–500 |
| `CoinSampling/Buckets.lean` | `bucketDec`, `bucket`, exact failure and bounds, `ofEquiv`, `RatSeed`, `weighted` | 250–400 |
| `Games/Closeness.lean` | `ProbComp.Close` + congruences + `simulate` + advantage; `OutputsSubset` + `allOutputs_bind_iff`; interop reader | 350–550 |
| `CoinSampling/Transfer.lean` | `draw`, `drawD`, `expect_draw`, the closeness and correctness atoms, per-query form | 200–350 |
| `CoinSampling/Asymptotic.lean` | `drawSlack`, negligible / subexponential, schedule bound | 80–150 |
| `CoinSampling/Instances.lean` | `zmod`, `noiseSeeds`, `lweSeeds`, LWE transfer | 200–350 |
| `CoinSampling/Efficiency.lean` | `encodeOption`, `UniformSampler` + machine readers, `bucketRaw`, its poly-time proof, `bucketSampler` | 350–650 |
| **Total** | 8 new files, 2 facade lines (`TCSlib.lean`, `Games.lean`) | **≈ 1,800–3,000 (central 2,300)** |

`Skeleton.lean`: 936 lines, 114 declarations (64 `sorry`s). Stage 2 crossings of the imports:
`Complexity/Randomized/PPT.lean` S2-BO-031 (proof-level), `Games/Probability.lean` S2-DL-16
(additive), `Asymptotic/SamplingFinDist.lean` S2-SL-214–216 (seal, proof-level); none on
`Asymptotic/Sampling`, `Games/Hopping`, `Bridges/Experiments`, `LWE/*`, `BinaryArith`. All
additive or proof-level. `Games/Tapes` and `Asymptotic.OneWay` are not imported.

Delivery suggestion: one owner PR (statements gate, then proofs), or two: `Games/Closeness` +
`Basic` + `Buckets` + `Transfer` first (the sPRG/PHFE jobs can state against them), then
`Asymptotic` (after #374), `Instances`, `Efficiency`.

## 8. Risks

- `Close.simulate` needs the query budget induction of `prob_bad_le`; the per-query form needs the
  draw inside each call (oracles that draw zero or two values: `prod` or ignore the coins).
- The bucket's endianness: `uniformFromBits` reads MSB first (`bitsToNat`), `BinArith` is LE;
  `bitsToNat_eq_listToNat` and `toLE` bridge it, but `bucketRaw_layout` is the fiddliest proof.
- `pi`'s `dec` uses `Option.get` under a decidable `∀`; if awkward, use `Option` traversal
  (`List.ofFn` + `Option.allSome`-style) with an `_iff` reader; statements unchanged.
- The axiom certificate of the TM tooling (§4.6, last bullet).
- [Lem19] as the source of the bucket method is a candidate citation, not yet verified or ingested.

## 9. Open questions for Seyoon (recommended option first; ★ = shapes the API)

**★Q1. What is per sampler, what per experiment?**
(A) Per sampler: the decoder contract `CoinSampler` (exact on success, derived `fail`) and its
uniform machine `UniformSampler`; per experiment: one closeness relation `ProbComp.Close` with
`bind`/`simulate` congruences, the sum of failures arising from the chain. (B) Per sampler as in (A);
per experiment three fixed lemmas (one draw, a vector, a fresh draw per query), no relation.
(C) (A) plus the generic compiler `ProbComp.viaCoins` now.

**★Q2. How are fallbacks specified?**
(A) A default value `d ∈ Ω` (`drawD`, `getD`) as the standard: exact correctness by output
inclusion, no change of formats; the branch form `draw >>= K` stays available for custom fallbacks.
(B) An explicit fallback branch at every call site. (C) "Send in the clear" (sum-typed outputs) as
the standard.

**★Q3. What is the decoder's "give up"?**
(A) `Option Ω`. (B) A sum type `Ω ⊕ Fail`. (C) A total decoder with a default plus a separate
success flag.

**Q4. The bucket map.**
(A) `x mod N` below `2^s − (2^s mod N)` (needs only `N`; `BinArith.mod`). (B) `⌊x/q⌋` below `q·N`
(contiguous buckets as in your sketch; needs `q = ⌊2^s/N⌋`). (C) Lemire's multiply-shift
(division-free per draw). The law is identical in all three.

**Q5. Slack bits per draw.**
(A) `s = b + t` with `t` a `PolyExpr` chosen by the consumer, default `t = κ`: per draw `≤ 2^{-κ}`,
total `q(κ)·2^{-κ}`, negligible and `SubexpSmall c` for every `c < 1`. (B) `t = κ + size q`, total
`≤ 2^{-κ}` (`SubexpSmall 1`). (C) a fixed `t = κ`, no parameter.

**★Q6. Target law of the contract.**
(A) Uniform on a finite type, other laws as pushforwards (`RatSeed`, noise seeds). (B) An arbitrary
`FinDist` target with an exact conditional law.

**★Q7. Where the code lives.**
(A) New area `TCSlib/Cryptography/CoinSampling/` (facade + 6 modules) and the two generic relations
in a new `TCSlib/Cryptography/Games/Closeness.lean`. (B) Everything in the new area. (C) Extend
existing files (`Asymptotic/Sampling.lean`, `Games/Hopping.lean`).

**Q8. The disclosed overlap (mixture identity vs `statClose_getD_of_uniform_of_some`).**
(A) Prove the identity beside the old lemma in `Asymptotic/Sampling.lean` and re-derive the old
lemma from it (proof-level). (B) Prove it in the new area, record the overlap in the dedup queue.

**Q9. Existing samplers.**
(A) No retrofit now: `BB1Machine.draw`, `sampleBelowL`, `expSampler` stay; new code uses the bridge;
a backlog row records that `draw` becomes an instance once `rejectBlocksL`'s uniformity on success is
published. (B) Retrofit BB1Machine now.

**★Q10. How the modulus reaches the honest machines (R4 consequence for sPRG/PHFE).**
(A) Every honest algorithm's machine takes the modulus numeral as input (in the index or public
parameters); for PHFE it comes from the group generator's description; efficiency is "uniform PPT
given ⦃p⦄". (B) A parameter generator outputs `p` (as `ExpGroupGen`/`BilinearGen` do), assumed PPT,
and the jobs quote it. (C) Restrict to schedules computable from `1^κ` (only `O(log κ)`-bit primes
today: unusable).

**Q11. Scope of the first PR.**
(A) §7's eight modules (bucket, rejection instance, ZMod, LWE seeds and challenge, efficiency).
(B) Without `Instances` (consumers write their own). (C) Basic + Buckets + Closeness + Transfer only.
