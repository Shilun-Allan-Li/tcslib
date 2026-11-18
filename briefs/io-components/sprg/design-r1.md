# io-sprg design r1: the structured-seed PRG of [JLS26, §2–§4, Theorem 4.1]

**Status.** Design note for the end-to-end Codex job `io-sprg` (campaign `IOComponentsPlan.md`).
The Codex prompt (`dispatch-prompt.md`) points here. Everything marked **proposed** is a starting
shape: Codex may refine it **with disclosure** (REPORT.md § *Deviations from the design note*),
never silently. Settled points (§0) and Seyoon's rulings on the open questions (§9, once ruled)
are binding.

| Pin | Value |
|---|---|
| Campaign plan | `IOComponentsPlan.md` at records `0fec25892d5aea3acde4908d94451f24b3c23b79` (rulings on rounding, sampling, degree) and `a2bf4bac0d545fce1fcb4014ef12b44f9651a658` (subexponential security) |
| Lean base | `<BASE>` (maintainer fills: the head of branch `foundations/subexp`, the owner PR adding `TCSlib/Cryptography/Foundations/Subexponential.lean`; or the records tip once it has merged) |
| Source | [JLS26] PDF, 30 pages, SHA-256 `bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d`, CC BY 4.0; PDF page *k* is article page 1:*k* (checked on pp. 8–21) |
| Content read | §2 (pp. 8–10: Def 2.1, 2.3, the law 𝒟_r(p)), §3 (pp. 10–11: Defs 3.1–3.4, Remarks 3.1–3.2), §4 (pp. 11–21: overview, Construction, Claim 4.1, Prop 4.1, Claim 4.2, Lemma 4.2), §5 (p. 21: Theorem 5.1, the consumer) |

## 0. Settled points (binding)

- **S1 Rounding and "n a sufficiently large polynomial in λ"** (Seyoon, 2026-11-18: maintainer's
  judgment). The convention is §3. Codex may refine with disclosure.
- **S2 Sampling** (Seyoon, 2026-11-18). Non-dyadic laws (uniform ℤ_p for prime p, the LPN noise
  𝒟_r(p), uniform functions [m] → [B]) are stated as **exact finite distributions**: uniform
  draws `Games.ProbComp.sample T` of finite types and their pushforwards, the convention of
  `LWE.Family`/`LWE.Noise`. Samplers are **separate contracts**, not asserted here. The generic
  "sampler bridge with perfect correctness" is deferred library work
  (`IOComponentsPlan.md` § *Deferred library work*). **The job must not build it**, nor
  approximate samplers (`Asymptotic/Sampling.rejectionSample`, `StatClose`, `LWE.sampleFromBits`,
  `Encoding.DyadicUniform.*` are not to be used for this purpose).
- **S3 Degree d, not d + 1** (Seyoon, 2026-11-18). p. 14's boxed G⁽³⁾ carries the factor
  (1 − err) with err in the public seed, hence "degree d + 1". The formal construction (pp. 16–17)
  never multiplies by err: G⁽⁴⁾ = Σ_k G⁽³⁾(P⁽ᵏ⁾, (flag⁽ᵏ⁾, S⁽ᵏ⁾, flag⁽ᵏ⁾·S⁽ᵏ⁾)) and
  Σ_k flag⁽ᵏ⁾ = 1 − err; flag·S is precomputed in the private seed. Statements use **degree d**
  (Theorem 4.1, p. 17), with a one-sentence docstring note on p. 14's wording.
- **S4 Security convention**: non-uniform PPT throughout (`Complexity.NUPPT`, [PS10, Def 26.8]);
  assumptions and security are "every NUPPT has negligible advantage"; every reduction is a
  machine construction with its efficiency proved.
- **S5 Independence**: new files only, in one new directory, plus at most one facade import line;
  no existing file is edited. Stage 2 coordination: §2.4.
- **S6 Out of scope** (plan): FE ⇒ iO, bilateral DLIN/LWE, NC⁰ PRG candidates, OWF ⇒ PRG, and the
  link "an ordinary PRG is an sPRG" to `Pseudorandom/Generators/Asymptotic/Defs` (S2-B owns that
  file; after Stage 2). The overview's warm-up cases (pp. 12–14) are motivation only.
- **S7 Subexponential security** (Seyoon, 2026-11-18, records `a2bf4bac`). An in-house file
  `TCSlib/Cryptography/Foundations/Subexponential.lean` (branch `foundations/subexp`, the job's
  base) provides **the Foundations/Subexponential API**: a smallness predicate (working name
  `SubexpSmall c μ`: eventually `|μ n| ≤ 2^(−n^c)`), a predicate-level helper with the constant
  quantified **before** the adversary (working name `SubexpHard adv := ∃ c > 0, ∀ D, SubexpSmall c
  (adv D)`), the implication to `Negligible`, closure under sums, polynomial factors and constant
  multiples, and re-indexing by a polynomial parameter. Exact names are fixed by that PR; read them
  at `<BASE>`. **The job must reuse this API and must not define its own subexponential notion**
  (a named wrapper such as `SPRG.SubexpSecure` is allowed only as a one-line definition whose body
  is the API predicate applied to the job's advantage function, with its `_iff` reader).
- **S8 Explicit slack** (same ruling). The core theorems are **explicit advantage inequalities
  between NUPPT machines with explicit slack terms**, not "∃ σ, Negligible σ": for every sPRG
  adversary A there are machines B, B′ and κ₀ with, for all κ ≥ κ₀,
  `adv_sPRG A κ ≤ 2κ·adv_LPN B (ℓ κ) + adv_PRG B′ (n κ) + 2·2^(−κ)`. The LPN advantage is
  taken in LPN's own parameter, its dimension ℓ = κ^E (C11), and the PRG's in its seed length n.
  Two corollaries follow: the negligible version (Theorem 4.1, polynomial security) and the
  subexponential version (Theorem 4.1's "if both assumptions are subexponentially secure, the sPRG
  is subexponentially secure"), the latter through the API's re-indexing lemma along ℓ(κ) and n(κ).
  The random-hybrid-index trick is allowed (§4.8).
- **S9 Adversaries**: non-uniform PPT only. Subexponential-*time* adversaries are out of scope;
  "subexponential" means advantage 2^(−κ^c) against NUPPT (JLS26 Def 2.1), as the API states it.

## 1. Source map (paper → Lean, proposed names)

Namespace root `TCSlib.Cryptography.Obfuscation.StructuredSeed` (below `SS.`). The paper's λ is
`κ` in Lean (`λ` is a Lean keyword), as in `LWE` and `Pairing`.

| Paper | Page | Lean (proposed) | File | M |
|---|---|---|---|---|
| Def 2.1 (ε-indistinguishability), Remark 2.1 | 8–9 | the library's `Games.advantage` + `Negligible`, and the Foundations/Subexponential API for the subexponential case (no new definition) | — | — |
| 𝒟_r(p) (0 w.p. 1 − r, else uniform ℤ_p) | 9 | `SS.lpnNoise p W : LWE.Noise` (r = 1/W) and its law theorem `lpnNoise_law` | `LPN` | 0/1 |
| Def 2.3 (δ-LPN_𝔽) | 9–10 | `SS.LPNFamily` (indexed by the secret dimension ℓ, Def 2.3's index), `LPNFamily.toLWE`, `LPNFamily.adv`, `LPNFamily.Assumption`; subexponential hardness = the API predicate on `adv` (S7, Q-S1) | `LPN` | 0 |
| Def 3.1 (sPRG syntax) | 10 | `SS.SPRG` | `Defs` | 0 |
| Remark 3.1 (polynomial stretch), Remark 3.2 | 10 | `SPRG.seedBits`, `SPRG.HasPolyStretch` | `Defs` | 0 |
| Def 3.2 (security), Def 2.1 | 8–10 | `SPRG.game`, `SPRG.adv`, `SPRG.Secure` (negligible); subexponential = the API predicate on `SPRG.adv` (S7) | `Defs` | 0 |
| Def 3.3 (complexity (ℂ, deg d)) | 10 | `SPRG.HasComplexity dPub dPriv` (ℂ = degree-dPub polynomials; Q-S4), `pubDegree`, `privDegree` | `Defs`, `Degree` | 0 |
| Def 3.4 (Boolean PRG, multilinear degree, locality) | 11 | `SS.BoolPRG`, `BoolPRG.adv`, `BoolPRG.Secure`, `BoolPRG.MultilinearRep`, `MultilinearRep.HasLocality`, `BoolPRG.HasStretch` | `BoolPRG` | 0 |
| Construction: parameters | 15 | `SS.Params` and its derived quantities (§3) | `Params` | 0 |
| IdSamp′ (φ_bkt, φ_ind, A) | 15 | `Params.idSamp'`, `Buckets.indexMap` | `Samplers`, `Buckets` | 0/1 |
| 1SdSamp (box) | 16 | `Params.oneSd` (deterministic core), `badSet`, `errSet`, `corr`, `bucketMatrix` | `Samplers` | 0 |
| sparse factorization M_i = U_iV_i | 16 | `SS.sparseFactor` (constructive), `sparseFactor_mul` | `SparseFactor` | 0/1 |
| SdSamp′, err, k* | 15–16 | `Params.sdSampFull`, `Params.sdSamp'` | `Samplers` | 0 |
| Eval′, G⁽⁴⁾ | 16 | `Params.eval'`, `Params.G4` | `Samplers`, `Polys` | 0 |
| G⁽¹⁾, G⁽²⁾, G⁽³⁾ (box, eqs. (3), (4)) | 17 | `Params.G1`, `G2`, `G3` | `Polys` | 0/1 |
| "G⁽⁴⁾ = (1 − err)·y", (deg d, deg 2) | 16–17 | `G4_eval_eq`, `jls_hasComplexity` | `Correctness` | 1 |
| Claim 4.1 (stretch) | 18 | `jls_seedBits_le`, `jls_hasPolyStretch` | `Stretch` | 2 |
| Claim 4.2 (Pr[err = 1] ≤ 2^−λ) | 19–21 | `claim42` | `Claim42`, `Claim42/Load` | 3 |
| Lemma 4.2 (D₀ ≈ D_{λ+1}) | 19 | `lemma42` (quantitative, with machines) | `Hybrids`, `Reductions/*` | 4 |
| Prop 4.1 (H₀ ≈ H₃, γ = O(λε)) | 18–19 | `prop41`: the core explicit-slack inequality (S8) | `Hybrids` | 4 |
| Theorem 4.1 (both clauses) | 11 | `theorem41` (negligible), `theorem41_subexp` (subexponential), `exists_sprg`, `exists_sprg_subexp` | `Security` | 5 |

## 2. Module layout

### 2.1 Directory, namespaces, facades

**Recommended home (Q-S5 A): a new area `TCSlib/Cryptography/Obfuscation/`**, with this job in
`Obfuscation/StructuredSeed/`.
- New facades (new files, allowed): `TCSlib/Cryptography/Obfuscation.lean` (area facade, imports
  `…Obfuscation.StructuredSeed`) and `TCSlib/Cryptography/Obfuscation/StructuredSeed.lean`
  (imports every child; `## Contents`, one line per child).
- **The one facade line**: `import TCSlib.Cryptography.Obfuscation` in `TCSlib.lean`, after
  `import TCSlib.Cryptography.AdvancedEncryption` (the pairing statements' precedent
  `b7ca2547`). `TCSlib.lean` has no `## Contents` list, so nothing else changes in an existing file.
- Why not `Pseudorandom/StructuredSeed/`: `scripts/campaign_style_lint.py`'s `check_facade` would
  then FAIL `Pseudorandom.lean` unless it imports the child, and its `## Contents` list would need a
  bullet (two edits to an existing facade, in an area S2-B is rewriting). Why not split LPN into
  `Cryptography/LPN/` beside `LWE/`: a second new area and a second root line. `LPN.lean` carries a
  docstring note that it is a candidate for promotion next to `LWE/` after the campaign.
- **Coordination**: the PHFE job (`briefs/io-components/phfe/`) lives under
  `AdvancedEncryption/FunctionalEncryption/` and `Pairing/`; it does not create
  `Obfuscation.lean`. Both PRs touch `TCSlib.lean` by one line at different places (trivial merge).
- Namespaces: `TCSlib.Cryptography.Obfuscation.StructuredSeed` for everything; helpers `private`
  or in an inner namespace (`…StructuredSeed.Internal`); no root-namespace declarations.

### 2.2 Files and size plan (policy §1: target 150–600 lines, hard cap 1000)

| File (under `Obfuscation/StructuredSeed/`) | Content | Lines |
|---|---|---|
| `LPN.lean` | `lpnNoise`, `lpnNoise_law`, `LPNFamily`, `toLWE`, `adv`, `Assumption` + readers | 150–250 |
| `BoolPRG.lean` | `BoolPRG`, `game`, `adv`, `Secure`, `HasStretch`, `MultilinearRep`, `HasLocality` + readers | 200–320 |
| `Degree.lean` | `pubDegree`, `privDegree`; `weightedTotalDegree` closure lemmas (§4.4) | 150–280 |
| `Defs.lean` | `SPRG`, `challengeStr`, `game`, `adv`, `Secure`, `HasComplexity`, `seedBits`, `HasPolyStretch` (subexponential: the API predicate, S7) | 250–400 |
| `Params.lean` | `Params`, ℓ, D, n, m, w, W, t, √c, c, B, Γ (§3); side-condition lemmas | 200–350 |
| `Buckets.lean` | `indexMap` (φ_ind from φ_bkt), overfull test, injectivity within buckets | 200–320 |
| `SparseFactor.lean` | `sparseFactor`, `sparseFactor_mul` | 150–260 |
| `Polys.lean` | G⁽¹⁾ (half-split, §4.6), G⁽²⁾, G⁽³⁾, G⁽⁴⁾ as `MvPolynomial`; degree bounds | 350–550 |
| `Samplers.lean` | `oneSd`, `idSamp'`, `sdSampFull`, `sdSamp'`, `eval'`, the instance `jlsSPRG` | 300–450 |
| `Correctness.lean` | M1: good outputs, correction, G⁽³⁾, G⁽⁴⁾ = (1 − err)·y, `jls_hasComplexity` | 450–750 |
| `Stretch.lean` | M2: Claim 4.1 | 250–450 |
| `Claim42/Load.lean` | binomial bound, balls-in-bins tails, Markov step (reusing §B and §F of the sweep) | 300–500 |
| `Claim42.lean` | Cond₁, Cond₂, Cond₃, independence over k, `claim42` | 300–500 |
| `Hybrids.lean` | games H₀–H₃ and D_i, statistical hops, `lemma42`, `prop41` | 350–550 |
| `Reductions/Encode.lean` | challenge strings, mod-p mat-vec on encodings (§4.8), `PolyTimeComputable` | 300–550 |
| `Reductions/LPNHybrid.lean` | the LPN hybrid machine (reparametrized ℓ ↦ κ), run lemma, hardwired advice, residue re-encoding | 300–550 |
| `Reductions/PRG.lean` | the PRG machine (reparametrized n ↦ κ), run lemma | 200–350 |
| `Security.lean` | `jls_secure`, `jls_subexpSecure`, `theorem41`, `theorem41_subexp`, `exists_sprg`, `exists_sprg_subexp` (both corollaries through the Foundations/Subexponential API) | 200–400 |
| `../StructuredSeed.lean`, `../../Obfuscation.lean` | facades | 70–100 |
| **Total** | | **≈ 4,700–7,900** (central ≈ 6,000) |

The plan's estimate was 4–7k. Split a file before it passes ~900 lines; never merge files to save
headers.

### 2.3 Imports (precise, no `import Mathlib`)

Expected TCSlib imports: `Foundations.Subexponential` (the API, S7; on `<BASE>`),
`Games.Probability`, `Games.Advantage`, `Games.Hopping`,
`Games.OracleComp` (for `AllOutputs`), `Games.Bridges.Experiments`, `Foundations.Probability`,
`Foundations.Negligible`, `Foundations.Experiments`, `Asymptotic.Adversary`,
`Asymptotic.ReductionSupport`, `Asymptotic.UniversalLemmas` (for `exists_reparam_pre_post_adv`),
`LWE.Assumption` (and through it `LWE.Basic/Noise/Encoding/Experiments`), `Encoding.Modular`,
`Encoding.DyadicLinearAlgebra`, `Encoding.BinaryArith`, `Complexity.ClassP.BinaryArith.Div`, and
`Authentication.Signatures.Lamport.Averaging` (Markov and averaging, until Stage 2's
`ProbComp.mul_prob_le_expect` is at the base). Mathlib roots expected: `MvPolynomial` (`Variables`,
`Degrees`, `Eval`, `Rename`, `RingTheory.MvPolynomial.Basic`, `…WeightedHomogeneous`),
`Data.Nat.Choose.Bounds`, `Analysis.Complex.Exponential`, `Analysis.SpecialFunctions.Exp`,
`NumberTheory.Bertrand`, `Data.Nat.Log`. Avoid heavy modules nobody needs (e.g.
`Complexity/ClassP/BinaryArith/DetMod`, ~25 min).

**Do not import** (Stage 2 restates their statements, §2.4): `Asymptotic.Ensembles`,
`EnsemblesLemmas`, `OneWay`, `Collections` (directly), `Games.Tapes`,
`Pseudorandom.Generators.Asymptotic.Defs`, `Asymptotic.HardCore.*`.

### 2.4 Stage 2 crossings (from `cleanup-stage2/scope.tsv`, column `owner_file`, and `s2a-workplan-r1.md` §1.3, §4)

| Module the job imports | Stage 2 rows | Kind of touch |
|---|---|---|
| `Foundations/Subexponential.lean` (new, branch `foundations/subexp`) | none (not in `scope.tsv`; an owner PR outside Stage 2) | — (names fixed by that PR; read at `<BASE>`) |
| `Games/Probability.lean` | S2-DL-16 (J0): adds `ProbComp.mul_prob_le_expect` | **additive** (new declaration, CS1-Q9) |
| `Authentication/Signatures/Lamport/Averaging.lean` | S2-RP-102: `expect_favourable_of_success` re-proved from `mul_prob_le_expect` | proof-level; statement and name kept |
| `Asymptotic/UniversalLemmas.lean` | S2-SL-231/232: seal fixes in `exists_reparam_pre_post(_adv)` | proof-level; statements unchanged |
| `Complexity/Randomized/PPT.lean` (via `Adversary`) | S2-BO-031: `runAtL_ofPolyTimeUniform` | proof-level |
| `Foundations/BitLists.lean` (transitive) | S2-DL-01/02 (move-in of `decide_singleton_eq_true`), S2-RP-042 | additive + proof-level |
| `Pseudorandom/Generators.lean` (transitive, via `ReductionSupport`) | S2-RD-29: adds `prgStep_eq` | additive |
| `Encoding/DyadicUniform.lean` (only if imported) | S2-RP-088 | proof-level |
| `Asymptotic/Collections*.lean` (transitive, via `UniversalLemmas`) | S2-BO-036/037 (private, in-file) and seal/re-point rows | private statement changes, not visible to the job |

Not touched by Stage 2: `Games/Advantage`, `Hopping`, `OracleComp`, `Bridges/Experiments`,
`Foundations/Probability`, `Negligible`, `Experiments`, `Asymptotic/Adversary`,
`ReductionSupport`, `Complexity/Randomized/Closure`, all of `LWE/`, `Encoding/Modular`,
`DyadicLinearAlgebra`, `DyadicArithmetic`, `Encoding/BinaryArith`, `Complexity/ClassP/BinaryArith/*`,
`InformationTheory/*` except `Entropy` and `LeftoverHash` (proof-level). None of the 14 restated
headers of `s2a-workplan-r1.md` §1.3 is used. **Conclusion: every touch the job sees is additive
or proof-level**; at landing the maintainer replays on the then-current tip.

## 3. Conventions (S1: parameters, rounding, indexing)

Paper symbols → Lean (all ℕ unless stated), for a fixed `P : Params` at security parameter κ.

| # | Quantity | Convention | Why |
|---|---|---|---|
| C1 | indexing | **One security parameter κ.** The sPRG of Defs 3.1–3.3 is a family indexed by κ alone; the paper's input-length index n becomes the schedule n(κ) below, fixed by the construction's exponent `E`. | Def 3.1's (λ, n) family with a fixed poly(λ) slack (Remark 3.2) needs n to be rounded to a D-th power and ℓ^{δ/2} to an integer for *every* n; a κ-indexed family with a polynomial schedule avoids every such rounding. "n a sufficiently large polynomial in λ" becomes "E ≥ E₀(d, δ, τ)" (C10) for the stretch, while security holds for every E ≥ 1 (C9), so a consumer still picks n as large a polynomial as it wants. |
| C2 | p | `p κ` prime with `2 ^ κ < p κ ≤ 2 ^ (κ + 1)`: a (κ + 1)-bit prime; residue width `κ + 1` | the paper's "λ-bit prime" with λ = κ + 1 (no λ-bit prime exists for λ ≤ 1); `Nat.exists_prime_lt_and_le_two_mul` gives one for the existential corollary. Security never uses the lower bound; Claim 4.1 uses the width. |
| C3 | D | `D := (d + 1) / 2` (= ⌈d/2⌉); assume `1 ≤ d` | d = 0 makes the PRG constant (vacuous) and n = 1. |
| C4 | ℓ, n | `ℓ κ := κ ^ E` (`1 ≤ E`), `n κ := ℓ κ ^ D` | ℓ = n^{1/⌈d/2⌉} exactly; n ≥ κ; ℓ and n are polynomial in κ and ≥ κ, which is what the API's re-indexing needs (S8). |
| C5 | m | `m κ := G.outLen (n κ)` (the PRG's own length; `HasStretch τ` gives m ≥ n^τ) | no truncation lemma needed. |
| C6 | ℓ^{δ/2}, ℓ^δ, r | `w κ := max 1 ⌊(ℓ κ : ℝ) ^ (δ / 2)⌋₊`, `W κ := w κ ^ 2`; noise rate `r := 1 / W` | one integer carries ℓ^{δ/2} and ℓ^δ, so √c is an integer by construction; `W ≤ ℓ^δ` gives `r ≥ ℓ^{−δ}`: the assumed LPN problem is **at least as noisy** as Def 2.3's (rounding in the safe direction); `W ≥ ℓ^δ/4` once ℓ^{δ/2} ≥ 2, so E|BAD| ≤ c_loc·m/W stays O(m ℓ^{−δ}). The noise law is the finite law `lpnNoise p W` (S2). |
| C7 | t, √c, c | `t κ := κ`, `rc κ := t κ * w κ` (√c), `cap κ := rc κ ^ 2` (c = t²W) | c is a perfect square by construction; the paper's capacity c is renamed `cap` (Def 3.4's locality is `cLoc`), removing the paper's double use of "c". |
| C8 | B, Γ | `B κ := max 1 ((m κ * t κ + W κ - 1) / W κ)` (⌈mt/W⌉, at least 1); `Γ κ := m κ * Nat.log 2 (n κ) / W κ` (⌊m log₂ n / W⌋) | B ≥ 1 keeps `Fin m → Fin B` inhabited; Γ ≤ B ⇔ log₂ n ≤ t (side condition). |
| C9 | side conditions | stated as **theorems**, eventually in κ: `Γ ≤ B`, `4 * cLoc ≤ Nat.log 2 (n κ)`, `κ ≤ n κ` (C4), B ≤ poly(κ); `claim42` is "∃ κ₀, ∀ κ ≥ κ₀" | log₂ n = E·D·log₂ κ grows, and is ≤ κ eventually; the paper's "for sufficiently large λ" made explicit. |
| C10 | stretch exponent | `E₀ d δ τ := ⌊max (10 / δ) (5 / (τ - 1))⌋₊ + 1` (proposed; confirm in M2) | Claim 4.1's bound seedBits ≤ C·κ⁵·(n + m/w) (the paper's λ⁵ factor); κ⁵m/w ≤ m^{1/τ'} for some τ' > 1 iff Eδ/2 > 5 (m ≤ poly(n)), and κ⁵n ≤ m^{1/τ'} for some τ' > 1 iff E·D·(τ − 1) > 5 (m ≥ n^τ). A finer count (κ²n for the public part) allows a smaller E₀; any change is disclosed (E is a free schedule parameter). |

| C11 | the LPN family | **Indexed by its own dimension ℓ** (Def 2.3's index; S8). At every ℓ: `κOf ℓ := Nat.findGreatest (· ^ E ≤ ℓ) ℓ` (so `κOf (κ ^ E) = κ`, a reader), `samples ℓ := ℓ ^ D`, `modulus ℓ := p (κOf ℓ)`, `noiseDen ℓ := (max 1 ⌊ℓ^{δ/2}⌋₊) ^ 2`, residue width `ℓ + 1` | The construction only meets ℓ = κ^E, where every value equals the sPRG's (same prime, same W). `LWE.Family` needs a `PolyExpr` width; ℓ + 1 ≥ κOf ℓ + 1 is one, so the LWE challenge carries (ℓ+1)-bit residues and the hop machine re-encodes them at the sPRG's κ + 1 bits (one `PolyTimeComputable` map). This is Def 2.3 with η_n = D, η_p = 1/E through the prime schedule, and rate 1/W (C6). |

**Disclosed alternative (not adopted).** Def 3.1 literally: a two-parameter family (λ, n) with
`seedBits λ n ≤ n · q(λ)` for a fixed polynomial q and `outLen λ n ≥ n^{τ'}`, with the construction
rounding n down to the nearest valid shape (ℓ := ⌊n^{1/D}⌋, w := ⌊ℓ^{δ/2}⌋, …) and security for
every polynomial schedule n(λ) ≥ λ. Rejected: two rounding layers, a statement-level "for every
schedule", and no consumer in the campaign that needs the (λ, n) form before the bootstrapping is
designed. The docstrings of `SPRG` and `theorem41` state the single-index form as a deviation.

## 4. Proposed statement shapes (proposed; Codex may refine with disclosure)

Lean-like; `κ` is the security parameter; universes `Type` (as `ProbComp` requires). Every public
definition lands with its readers (policy §1: `simps (config := { isSimp := false })` for
structure-valued ones, `_eq` by `rfl`, `_iff` for predicates); no `@[simp]`.

### 4.1 LPN over 𝔽_p (Def 2.3), as an LWE family

```lean
/-- The LPN noise 𝒟_{1/W}(p) [JLS26, §2, before Definition 2.3]: a uniform seed (a, x) of
`Fin W × ZMod p` gives `x` if `a = 0` and `0` otherwise (rate r = 1/W). -/
def lpnNoise (p W : ℕ) [NeZero p] [NeZero W] : LWE.Noise where
  Coins := Fin W × ZMod p
  sample c := if c.1 = 0 then (c.2.val : ℤ) else 0

/-- The law: `Pr[e = 0] = 1 - 1/W + 1/(W p)`, `Pr[e = z] = 1/(W p)` for `z ≠ 0`. -/
theorem lpnNoise_law (p W : ℕ) [NeZero p] [NeZero W] (z : ZMod p) :
    uprob (fun c => ((lpnNoise p W).sample c : ZMod p) = z) =
      if z = 0 then 1 - 1 / W + 1 / (W * p) else 1 / (W * p)

/-- An LPN-over-𝔽_p family [JLS26, Definition 2.3], indexed by the secret dimension ℓ (the
definition's own parameter): n(ℓ) samples, a prime modulus p(ℓ), noise 𝒟_{1/W(ℓ)}(p(ℓ)). -/
structure LPNFamily where
  samples modulus noiseDen : ℕ → ℕ
  modulus_prime : ∀ ℓ, (modulus ℓ).Prime
  noiseDen_pos : ∀ ℓ, 0 < noiseDen ℓ
  samplesBound residueBits : PolyExpr
  samples_le : ∀ ℓ, samples ℓ ≤ samplesBound.eval ℓ
  modulus_le_pow : ∀ ℓ, modulus ℓ ≤ 2 ^ residueBits.eval ℓ

def LPNFamily.toLWE (F : LPNFamily) : LWE.Family   -- dimension ℓ := ℓ; noise ℓ := lpnNoise …
noncomputable def LPNFamily.adv (F : LPNFamily) (D : NUPPT) (ℓ : ℕ) : ℝ := F.toLWE.advantageAt D ℓ
def LPNFamily.Assumption (F : LPNFamily) : Prop := ∀ D : NUPPT, Negligible (F.adv D)
theorem LPNFamily.assumption_iff (F : LPNFamily) :
    F.Assumption ↔ LWE.DLWEAssumption F.toLWE
-- subexponential hardness in the dimension: the API predicate applied to `F.adv` (S7)
```

Docstring deviations: (i) `LWE`'s orientation `(A, A s + e)` with `A ∈ ℤ_p^{n×ℓ}` is the transpose
of the paper's `(A, s A + e)`, `A ∈ ℤ_p^{ℓ×n}` (a bijection of the uniform matrix; the
construction stores the n × ℓ matrix); (ii) one schedule instead of Def 2.3's
"∀ η_p, ∀ p(ℓ), ∀ η_n" (Q-S1); (iii) rate 1/W (C6); (iv) residue width ℓ + 1 (C11). The
construction's family `P.lpnFamily` is C11's (`lpnFamilyOf d δ E p` for `exists_sprg`).

### 4.2 Boolean PRG with locality and multilinear degree (Def 3.4)

```lean
/-- A Boolean PRG with a function index [JLS26, Definition 3.4], indexed by its seed length n. -/
structure BoolPRG where
  Idx : ℕ → Type
  [idxFintype : ∀ n, Fintype (Idx n)]  [idxNonempty : ∀ n, Nonempty (Idx n)]
  idSamp : (n : ℕ) → ProbComp (Idx n)                -- the law of IdSamp(1^n)
  encIdx : (n : ℕ) → Idx n → List Bool               -- how a distinguisher receives I
  idxBits : PolyExpr
  encIdx_length_le : ∀ n I, (encIdx n I).length ≤ idxBits.eval n
  outLen : ℕ → ℕ
  outBound : PolyExpr
  outLen_le : ∀ n, outLen n ≤ outBound.eval n
  eval : (n : ℕ) → Idx n → (Fin n → Bool) → Fin (outLen n) → Bool

noncomputable def BoolPRG.game (G : BoolPRG) (D : NUPPT) (real : Bool) (n : ℕ) : ProbComp Bool :=
  (G.idSamp n).bind fun I => (sample (Fin n → Bool)).bind fun σ =>
  (sample (Fin (G.outLen n) → Bool)).bind fun w => (sample (D.Coins n)).bind fun ρ =>
  .pure (D.distinguisherL n
    (pairEncode (G.encIdx n I) (List.ofFn (if real then G.eval n I σ else w))) ρ)
noncomputable def BoolPRG.adv (G : BoolPRG) (D : NUPPT) (n : ℕ) : ℝ :=
  advantage (G.game D true n) (G.game D false n)
def BoolPRG.Secure (G : BoolPRG) : Prop := ∀ D : NUPPT, Negligible (G.adv D)
-- subexponential security in the seed length: the API predicate applied to `G.adv` (S7)
def BoolPRG.HasStretch (G : BoolPRG) (τ : ℝ) : Prop := ∀ n, (n : ℝ) ^ τ ≤ G.outLen n

/-- Multilinear degree-d representation over ℤ, carried as data (no uniqueness theorem). -/
structure BoolPRG.MultilinearRep (G : BoolPRG) (d : ℕ) where
  poly : (n : ℕ) → G.Idx n → Fin (G.outLen n) → MvPolynomial (Fin n) ℤ
  poly_mem_restrictDegree : ∀ n I j, poly n I j ∈ MvPolynomial.restrictDegree (Fin n) ℤ 1
  totalDegree_poly_le : ∀ n I j, (poly n I j).totalDegree ≤ d
  eval_poly : ∀ n I σ j,
    MvPolynomial.eval (fun i => ((σ i).toNat : ℤ)) (poly n I j) = ((G.eval n I σ j).toNat : ℤ)
/-- Locality cLoc: every output polynomial has at most cLoc variables. -/
def BoolPRG.MultilinearRep.HasLocality {G d} (R : G.MultilinearRep d) (cLoc : ℕ) : Prop :=
  ∀ n I j, (R.poly n I j).vars.card ≤ cLoc
```

Docstring deviations: PRG security in its seed length n (Def 3.4 calls the PRG an sPRG with
IdSamp(1^n)); the representation and locality are required for every `I : Idx n` (choose `Idx`
as the support of IdSamp; the paper says "every I in the support"); locality is read on the
representation's variables (by uniqueness of multilinear representations this is the paper's
semantic locality, which is not formalized); `HasStretch` is m(n) ≥ n^τ (the paper has
m = n^τ). The variable set `(R.poly n I j).vars` is the paper's `Vars_j` (p. 16).

### 4.3 sPRG syntax, security, complexity, stretch (Defs 3.1–3.3, Remark 3.1)

```lean
/-- A structured-seed Boolean PRG over ℤ_p [JLS26, Definition 3.1], one security parameter
(convention C1). Seeds are vectors over ℤ_{p(κ)} (Definition 3.3's view); the public seed is a
`Fin`-indexed vector (the distinguisher reads it), the private seed is indexed by any finite type. -/
structure SPRG where
  modulus : ℕ → ℕ
  modulus_prime : ∀ κ, (modulus κ).Prime
  residueBits : PolyExpr
  modulus_le_pow : ∀ κ, modulus κ ≤ 2 ^ residueBits.eval κ
  Idx : ℕ → Type  [Fintype, Nonempty]
  idSamp : (κ : ℕ) → ProbComp (Idx κ)
  encIdx : (κ : ℕ) → Idx κ → List Bool;  idxBits : PolyExpr;  encIdx_length_le : …
  pubLen : ℕ → ℕ;  Priv : ℕ → Type  [Fintype, DecidableEq]
  sdSamp : (κ : ℕ) → Idx κ →
    ProbComp ((Fin (pubLen κ) → ZMod (modulus κ)) × (Priv κ → ZMod (modulus κ)))
  outLen : ℕ → ℕ;  seedBound outBound : PolyExpr;  pubLen_le, card_priv_le, outLen_le : …
  eval : (κ : ℕ) → Idx κ →
    (Fin (pubLen κ) → ZMod (modulus κ)) × (Priv κ → ZMod (modulus κ)) → Fin (outLen κ) → Bool

/-- `⟨I, ⟨P, z⟩⟩`: index, public seed (fixed-width residues), output string. -/
def SPRG.challengeStr (S : SPRG) (κ : ℕ) (I : S.Idx κ) (P : Fin (S.pubLen κ) → ZMod _)
    (z : Fin (S.outLen κ) → Bool) : List Bool :=
  pairEncode (S.encIdx κ I)
    (pairEncode (Encoding.Modular.encodeVector (S.residueBits.eval κ) P) (List.ofFn z))

/-- Definition 3.2: `(I, P, Eval(I, sd))` versus `(I, P, r)`. -/
noncomputable def SPRG.game (S : SPRG) (D : NUPPT) (real : Bool) (κ : ℕ) : ProbComp Bool :=
  (S.idSamp κ).bind fun I => (S.sdSamp κ I).bind fun sd =>
  (sample (Fin (S.outLen κ) → Bool)).bind fun r => (sample (D.Coins κ)).bind fun ρ =>
  .pure (D.distinguisherL κ (S.challengeStr κ I sd.1 (if real then S.eval κ I sd else r)) ρ)
noncomputable def SPRG.adv (S : SPRG) (D : NUPPT) (κ : ℕ) : ℝ :=
  advantage (S.game D true κ) (S.game D false κ)
def SPRG.Secure (S : SPRG) : Prop := ∀ D : NUPPT, Negligible (S.adv D)
-- subexponential security (JLS26 Def 2.1, NUPPT adversaries): the API predicate on `S.adv` (S7)

/-- Definition 3.3 for ℂ = degree-dPub polynomials, composite form: for every index there are
output polynomials over (public ⊕ private) variables, of public degree ≤ dPub and private degree
≤ dPriv, that compute Eval (as 0/1 in ℤ_p) on every seed SdSamp can output. -/
def SPRG.HasComplexity (S : SPRG) (dPub dPriv : ℕ) : Prop :=
  ∀ κ (I : S.Idx κ), ∃ Q : Fin (S.outLen κ) →
      MvPolynomial (Fin (S.pubLen κ) ⊕ S.Priv κ) (ZMod (S.modulus κ)),
    (∀ j, pubDegree (Q j) ≤ dPub ∧ privDegree (Q j) ≤ dPriv) ∧
    (S.sdSamp κ I).AllOutputs fun sd => ∀ j,
      (((S.eval κ I sd j).toNat : ℕ) : ZMod _) = MvPolynomial.eval (Sum.elim sd.1 sd.2) (Q j)

def SPRG.seedBits (S : SPRG) (κ : ℕ) : ℕ :=
  (S.pubLen κ + Fintype.card (S.Priv κ)) * S.residueBits.eval κ
/-- Polynomial stretch (Remark 3.1, single-index form C1). -/
def SPRG.HasPolyStretch (S : SPRG) : Prop :=
  ∃ τ' : ℝ, 1 < τ' ∧ ∃ κ₀, ∀ κ ≥ κ₀, ((S.seedBits κ : ℝ)) ^ τ' ≤ S.outLen κ
```

Docstring deviations: single index (C1); seeds as ℤ_p vectors with bit length counted by
`seedBits`; Def 3.3 only for ℂ = degree-d polynomials and in composite form (Q-S4; equivalent to
Process_I = "all monomials of degree ≤ d of P" and Q_I of degree 1 in P̄); "Q_I efficiently
generated from I" and "p efficiently computable" are not formalized, and no efficiency of
IdSamp/SdSamp/Eval is asserted (S2, Q-S3), exactly as `LWE.Family`'s docstring does.

### 4.4 Degree notions (Mathlib, read at the pin; no Lean run)

- Per-group degree = **`MvPolynomial.weightedTotalDegree`** with an indicator weight
  (`Mathlib/RingTheory/MvPolynomial/WeightedHomogeneous.lean:90`):
  `pubDegree q := q.weightedTotalDegree (Sum.elim (fun _ => 1) (fun _ => 0))`,
  `privDegree q := q.weightedTotalDegree (Sum.elim (fun _ => 0) (fun _ => 1))`.
  Available: `le_weightedTotalDegree` (:112), `weightedTotalDegree_zero` (:108),
  `weightedTotalDegree_one` (`…/Homogeneous.lean:50`, weight 1 is `totalDegree`),
  `weightedTotalDegree_rename_of_injective` (`Homogeneous.lean:56`), `Finsupp.weight`
  (`Data/Finsupp/Weight.lean:74`), `MvPolynomial.support_mul` (`Algebra/MvPolynomial/Basic.lean:554`).
- **Missing at the pin** (searched: no `weightedTotalDegree_add/_mul/_sum/_prod/_C/_X`): the job
  writes them generically for `w : σ → ℕ` in `Degree.lean`, following `totalDegree_mul`
  (`Algebra/MvPolynomial/Degrees.lean:403`) and `totalDegree_add` (:373), disclosed as Mathlib-shaped
  additions (upstream candidates).
- Multilinear (Def 3.4): `MvPolynomial.restrictDegree σ R 1` and `mem_restrictDegree`
  (`RingTheory/MvPolynomial/Basic.lean:101, 111`); degree `totalDegree`; variables `vars`
  (`Algebra/MvPolynomial/Variables.lean:65`), `vars_mul` (:114), `vars_add_subset` (:100);
  evaluation agreement off the variables `eval₂Hom_congr'` (`Variables.lean:253`) /
  `eval₂_congr` (`Eval.lean:204`); `eval_map` (`Eval.lean:417`) for ℤ → ℤ_p.
- Not needed: `sumAlgEquiv` (`Algebra/MvPolynomial/Equiv.lean:295`), `degreeOf`,
  `restrictTotalDegree`, `TensorProduct`, `Matrix.kroneckerMap`. The tensor power s̄^{⊗D} is the
  function `α ↦ ∏ t, s̄ (α t)` on `Fin D → Fin (ℓ + 1)`, expanded with `Finset.prod_univ_sum`
  (`Algebra/BigOperators/Ring/Finset.lean:150`).

### 4.5 Parameters

```lean
structure Params where
  d : ℕ;  one_le_d : 1 ≤ d
  δ : ℝ;  δ_pos : 0 < δ;  δ_lt_one : δ < 1
  E : ℕ;  one_le_E : 1 ≤ E
  G : BoolPRG;  R : G.MultilinearRep d
  p : ℕ → ℕ;  p_prime : ∀ κ, (p κ).Prime;  p_bits : ∀ κ, 2 ^ κ < p κ ∧ p κ ≤ 2 ^ (κ + 1)
-- derived (each with an `_eq` reader): D ℓ n m w W t rc cap B Γ as in §3; lpnFamily : LPNFamily
-- side conditions (M0 statements, M3 proofs):
theorem Params.Γ_le_B (P : Params) : ∃ κ₀, ∀ κ ≥ κ₀, P.Γ κ ≤ P.B κ
theorem Params.le_log_n (P : Params) (c : ℕ) : ∃ κ₀, ∀ κ ≥ κ₀, c ≤ Nat.log 2 (P.n κ)
theorem Params.le_n (P : Params) (κ : ℕ) : κ ≤ P.n κ
```

### 4.6 The construction (pp. 15–17)

Proposed concrete types at κ: `Idx' κ := G.Idx (n κ) × (Fin (m κ) → Fin (B κ)) ×
Matrix (Fin (n κ)) (Fin (ℓ κ)) (ZMod (p κ))` (I, φ_bkt, A stored transposed; φ_ind is derived);
public seed `Fin (κ * n κ + 1)` (the b⁽ᵏ⁾ in order, then err), via `finProdFinEquiv`/`Fin.cast`
readers; private seed per instance `Unit ⊕ SVar ⊕ SVar` (flag, S, flag·S) with
`SVar := (Fin D → Fin (ℓ + 1)) ⊕ (Fin B × (Fin rc × Fin t ⊕ Fin t × Fin rc))` (S₁ = s̄^{⊗D}, then
U_i, V_i), and `Priv κ := Fin κ × (Unit ⊕ SVar ⊕ SVar)`.

- **Buckets** (`Buckets.lean`): `overfull φ := ∃ i, cap < (univ.filter (φ · = i)).card`;
  `indexMap φ j : Fin rc × Fin rc` = the rank of j inside its bucket, split as (rank / rc,
  rank % rc), or `(0, 0)` everywhere if `overfull φ` (the paper's constant (1, 1)). Lemma:
  `¬ overfull φ → φ j₁ = φ j₂ → indexMap φ j₁ = indexMap φ j₂ → j₁ = j₂`.
- **1SdSamp core** (`Samplers.lean`): `oneSd I' σ s e` (deterministic in the seed σ, secret s and
  noise e) returns flag, b = A s + e + σ, S₁ = s̄^{⊗D} (s̄ = s‖1), and U_i, V_i:
  `errSet e := {i | e i ≠ 0}`, `badSet := {j | ((R.poly n I j).vars ∩ errSet e).Nonempty}`,
  `flag := ¬ (Γ < |BAD| ∨ overfull φ ∨ ∃ i, t < |φ⁻¹(i) ∩ BAD|)`,
  `corr j := y_j − y'_j` with `y_j = Eval_I(σ)_j` and `y'_j = (poly j mapped to ℤ_p)(σ + e)`,
  `bucketMatrix i : Matrix (Fin rc) (Fin rc) (ZMod p)` with entry `corr j` at `indexMap φ j` for
  `φ j = i`, and `(U_i, V_i) := if flag then sparseFactor (bucketMatrix i) t else 0`.
- **Sparse factorization** (`SparseFactor.lean`, the maintainer note: constructive, no rank theory):
  for `M` with at most t nonzero entries, list them in a fixed order; column r of `U` holds the r-th
  entry's value at its row, row r of `V` holds `1` at its column. `sparseFactor_mul :
  (#nonzero M ≤ t) → U * V = M` (`Matrix.mul_apply`, sum over r).
- **Laws**: `idSamp' κ := G.idSamp (n κ) × sample (Fin m → Fin B) × sample (Matrix …)`;
  `sdSampFull κ I'` draws σ ← `sample (Fin n → Bool)` and **one** joint
  `sample (Fin κ → (Fin ℓ → ZMod p) × (Fin n → Fin W × ZMod p))` (κ independent instances), then
  computes the κ outputs of `oneSd`, `err := !(∃ k, flag k)`, `k* := min {k | flag k}`, zeroes the
  later flags, and assembles P′ = ({b⁽ᵏ⁾}, err) and S′ = ({flag⁽ᵏ⁾, S⁽ᵏ⁾, flag⁽ᵏ⁾·S⁽ᵏ⁾}); it
  returns σ, the instances and the seed. `sdSamp' := (·.seed) <$> sdSampFull`.
- **Polynomials** (`Polys.lean`), over `MvPolynomial (Fin (κ * n + 1) ⊕ Priv κ) (ZMod p)`:
  - for a multilinear monomial with support h (|h| ≤ d ≤ 2D), list h increasingly, pad with a
    marker `none` to length 2D, and cut into halves h₁, h₂ of length D;
    `L_{hₖ} := Σ_{α : Fin D → Fin (ℓ+1)} (∏_t c_{hₖ t}(α t)) · X(S₁ α)` with
    `c_i(a) := C(−A i a)` for a < ℓ, `X(b_i)` for a = ℓ, and `c_none(a) := [a = ℓ]`;
    `G1_j := Σ_{mono} C(coeff) · L_{h₁} · L_{h₂}` (eq. (3), split at half degree; the half-split
    makes the private degree 2 and the public degree |h| ≤ d);
  - `G2_j := G1_j + Σ_{r<t} X(U_{φ j}[indexMap j .1, r]) · X(V_{φ j}[r, indexMap j .2])`;
  - `G3_j` = `G2_j` with the first factor of every quadratic term (the `L_{h₁}` and the `U`
    variable) read from the flag·S copy, so that on the seeds `G3_j = flag · G2_j` (eq. (4)) while
    the private degree stays 2;
  - `G4_j := Σ_k G3⁽ᵏ⁾_j`; `eval' I' sd j := decide (MvPolynomial.eval (Sum.elim …) (G4 I' j) = 1)`.
- `jlsSPRG P : SPRG` with modulus `p`, `residueBits := .var + 1`, the laws and `eval'` above.

### 4.7 Results

```lean
-- M1 (algebraic correctness, pp. 16–17)
theorem G1_eval_of_good … : j ∉ badSet … → eval (seed) (G1 j) = y_j          -- "∀ j ∉ BAD"
theorem G2_eval_of_flag … : flag = true → eval (seed) (G2 j) = y_j
theorem G4_eval_eq (P) (κ) (I') : (P.sdSampFull κ I').AllOutputs fun x =>
    ∀ j, MvPolynomial.eval (Sum.elim x.seed.1 x.seed.2) (P.G4 I' j) =
      if x.err then 0 else ((P.G.eval _ I'.1 x.σ j).toNat : ZMod _)
theorem jls_hasComplexity (P : Params) : (jlsSPRG P).HasComplexity P.d 2
-- M2 (Claim 4.1)
theorem jls_seedBits_le (P) : ∃ C, ∀ κ, (jlsSPRG P).seedBits κ ≤
    C * (κ + 1) ^ 5 * (P.n κ + P.m κ / P.w κ + 1)
theorem jls_hasPolyStretch (P) {τ} (hτ : 1 < τ) (hs : P.G.HasStretch τ)
    (hE : E₀ P.d P.δ τ ≤ P.E) : (jlsSPRG P).HasPolyStretch
-- M3 (Claim 4.2)
theorem claim42 (P : Params) {cLoc} (hLoc : P.R.HasLocality cLoc) : ∃ κ₀, ∀ κ ≥ κ₀,
    prob ((P.idSamp' κ).bind fun I' => P.sdSampFull κ I') (·.err = true) ≤ (2 : ℝ)⁻¹ ^ κ
-- M4 (Lemma 4.2, explicit slack, machines; hybrids D_i of p. 19 with φ included, tail y or r)
theorem lemma42 (P) (A : NUPPT) : ∃ B B' : NUPPT, ∀ κ,
    advantage (P.hyb A .prg 0 κ) (P.hyb A .prg (κ + 1) κ) ≤
      κ * P.lpnFamily.adv B (P.ℓ κ) + P.G.adv B' (P.n κ)
-- the CORE inequality (S8): Proposition 4.1 with explicit slack
theorem prop41 (P) {cLoc} (hLoc : P.R.HasLocality cLoc) (A : NUPPT) :
    ∃ B B' : NUPPT, ∃ κ₀, ∀ κ ≥ κ₀,
      (jlsSPRG P).adv A κ ≤
        2 * κ * P.lpnFamily.adv B (P.ℓ κ) + P.G.adv B' (P.n κ) + 2 * (2 : ℝ)⁻¹ ^ κ
-- M5 (Theorem 4.1: both clauses, as corollaries of `prop41`)
theorem jls_secure (P) {cLoc} (hLoc) (hG : P.G.Secure) (hLPN : P.lpnFamily.Assumption) :
    (jlsSPRG P).Secure
theorem jls_subexpSecure (P) {cLoc} (hLoc)
    (hG : SubexpHard P.G.adv) (hLPN : SubexpHard P.lpnFamily.adv) :   -- API names TBD (S7)
    SubexpHard (jlsSPRG P).adv
theorem theorem41 (P) {cLoc τ} (hLoc) (hτ : 1 < τ) (hs : P.G.HasStretch τ)
    (hE : E₀ P.d P.δ τ ≤ P.E) (hG : P.G.Secure) (hLPN : P.lpnFamily.Assumption) :
    (jlsSPRG P).Secure ∧ (jlsSPRG P).HasComplexity P.d 2 ∧ (jlsSPRG P).HasPolyStretch
theorem theorem41_subexp (P) {cLoc τ} (hLoc) (hτ) (hs) (hE)
    (hG : SubexpHard P.G.adv) (hLPN : SubexpHard P.lpnFamily.adv) :
    SubexpHard (jlsSPRG P).adv ∧ (jlsSPRG P).HasComplexity P.d 2 ∧ (jlsSPRG P).HasPolyStretch
theorem exists_sprg {d cLoc : ℕ} (hd : 1 ≤ d) {δ τ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hτ : 1 < τ)
    (G : BoolPRG) (R : G.MultilinearRep d) (hLoc : R.HasLocality cLoc) (hs : G.HasStretch τ)
    (hG : G.Secure) (p : ℕ → ℕ) (hp : ∀ κ, (p κ).Prime ∧ 2 ^ κ < p κ ∧ p κ ≤ 2 ^ (κ + 1))
    (hLPN : ∀ E, 1 ≤ E → (lpnFamilyOf d δ E p hp).Assumption) :
    ∃ S : SPRG, S.modulus = p ∧ S.Secure ∧ S.HasComplexity d 2 ∧ S.HasPolyStretch
theorem exists_sprg_subexp … (hG : SubexpHard G.adv)
    (hLPN : ∀ E, 1 ≤ E → SubexpHard (lpnFamilyOf d δ E p hp).adv) :
    ∃ S : SPRG, S.modulus = p ∧ SubexpHard S.adv ∧ S.HasComplexity d 2 ∧ S.HasPolyStretch
```

Notes. `prop41` is the paper's γ = O(λε) with explicit constants (S8): H₀ ≈ H₁ and H₂ ≈ H₃ cost
Pr[err = 1] ≤ 2^{−κ} each (`Hopping.abs_prob_sub_le_of_agree`, `claim42`); H₁ ≈ H₂ is two chains
of κ LPN hops (tails y and r) plus one PRG hop. `B` is one machine for all 2κ hops. The paper's
D_i omit φ; including φ (independent, Prop 4.1's remark (i)) is a docstring deviation.
`claim42` and `prop41` hold for every E ≥ 1; only `HasPolyStretch` needs E ≥ E₀.
**Corollaries.** Negligible: `Negligible.comp_of_le` (or the API's re-indexing) moves
`adv_LPN B` along ℓ κ ≥ κ and `adv_PRG B'` along n κ ≥ κ, then `Negligible.polyExpr_mul` (the 2κ
factor), `.add`, `negligible_two_pow_neg`. Subexponential: the API's re-indexing by the polynomial
parameters ℓ κ = κ^E and n κ = κ^{ED}, its closure under polynomial factors, constant multiples and
sums, and 2^{−κ} small; the constant of the conclusion depends only on the two hypotheses' constants
and E, D, so it precedes the adversary, as the API's predicate requires. `SubexpHard` stands for
the API's predicate; use the names fixed at `<BASE>`.

### 4.8 Reductions as machines (route)

- **Non-uniform hardwiring** (follows from S2 + S4). A hop's two games differ in one coordinate;
  everything else (I, φ, σ, the other instances' s, e or u, the tail) is averaged out:
  `|E_ω f ω − E_ω g ω| ≤ E_ω |f ω − g ω| ≤ |f ω* − g ω*|`
  (`ProbComp.abs_expect_sub_le_expect`, `LamportReduction.exists_expect_sample_le`), and ω* is
  written into the reduction's **advice**. The machines therefore never sample ℤ_p, the noise or a
  random function: no sampler is needed, consistent with S2. The paper's reductions sample; this
  is a proof-route deviation, recorded in the sketches.
- **The hop index.** Either way is allowed (Seyoon: "the random-hybrid-index trick is fine"):
  (a) chosen by advice (`Games.exists_advantage_hybrid_gap`; exact factor κ per chain), or
  (b) drawn from the machine's coins. A uniform index is exactly samplable from fair coins only on a
  power-of-two range, so (b) pads each chain to 2^⌈log₂ κ⌉ hops with zero-gap hops and pays a factor
  ≤ 2κ; the statement's constant then changes accordingly (disclose). (a) is recommended.
- **LPN hop machine** (`Reductions/LPNHybrid.lean`): `NUPPT.exists_reparam_pre_post_adv`
  (`Asymptotic/UniversalLemmas.lean:125`) from the LPN parameter L to κ(L) = `κOf L` (C11;
  κOf L ≤ L), advice ω* and the hop choice; pre-processing parses `LWE.encodeChallenge (A, b)`
  (residues of L + 1 bits), re-encodes the residues at κ + 1 bits, and writes the sPRG challenge
  string of the hop: `b⁽ᵏ⁾ = A s⁽ᵏ⁾ + e⁽ᵏ⁾ + σ` for k after the hop, `b + σ` at the hop, hardwired
  `u⁽ᵏ⁾` before, then err = 0 and the tail. For L not of the form κ^E the advice is empty and the
  machine outputs a constant (no claim is made there). `NUPPT.wrap`
  (`Asymptotic/ReductionSupport.lean:148`, `runAt_wrap` :200) is the same-parameter form, for any
  hop that needs no re-indexing.
- **Mod-p arithmetic on encodings** (Q-S6 A): `A s mod p` by
  `Encoding.DyadicLinearAlgebra.matVecPoly` (`:342`, `matVecPoly_encodeMatrix` :395,
  `polyTimeComputable_matVecPoly` :445) at a width with no wrap-around
  (≥ 2·(κ+1) + log₂ ℓ + 1), followed per coordinate by `Complexity.BinArith.mod`
  (`Complexity/ClassP/BinaryArith/Div.lean:55`, `polyTimeComputable_mod` :245; endianness through
  `Encoding.BinaryArith.toLE`), and additions by `DyadicArithmetic.addPoly` + `mod`. The only host
  used is H16 (`Complexity.BinArith.forLoop`, via `matVecPoly`); any other host need is E-SCOPE.
- **PRG hop machine** (`Reductions/PRG.lean`): `NUPPT.exists_reparam_pre_post_adv`
  (`Asymptotic/UniversalLemmas.lean:125`) from the PRG parameter N to κ(N) (the κ with
  n κ = N, or 0; κ(N) ≤ N), advice ω* (A, φ, the u⁽ᵏ⁾); in the corollaries, negligibility moves
  along n κ ≥ κ by `Negligible.comp_of_le` (`Foundations/Negligible.lean:237`) and subexponential
  smallness by the API's re-indexing.
- **LPN in a ProbComp proof**: `Bridge.distAdv_eq` (`Games/Bridges/Experiments.lean:139`) turns
  `LWE.decisionAdvantage` into `advantage` of `acceptGame`s; `Family.encodeChallenge_length_le`
  bounds the input.
- Efficiency is proved: every pre-processing map is `PolyTimeComputable` (the pairing calculus,
  `takeLen_poly`/`dropLen_poly`, `polyTimeComputable_layout`), advice lengths are bounded by a
  `PolyExpr`.

## 5. Milestones

Each milestone ends with a commit on `fill/io-sprg` and a push of the payload to
`inbox/fills/io-sprg/` (checkpoint), so a stalled run leaves a reviewable prefix. M1–M3 are
independent and may be reordered; M4 needs M1 and M3; M5 needs all.

| M | Content | Exit criterion | Lines (cum.) |
|---|---|---|---|
| **M0** statements | every file of §2.2 with module docstring; **every definition final** (LPN, BoolPRG, degree notions, SPRG and its predicates, Params and derived quantities, buckets, sparse factor, polynomials, laws, `jlsSPRG`, games and hybrids) with its readers proved (`rfl`/`simps`); **every theorem stated with `sorry`** under its `**Proof sketch.**`; reductions as ∃-statements; the fidelity table (each statement → page, item, deviations) in REPORT | all modules elaborate (rc 0, 0 errors), `sorry` only in the listed theorems; coe-A seals and controls on the definitions; lint; StmtDump | 1,800–2,600 |
| **M1** algebra | degree closure lemmas, buckets, sparse factor, G⁽¹⁾–G⁽⁴⁾ evaluation and degrees, `G4_eval_eq`, `jls_hasComplexity`, `lpnNoise_law` | listed theorems sorry-free, standard axioms | +800–1,400 |
| **M2** stretch | `jls_seedBits_le`, `jls_hasPolyStretch` (confirm C10) | same | +250–450 |
| **M3** Claim 4.2 | Markov step, balls-in-bins, binomial bound, independence over k, side conditions, `claim42` | same | +600–1,000 |
| **M4** hybrids | games, statistical hops, encodings, mod-p machines, LPN and PRG machines with run lemmas and efficiency, `lemma42`, `prop41` | same | +1,100–2,000 |
| **M5** Theorem 4.1 | `jls_secure`, `jls_subexpSecure`, `theorem41`, `theorem41_subexp`, `exists_sprg`, `exists_sprg_subexp`, through the Foundations/Subexponential API | **0 `sorry`** in the job; full evidence | +200–400 |
| **Total** | | | **4,750–7,900** |

## 6. Proof sketches the statements must carry (M0)

- `claim42`: the paper's three conditions; Cond₁: E|BAD⁽ᵏ⁾| ≤ cLoc·m/W (union over the ≤ cLoc
  variables, Pr[e_i ≠ 0] ≤ 1/W), Markov ⇒ Pr ≤ cLoc / log₂ n; Cond₂ given ¬Cond₁: φ_bkt is
  independent of e⁽ᵏ⁾, a fixed bucket gets t + 1 of the ≤ Γ ≤ B bad outputs with probability
  ≤ C(Γ, t+1)/B^{t+1} ≤ (e/(t+1))^{t+1} ≤ e^{−κ}, union over B; Cond₃: ≤ C(m, cap+1)/B^{cap+1}
  ≤ (e/t³)^{cap+1} ≤ κ^{−2κ²}; Pr[err] ≤ Pr[Cond₃] + Σ_k Pr[Cond₂⁽ᵏ⁾ ∧ ¬Cond₁⁽ᵏ⁾] +
  Π_k Pr[Cond₁⁽ᵏ⁾] (the instances' noises are independent), then ≤ 2^{−κ} for κ ≥ κ₀ (C9).
- `lemma42`/`prop41`: §4.8; the corollaries: §4.7 *Corollaries*; `jls_hasComplexity`: G⁽⁴⁾ with
  `G4_eval_eq` and the degree lemmas;
  `jls_seedBits_le`: count of §4.6 (κ·n + 1 public, κ·(1 + 2((ℓ+1)^D + 2·B·t·rc)) private
  residues of κ + 1 bits, B·t·rc ≤ (m t/W + 1)·t²·w).

## 7. Risks

1. **Elaboration cost of the polynomials** (sums over `Fin D → Fin (ℓ+1)` inside `MvPolynomial`).
   Keep them as definitions read through `_eq` lemmas; never `decide`/`simp` them open.
2. **Rule 10 across the job's own files**: each file is foreign to the others; every definition
   used downstream needs its reader at M0 (that is most of M0's proved content).
3. **Encodings of the hop machine** (M4) are the longest step; reuse the pairing calculus and
   `DyadicLinearAlgebra`, never hand-build a loop.
4. **Constants of Claim 4.2** (e^{−κ} vs 2^{−κ}): only "eventually" statements; do not chase
   explicit κ₀.
5. **Statement changes after M0**: allowed only as separate, disclosed commits (§ dispatch).

## 8. Disclosed deviations (docstrings must say each where it applies)

Dv1 single security parameter (C1). Dv2 seeds as ℤ_p vectors; bit length `seedBits`. Dv3 LPN via
`LWE.Family`, indexed by its dimension ℓ: transposed orientation; one schedule (η_n = D,
η_p = 1/E); rate 1/W ≥ ℓ^{−δ} (C6); residue width ℓ + 1 (C11). Dv4 PRG security
in its seed length; representation and locality for every index of the index type; locality on
the representation. Dv5 `HasStretch` as m ≥ n^τ. Dv6 Def 3.3 for ℂ = degree-d polynomials,
composite form; no efficiency contracts (S2, Q-S3). Dv7 Claim 4.2 for κ ≥ κ₀. Dv8 Lemma 4.2 with
φ included; quantitative forms with machines. Dv9 p a (κ+1)-bit prime (C2). Dv10 degree d, not
p. 14's d + 1 (S3). Dv11 d ≥ 1. Dv12 reductions hardwire averaged values in their advice (§4.8).
Dv13 subexponential security is advantage 2^{−κ^c} against non-uniform PPT (Def 2.1; S7, S9),
through the Foundations/Subexponential API; subexponential-time adversaries are not covered.

## 9. Open questions for Seyoon (multiple choice, recommended option first)

★ = where Seyoon's high-level vision matters most: these fix what the later FE ⇒ iO bootstrapping
([JLS26, Theorem 5.1]) can consume.

- **★ Q-S1. The LPN hypothesis of Theorem 4.1.** (The family is indexed by its dimension ℓ either
  way, per S8.)
  (A) LPN (negligible, or subexponential through the API) for the construction's own family C11
  (n = ℓ^D samples, p(ℓ) from the prime schedule, rate 1/W), defined through an LPN-shaped
  `LWE.Family` (§4.1): the weakest hypothesis, maximal reuse; `exists_sprg(_subexp)` assume it
  for every E. A literal Def 2.3 predicate (∀ η_p, ∀ p(ℓ), ∀ η_n, rate exactly ℓ^{−δ}) with the
  bridge "Def 2.3 ⇒ family form" (raising the rate by hardwired extra noise, transposition) is a
  later small job. (B) The same, with the literal Def 2.3 predicate and its bridge inside this job
  (+400–700 lines, after M5). (C) A native LPN game in the paper's orientation, not through `LWE`
  (duplicates the LWE experiment shape; needs Seyoon's approval as debt).
- **★ Q-S2. The modulus.** (A) A deterministic prime schedule p(κ), as Def 3.3 says ("p = p(λ) …
  an efficiently computable function in λ"); the bootstrapping then needs a group generator of that
  same order. (B) p sampled with the index (part of `Idx`), so the sPRG can follow a group
  generator's random order; every statement becomes per-index, and the LPN family must then range
  over random moduli.
- **★ Q-S3. Efficiency of the sPRG's algorithms.** (A) Assert none in this job (as `LWE.Family`):
  IdSamp/SdSamp are laws (S2), Eval and "Q_I efficiently generated" are docstring disclaimers, all
  deferred with the sampler bridge. (B) Prove `eval'` polynomial-time on encodings now (a machine
  evaluating G⁽⁴⁾ over ℤ_p from BinArith; +1,500–3,000 lines) and keep the samplers deferred.
  (C) Also a machine producing an encoding of Q_I from I.
- **★ Q-S4. Definition 3.3's complexity class.** (A) Only ℂ = degree-d polynomials, in composite
  form (one polynomial over public ⊕ private variables, public degree ≤ d, private degree ≤ 2),
  which is what Theorem 5.1 consumes. (B) General ℂ as a predicate on Process_I with Q_I linear in
  P̄, plus the degree-d instance and its equivalence with (A).
- **Q-S5. Where the code lives.** (A) New area `TCSlib/Cryptography/Obfuscation/StructuredSeed/`,
  one line in `TCSlib.lean` (§2.1). (B) `TCSlib/Cryptography/Pseudorandom/StructuredSeed/`, one
  import line plus a `## Contents` bullet in `Pseudorandom.lean` (an S2-B area facade; needs a
  scope exception for the second edit). (C) Split: `Cryptography/LPN/` beside `LWE/` and the sPRG
  under `Obfuscation/` (two root lines).
- **Q-S6. Arithmetic in the reduction machines.** (A) From proved machines only
  (`DyadicLinearAlgebra.matVecPoly` at a non-wrapping width, then `Complexity.BinArith.mod`); no new
  hypothesis on Theorem 4.1. (B) Take `Candidates.ArithmeticFP` as a hypothesis (the
  `bb1_sidSecure` precedent); shorter M4.
- *(Q-S7, the subexponential clause, is withdrawn: settled by Seyoon's ruling of records
  `a2bf4bac`, S7–S9.)*
- **Q-S8. Statements-gate repairs while the job runs.** (A) Codex continues after checkpoint 0;
  if the statements gate finds majors, Seyoon pastes the repair list into the running chat and
  Codex applies it as disclosed statement-change commits. (B) Codex pauses after M0 until the gate
  closes.
