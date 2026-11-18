# io-sprg design r2: the structured-seed PRG of [JLS26, §2–§4, Theorem 4.1], Phase A

**Status.** Design note for the end-to-end Codex job `io-sprg`, **Phase A** (campaign
`IOComponentsPlan.md`). The Codex prompt (`dispatch-prompt-r2.md`) points here. r2 supersedes
`design-r1.md` wherever they differ. Sections marked *unchanged from r1* are read in `design-r1.md`
and are binding as written there, with the substitutions of §0.1 below. Everything marked
**proposed** is a starting shape: Codex may refine it **with disclosure** (REPORT.md § *Deviations
from the design note*), never silently. The settled points (§0) and Seyoon's answers to the open
questions (§10.2, once ruled, in `rulings.md`) are binding.

| Pin | Value |
|---|---|
| Rulings | every decision-log row dated 2026-11-18 in `IOComponentsPlan.md`, read at records `dab31951abb5c892dc6279c229e49497ec95de10`; the rows used are named in §0 and §10.1 by their bold title |
| Lean base | `<BASE>`: the head of branch `foundations/subexp` (draft PR #374, `cbce64d1c135c710b7c036968ed9d4f21414aa72`), or a later head stacked on it (e.g. with the shared realisation file of Q-S9 A) |
| Base tree | `git diff --stat 0fec25892 cbce64d1c -- TCSlib` lists only `Foundations/Subexponential.lean` (+300) and `Foundations.lean` (+3): every other file:line of r1 and of the sweep is valid at `cbce64d1` |
| Source | [JLS26] PDF, 30 pages, SHA-256 `bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d`, CC BY 4.0; PDF page *k* is article page 1:*k* |
| Content read for r2 | pp. 9–11 (Def 2.3, Defs 3.1–3.4, Theorem 4.1) and pp. 15–17 (the construction, 1SdSamp, G⁽³⁾/G⁽⁴⁾), re-read for the public-parameter and efficiency wording; r1 read pp. 8–21 |

## What changed from r1

1. **Two phases** (row *Strategy and uniformity*). This job is Phase A: honest algorithms and
   reductions are explicit Lean functions; correctness, stretch, Claim 4.2; security as explicit
   advantage inequalities for **every NUPPT that realises** each reduction function; efficiency
   statements are written (as named propositions), not proved. r1's M4 machine construction
   (`DyadicLinearAlgebra.matVecPoly`, `Complexity.BinArith.mod`, the H16 loop, the hop machines
   and their `PolyTimeComputable` proofs, `Reductions/Encode.lean`) is **removed**; it moves to
   Phase B (§9), which works through word-RAM programs. Phase A commits to no RAM interface.
2. **p is an input** (rows *sPRG rulings* Q-S2, *Strategy and uniformity* (3)). `Params` no
   longer carries a prime schedule. Every honest algorithm of the construction is defined for an
   arbitrary public parameter `pp : PrimeParam κ` (a prime with its primality and width proofs,
   §4.1); a schedule `π : PrimeSchedule` only assembles the family `jlsSPRG P π`; every theorem is
   `∀ π`. The public parameter is part of every challenge string and of every efficiency
   statement's input; no definition computes or hard-wires p.
3. **Uniformity** (row *Strategy and uniformity* (2)). Efficiency of honest algorithms is written
   only as `PolyTimeComputable` of **one** string map, quantified **before** κ and before the public
   parameter (§4.10); never a bare `∃ A : NUPPT, A.Computes f`. Advice appears only in reductions,
   only as their input.
4. **Subexponential API with its real names** (row *`Foundations/Subexponential.lean` written*):
   `SubexpSmall`, `SubexpHard` (any adversary type), `.negligible`, `.add`/`.const_mul`/`.mul_pow`
   (to any `c' < c`, `0 < c`), `.mono`, `.mono_exponent`, `.comp_of_rpow_le`,
   `SubexpHard.comp_of_rpow_le`, `eventually_const_mul_rpow_mul_two_rpow_neg_le`,
   `subexpSmall_two_pow_neg`. The working names of r1 are retired.
5. **The core theorem holds for every κ**, with the slack `2 · errProb κ (π κ)` written as an
   explicit function; Claim 4.2 (uniform in the prime) bounds it by `2 · 2^{-κ}` eventually. Both
   corollaries (negligible, subexponential with an explicit exponent) are derived from it.
6. **Settled questions.** Q-S1, Q-S2, Q-S4, Q-S5, Q-S8 are ruled; Q-S3 and Q-S6 are superseded;
   Q-S7 was withdrawn in r1 (§10.1). Four new questions remain (Q-S9–Q-S12, §10.2).
7. Smaller changes: the width condition is `2^κ ≤ p ≤ 2^(κ+1)` (C2: exactly the (κ+1)-bit primes
   for κ ≥ 1, and p = 2 at κ = 0, so a schedule exists); the generic `SPRG` has `Fin`-indexed
   seeds (C13); the samplers are written as a named deterministic core applied to exact uniform
   draws (C14), the shape the in-house sampler bridge consumes.

## 0. Settled points (binding)

### 0.1 Kept from r1 (design-r1 §0), with r2 substitutions

- **S1 Rounding** (row *sPRG design inputs* (1)): convention §3. Unchanged except C2, C11 (§3).
- **S2 Sampling** (rows *sPRG design inputs* (2), *Efficiency rulings* (1), *Sampler-bridge
  rulings*). Non-dyadic laws are **exact finite distributions** (`Games.ProbComp.sample` of finite
  types and pushforwards, the `LWE.Family`/`LWE.Noise` convention). The sampler bridge is built
  in-house, separately (`briefs/io-components/sampler-bridge/`, future area
  `TCSlib/Cryptography/CoinSampling/` and `Games/Closeness.lean`). **The job must not build one**,
  must not approximate samplers (`rejectionSample`, `StatClose`, `LWE.sampleFromBits`,
  `Encoding.DyadicUniform.*`, `uniformFromBits`), and must not import `CoinSampling` or
  `Games.Closeness` even if a later `<BASE>` carries them.
- **S3 Degree d, not d + 1** (row *sPRG design inputs* (3)): unchanged.
- **S4 Adversaries and assumptions**: non-uniform PPT (`Complexity.NUPPT`, [PS10, Def 26.8]);
  assumptions and security are "every NUPPT has negligible (or `SubexpHard`) advantage". r1's
  "every reduction is a machine construction with its efficiency proved" is **replaced** by S10.
- **S5 Independence**: new files only, under `TCSlib/Cryptography/Obfuscation/` (Q-S5, ruled),
  plus the one line `import TCSlib.Cryptography.Obfuscation` in `TCSlib.lean`; no existing file
  is edited. Stage 2 coordination: design-r1 §2.4, unchanged.
- **S6 Out of scope**: as r1 (FE ⇒ iO, bilateral DLIN/LWE, NC⁰ candidates, OWF ⇒ PRG, the link to
  `Pseudorandom/Generators/Asymptotic/Defs`), **plus** everything of Phase B (§9): word-RAM
  programs, efficiency proofs, the RAM bridge, the sampler bridge, the randomised prime-sampler
  bridge, and the literal Def 2.3 bridge (Q-S1).
- **S7 Subexponential security** (rows *Subexponential security*, *`Foundations/Subexponential.lean`
  written*): only through `TCSlib/Cryptography/Foundations/Subexponential.lean` at `<BASE>`,
  namespace `TCSlib.Cryptography`, with the names of item 4 above. No subexponential notion of the
  job's own; a named wrapper (e.g. `SPRG.SubexpSecure`) only as a one-line definition whose body is
  `SubexpHard S.adv`, with its `_iff` reader.
- **S8 Explicit slack**: the core theorem is an explicit inequality (§4.9), LPN advantage in its
  own dimension ℓ, PRG advantage in its seed length n; both corollaries derived from it.
- **S9** Subexponential-*time* adversaries are out of scope.

### 0.2 New in r2

- **S10 Two phases** (row *Strategy and uniformity* (1)). Phase A (this job): (i) honest
  algorithms as explicit Lean functions (samplers as exact laws, S2); (ii) each reduction as an
  explicit Lean function of its input, its advice and its coins (§4.8); (iii) correctness, stretch
  (Claim 4.1), Claim 4.2; (iv) security as explicit advantage inequalities stated for **any
  non-uniform PPT machine that realises each reduction function** (§4.8, §4.9); (v) efficiency
  statements written as named propositions, not proved (§4.10). Phase B (later, not this job):
  word-RAM programs, their correctness and step bounds, the RAM ⇒ `PolyTimeComputable`/NUPPT bridge
  (`briefs/io-components/ram-bridge-assessment.md`), and the final "∃ NUPPT B" theorems.
- **S11 Uniformity** (row *Strategy and uniformity* (2), binding). Honest algorithms' efficiency,
  when stated, is `PolyTimeComputable f` of one map `f`, or `∃ A, A.Uniform ∧ A.Computes f`; never
  a bare `∃ A : NUPPT, A.Computes f`. One algorithm for all κ (κ read from `1^κ`), no per-κ
  constants (no hard-wired prime), so `f` is quantified before κ and before the public parameter.
  Advice only for reductions (and adversaries), and only as input.
- **S12 p as an input** (rows *sPRG rulings* Q-S2, *Strategy and uniformity* (3), *Sampler-bridge
  rulings* Q10). The prime is part of the public parameters: an input of `IdSamp′`, `SdSamp′`,
  `Eval′` and of every reduction (in its advice), and visible to the adversary in the challenge.
  Statements hold **for every prime schedule** `π` of (κ+1)-bit primes (C2). No honest algorithm
  computes p (no deterministic poly(κ)-time generation of κ-bit primes is known;
  `BinaryArith/PrimeFind` covers only O(log n)-bit primes from unary input) or hard-wires it. A
  randomised prime-sampler bridge supplies p later (§ *Deferred library work*); the honest
  algorithms do not deal with it.

## 1. Source map (paper → Lean, proposed names)

Namespace root `TCSlib.Cryptography.Obfuscation.StructuredSeed` (below `SS.`). The paper's λ is `κ`.

| Paper | Page | Lean (proposed) | File | M |
|---|---|---|---|---|
| Def 2.1, Remark 2.1 | 8–9 | `Games.advantage`, `Negligible`; `SubexpSmall`, `SubexpHard` (no new definition) | — | — |
| "a λ bit prime" (p. 15), "p = p(λ)" (Def 3.3) | 10, 15 | `SS.PrimeParam κ`, `SS.PrimeSchedule`, `PrimeParam.enc`, `PrimeSchedule.nonempty` (§4.1) | `Defs` | 0 |
| 𝒟_r(p) | 9 | `SS.lpnNoise p W`, `lpnNoise_law` | `LPN` | 0/1 |
| Def 2.3 (δ-LPN_𝔽) | 9–10 | `SS.LPNFamily`, `toLWE`, `adv`, `Assumption`; the construction's family `P.lpnFamily π` (Q-S1, ruled) | `LPN`, `Params` | 0 |
| Def 3.1 | 10 | `SS.SPRG` (Fin-indexed seeds, C13) | `Defs` | 0 |
| Remarks 3.1–3.2 | 10 | `SPRG.seedBits`, `SPRG.HasPolyStretch` | `Defs` | 0 |
| Def 3.2 | 10 | `SPRG.encPP`, `SPRG.challengeStr` (p public), `SPRG.game`, `SPRG.adv`, `SPRG.Secure`; subexponential: `SubexpHard S.adv` | `Defs` | 0 |
| Def 3.3 (deg d, deg 2) | 10 | `SPRG.HasComplexity` (Q-S4, ruled); efficiency forms `SPRG.EvalEfficient`, `SPRG.HasComplexityEff` (§4.10) | `Defs`, `Degree`, `PolyTerms` | 0 |
| Def 3.4 | 11 | `SS.BoolPRG` and its predicates (design-r1 §4.2, unchanged) + `BoolPRG.EvalEfficient`, `MultilinearRep.TermsEfficient` (Phase B hypotheses) | `BoolPRG` | 0 |
| Construction: parameters | 15 | `SS.Params` (no prime, §4.6) and derived quantities (§3) | `Params` | 0 |
| IdSamp′ | 15 | `P.idSamp' κ pp`, `Buckets.indexMap` | `Samplers`, `Buckets` | 0/1 |
| 1SdSamp, SdSamp′, err, k* | 15–16 | `P.oneSd`, `P.Draw κ pp`, `P.sdCore`, `P.sdSampFull`, `P.sdSamp'` (C14) | `Samplers` | 0 |
| M_i = U_iV_i | 16 | `SS.sparseFactor`, `sparseFactor_mul` | `SparseFactor` | 0/1 |
| G⁽¹⁾–G⁽⁴⁾, Eval′ | 16–17 | `P.G1 … P.G4` at `pp`, `P.eval'` | `Polys`, `Samplers` | 0 |
| the family | 15–17 | `jlsSPRG P π : SPRG` | `Samplers` | 0 |
| "G⁽⁴⁾ = (1 − err)·y", (deg d, deg 2) | 16–17 | `G4_eval_eq`, `jls_hasComplexity` | `Correctness` | 1 |
| Claim 4.1 | 18 | `jls_seedBits_le`, `jls_hasPolyStretch` | `Stretch` | 2 |
| Claim 4.2 | 19–21 | `P.errProb κ pp`, `claim42` (uniform in `pp`) | `Claim42`, `Claim42/Load` | 3 |
| Lemma 4.2 | 19 | hybrids `P.hyb`, the reduction functions `P.lpnRed`, `P.prgRed`, hop lemmas | `Hybrids`, `Reductions/*` | 4 |
| Prop 4.1 | 18–19 | `prop41`: the core explicit inequality, for every realiser (§4.9) | `Security` | 4 |
| Theorem 4.1 | 11 | `jls_secure`, `jls_subexpSmall`, `jls_subexpSecure`, `theorem41`, `theorem41_subexp`, `exists_sprg`, `exists_sprg_subexp` (under realisability, §4.9) | `Security` | 5 |
| (efficiency, Phase B) | 10, 15–16 | targets `P.evalTarget`, `P.qGenTarget`, `P.coreTarget`, `P.lpnPreTarget`, `P.prgPreTarget`; `realizable_of_targets`, `theorem41_of_targets` (Q-S10, Q-S11) | `Targets` | 0/6 |

## 2. Module layout (Phase A)

### 2.1 Directory, namespaces, facades

As design-r1 §2.1 (Q-S5 ruled: option A). New area facade `TCSlib/Cryptography/Obfuscation.lean`,
child facade `Obfuscation/StructuredSeed.lean` (`## Contents`, one line per child), one import line
in `TCSlib.lean` after `import TCSlib.Cryptography.AdvancedEncryption`. Namespace
`TCSlib.Cryptography.Obfuscation.StructuredSeed`; helpers `private` or in `…StructuredSeed.Internal`;
nothing in the root namespace. The PHFE job does not create `Obfuscation.lean`.

### 2.2 Files and size plan (policy §1: target 150–600 lines, hard cap 1000)

| File (under `Obfuscation/StructuredSeed/`) | Content | Lines |
|---|---|---|
| `LPN.lean` | `lpnNoise`, `lpnNoise_law`, `LPNFamily`, `toLWE`, `adv`, `Assumption` + readers | 150–250 |
| `BoolPRG.lean` | design-r1 §4.2, plus the Phase B hypotheses `EvalEfficient`, `MultilinearRep.TermsEfficient` (definitions with readers only) | 200–340 |
| `Degree.lean` | `pubDegree`, `privDegree`; `weightedTotalDegree` closure lemmas (design-r1 §4.4) | 150–280 |
| `PolyTerms.lean` | `PolyTerms σ R`, `denote`, `encTerms` + readers (only if Q-S10 A) | 60–120 |
| `Defs.lean` | `PrimeParam`, `PrimeSchedule` (+ `nonempty`), `SPRG`, `encPP`, `encSeed`, `challengeStr`, `game`, `adv`, `Secure`, `HasComplexity`, `seedBits`, `HasPolyStretch`, `EvalEfficient`, `HasComplexityEff` | 280–450 |
| `Params.lean` | `Params` (no prime), derived quantities (§3), `κOf`, `κOfN` and readers, `lpnFamily π`, side conditions | 200–350 |
| `Buckets.lean` | `indexMap`, overfull test, injectivity within buckets | 200–320 |
| `SparseFactor.lean` | `sparseFactor`, `sparseFactor_mul` | 150–260 |
| `Polys.lean` | G⁽¹⁾–G⁽⁴⁾ at `pp` as `MvPolynomial`; renaming to `Fin` variables (C13); degree bounds | 350–550 |
| `Samplers.lean` | `idSamp'`, `Draw`, `oneSd`, `sdCore`, `sdSampFull`, `sdSamp'`, `eval'`, the encodings `encIdx'`/`encSeed'` with explicit equivalences, `jlsSPRG` | 330–500 |
| `Correctness.lean` | M1: good outputs, correction, G⁽³⁾, `G4_eval_eq`, `jls_hasComplexity` | 450–750 |
| `Stretch.lean` | M2: Claim 4.1 | 250–450 |
| `Claim42/Load.lean` | binomial bound, balls-in-bins tails, Markov step | 300–500 |
| `Claim42.lean` | `errProb`, Cond₁–Cond₃, independence over k, `claim42` | 300–500 |
| `Hybrids.lean` | H₀–H₃ and the hop hybrids at `pp`, statistical hops | 350–550 |
| `Realization.lean` | only if Q-S9 is not A at `<BASE>`: `RealizesOn` + readers + the verdict lemma | 0–150 |
| `Reductions/LPN.lean` | `LPNChal`, `lpnEnc`, `LPNAdvice`, `encLPNAdvice` (+ length bound), `lpnPre`, `lpnRed`; hop lemma | 250–450 |
| `Reductions/PRG.lean` | `PRGChal`, `prgEnc`, `PRGAdvice`, `encPRGAdvice`, `prgPre`, `prgRed`; hop lemma | 120–250 |
| `Security.lean` | `prop41`, realisability propositions, `jls_secure`, `jls_subexpSmall`, `jls_subexpSecure`, `theorem41`, `theorem41_subexp`, `exists_sprg`, `exists_sprg_subexp` | 220–400 |
| `Targets.lean` | the efficiency targets (§4.10) and, with Q-S11 A, `realizable_of_targets`, `evalEfficient_of_target`, `theorem41_of_targets` | 220–400 |
| `../StructuredSeed.lean`, `../../Obfuscation.lean` | facades | 70–100 |
| **Total** | 20 modules + 2 facades (19 modules without `Realization.lean`) | **≈ 4,600–7,900** (central ≈ 6,000) |

**Size compared with r1 (4,700–7,900).** About the same total, much lower risk. Leaving: the machine
construction of r1 M4 (`Reductions/Encode.lean`, the hop machines' run and efficiency lemmas, the
mod-p arithmetic on encodings: ≈ 800–1,450 lines). Coming in: `PolyTerms`, the realisation layer,
the canonical encodings of index and seeds (needed so the targets are statable), the target
statements and the link through `NUPPT.exists_reparam_pre_post` (≈ 600–1,200 lines). M4 shrinks
from 1,100–2,000 to 650–1,200. Split a file before ~900 lines; never merge files to save headers.

### 2.3 Imports (precise, no `import Mathlib`)

As design-r1 §2.3, **minus** the Phase B modules `Encoding.DyadicLinearAlgebra`,
`Encoding.DyadicArithmetic`, `Encoding.BinaryArith`, `Complexity.ClassP.BinaryArith.*`; **plus**
`Foundations.Subexponential` (S7) and, if Q-S9 A, the shared realisation module. Keep
`Asymptotic.UniversalLemmas` (for `NUPPT.exists_reparam_pre_post`, Q-S11 A), `Encoding.Modular`,
`Candidates.Arithmetic` (`natToList`), `LWE.Assumption`. Mathlib adds `Logic.Equiv.Fin.Basic`
(`finSumFinEquiv`, `finProdFinEquiv`) and `Algebra.BigOperators.Fin` (`finFunctionFinEquiv`). **Do not import** anything under
`TCSlib/Programs/` or `TCSlib/Complexity/RAMSimulation/` (no RAM interface in Phase A), nor the
modules of design-r1 §2.3 *Do not import*, nor `CoinSampling`/`Games.Closeness` (S2).

### 2.4 Stage 2 crossings

Unchanged from design-r1 §2.4 (the base adds only `Foundations/Subexponential.lean`, which is not in
`scope.tsv`); the `DyadicUniform` row no longer applies. Every touch the job sees is additive or
proof-level.

## 3. Conventions

C1, C3–C10 **unchanged from design-r1 §3**. Changed or new:

| # | Quantity | Convention (r2) | Why |
|---|---|---|---|
| C2 | p | the public parameter `pp : PrimeParam κ` (§4.1): `pp.p` prime with `2 ^ κ ≤ pp.p ≤ 2 ^ (κ + 1)`; residue width `κ + 1`; `p` itself on the wire in `κ + 2` bits (`PrimeParam.enc`) | For κ ≥ 1 this is exactly "a (κ+1)-bit prime" (2^κ and 2^(κ+1) are prime only for κ = 0, 1, and 2 = 2^1 is a 2-bit prime), the paper's "λ-bit prime" with λ = κ + 1. At κ = 0 no 1-bit prime exists and the condition admits p = 2, so `PrimeSchedule` is inhabited (Bertrand), which keeps every `∀ π` statement non-vacuous. Residues are `< p ≤ 2^(κ+1)`, so they fit in κ + 1 bits; p = 2^(κ+1) happens only at κ = 0, hence κ + 2 bits for p itself. r1 had `2 ^ κ < p`; the change admits p = 2 at κ = 1 and is disclosed. Security never uses the lower bound; Claim 4.1 uses the width. |
| C11 | the LPN family | `P.lpnFamily π`, indexed by its own dimension ℓ (Def 2.3's index): at every ℓ, `κOf ℓ := Nat.findGreatest (· ^ E ≤ ℓ) ℓ`, `samples ℓ := ℓ ^ D`, `modulus ℓ := (π (κOf ℓ)).p`, `noiseDen ℓ := (max 1 ⌊ℓ^{δ/2}⌋₊) ^ 2`, residue width `ℓ + 1` | as r1 C11, with the schedule `π` in place of r1's `p`; at ℓ = κ^E every value equals the sPRG's at `π κ` (`κOf (κ ^ E) = κ`, a reader). |
| C12 | public parameter on the wire | every challenge string handed to an sPRG adversary starts with the encoding of the public parameter (`SPRG.encPP κ`); every efficiency statement's input carries it (`PrimeParam.enc`); every reduction carries it in its advice encoding | S12: p is public and an input, never computed. With a fixed schedule a non-uniform adversary could hold p anyway, so publishing it costs nothing. |
| C13 | encoded index types | everything that is encoded for a machine (seeds, index, advice) is indexed by a `Fin k`, or carries an **explicit** equivalence to one, built from `finSumFinEquiv`, `finProdFinEquiv`, `finFunctionFinEquiv`, `Equiv.sumCongr`, `Equiv.prodCongr`; **never `Fintype.equivFin`** or another classical choice | an encoding through a classical enumeration is not a fixed function of the data, so its efficiency target would be unprovable in Phase B. The generic `SPRG` therefore has seeds `Fin (pubLen κ) → ℤ_p` and `Fin (privLen κ) → ℤ_p`; the construction's structured private seed (r1 §4.6: `Fin κ × (Unit ⊕ SVar ⊕ SVar)`) is transported by an explicit `privEquiv`, and its polynomials renamed along it (`MvPolynomial.rename`; degrees by `weightedTotalDegree_rename_of_injective`). |
| C14 | sampler shape | every honest sampler is `core <$> (exact uniform draws)`: `idSamp' κ pp := (G.idSamp (n κ)) ×ˢ sample (Fin m → Fin B) ×ˢ sample (Matrix (Fin n) (Fin ℓ) (ZMod pp.p))` (the index is the draw itself; φ_ind is derived by `indexMap`), and `sdSamp' κ pp I' := (fun x => (P.sdCore κ pp I' x).seed) <$> sample (P.Draw κ pp)` with `Draw κ pp := (Fin n → Bool) × (Fin κ → (Fin ℓ → ZMod pp.p) × (Fin n → Fin W × ZMod pp.p))` | the in-house sampler bridge (row *Sampler-bridge rulings*) replaces the exact draws by coin samplers and feeds the same deterministic core; `HasComplexity` (an `AllOutputs` predicate) then transfers exactly. The core's efficiency is a Phase B target (T3). |

## 4. Statement shapes (proposed; Codex may refine with disclosure)

Lean-like; universes `Type`; every public definition lands with its readers (`simps (config :=
{ isSimp := false })`, `_eq` by `rfl`, `_iff`); no `@[simp]`.

### 4.1 How p enters: the public parameter

```lean
/-- A public parameter of the construction at security parameter `κ` [JLS26, §4, p. 15: "modulus
p, which is a λ bit prime"; Definition 3.3, p. 10, "p = p(λ)"]: a prime `p` with
`2^κ ≤ p ≤ 2^(κ+1)` (a (κ+1)-bit prime for κ ≥ 1, and p = 2 at κ = 0). It is an INPUT of every
honest algorithm and is published to the adversary; no algorithm computes it (Deviation Dv9). -/
structure PrimeParam (κ : ℕ) where
  p : ℕ
  prime : p.Prime
  two_pow_le : 2 ^ κ ≤ p
  le_two_pow : p ≤ 2 ^ (κ + 1)

/-- `Fact p.Prime` for `ZMod pp.p` as a field (a `def` used with `haveI`, or a scoped instance). -/
theorem PrimeParam.fact (pp : PrimeParam κ) : Fact pp.p.Prime := ⟨pp.prime⟩

/-- The public parameter on the wire: `p` in `κ + 2` big-endian bits (C2). -/
def PrimeParam.enc (pp : PrimeParam κ) : List Bool := Candidates.natToList (κ + 2) pp.p

/-- A prime schedule [JLS26, Definition 3.3] (Q-S2): one public parameter per κ. Not assumed
computable; every theorem about the construction holds for every schedule. -/
abbrev PrimeSchedule : Type := (κ : ℕ) → PrimeParam κ

/-- Non-vacuity: a schedule exists (Bertrand, `Nat.exists_prime_lt_and_le_two_mul`). Existence
only: no algorithm uses this choice. -/
theorem PrimeSchedule.nonempty : Nonempty PrimeSchedule
```

How it flows:
- **Honest algorithms** take `pp` explicitly: `P.idSamp' κ pp`, `P.sdCore κ pp I' x`,
  `P.sdSamp' κ pp I'`, `P.G1 … P.G4 κ pp I' j`, `P.eval' κ pp I' sd`. `Params` has no prime field
  and no definition reads a schedule.
- **The family** `jlsSPRG P π : SPRG` sets `modulus κ := (π κ).p` and runs the algorithms at `π κ`.
- **Statements**: correctness, stretch and Claim 4.2 are stated `∀ κ (pp : PrimeParam κ)` (Claim 4.2
  with κ₀ independent of `pp`); security is stated `∀ π`.
- **Efficiency targets** (§4.10) quantify one string map `f` **before** κ and `pp`, and pass
  `pp.enc` in `f`'s input; the reduction targets pass it in the advice encoding.
- **The adversary** sees `encPP` first in every challenge (C12).
- **Alternative (Q-S12 B)**: the generic `SPRG` also takes the public parameter as input, with
  security quantified over schedules inside the predicate. Not recommended (§10.2).

### 4.2 LPN over 𝔽_p (Def 2.3), as an LWE family

Unchanged from design-r1 §4.1 (`lpnNoise`, `lpnNoise_law`, `LPNFamily` with its fields, `toLWE`,
`adv`, `Assumption`, `assumption_iff`; docstring deviations (i)–(iv)). The construction's family is
`P.lpnFamily π` (C11); for `exists_sprg`, `lpnFamilyOf d δ E π`. Subexponential hardness in the
dimension is `SubexpHard (P.lpnFamily π).adv` (S7). Q-S1 is ruled (option A): the literal Def 2.3
predicate and its bridge come later, not in this job.

### 4.3 Boolean PRG (Def 3.4)

Unchanged from design-r1 §4.2. Added (definitions with readers; hypotheses of Phase B theorems only;
the job proves nothing about them):

```lean
/-- `G.Eval` is efficient, uniformly: one polynomial-time map computes `Eval_I(σ)` from
`⟨1^n, ⟨encIdx I, σ⟩⟩` for every `n` [JLS26, Definition 3.4 via Definition 3.1, "PPT"]. -/
def BoolPRG.EvalEfficient (G : BoolPRG) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∀ n I (σ : Fin n → Bool),
    f (NUPPT.advInput n (pairEncode (G.encIdx n I) (List.ofFn σ))) = List.ofFn (G.eval n I σ)

/-- The multilinear representation is efficiently generated: one polynomial-time map outputs, for
every `n`, index `I` and output `j`, a term list denoting `R.poly n I j` (any term list; no
canonical form is required). -/
def BoolPRG.MultilinearRep.TermsEfficient {G d} (R : G.MultilinearRep d) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∀ n I (j : Fin (G.outLen n)),
    ∃ ts : PolyTerms (Fin n) ℤ, f (NUPPT.advInput n (pairEncode (G.encIdx n I) (encFin j))) =
      encTerms encInt encFin ts ∧ denote ts = R.poly n I j
```

### 4.4 sPRG syntax, security, complexity (Defs 3.1–3.3)

As design-r1 §4.3, with C12 and C13:

```lean
structure SPRG where
  modulus : ℕ → ℕ
  modulus_prime : ∀ κ, (modulus κ).Prime
  residueBits : PolyExpr
  modulus_le_pow : ∀ κ, modulus κ ≤ 2 ^ residueBits.eval κ
  Idx : ℕ → Type  [Fintype, Nonempty]
  idSamp : (κ : ℕ) → ProbComp (Idx κ)
  encIdx : (κ : ℕ) → Idx κ → List Bool;  idxBits : PolyExpr;  encIdx_length_le : …
  pubLen privLen outLen : ℕ → ℕ;  seedBound outBound : PolyExpr;  … bounds …
  sdSamp : (κ : ℕ) → Idx κ →
    ProbComp ((Fin (pubLen κ) → ZMod (modulus κ)) × (Fin (privLen κ) → ZMod (modulus κ)))
  eval : (κ : ℕ) → Idx κ →
    (Fin (pubLen κ) → ZMod (modulus κ)) × (Fin (privLen κ) → ZMod (modulus κ)) →
      Fin (outLen κ) → Bool

/-- The public parameter on the wire: `modulus κ` in `residueBits κ + 1` bits (C2, C12). -/
def SPRG.encPP (S : SPRG) (κ : ℕ) : List Bool :=
  Candidates.natToList (S.residueBits.eval κ + 1) (S.modulus κ)
/-- `⟨pp, ⟨I, ⟨P, z⟩⟩⟩` [JLS26, Definition 3.2], with the public parameter first (C12). -/
def SPRG.challengeStr (S : SPRG) (κ) (I) (P) (z) : List Bool :=
  pairEncode (S.encPP κ) (pairEncode (S.encIdx κ I)
    (pairEncode (Encoding.Modular.encodeVector (S.residueBits.eval κ) P) (List.ofFn z)))
/-- The whole seed on the wire (both parts at `residueBits κ` bits per residue). -/
def SPRG.encSeed (S : SPRG) (κ) (sd) : List Bool := pairEncode (encodeVector … sd.1) (encodeVector … sd.2)
-- `game`, `adv`, `Secure`, `seedBits`, `HasPolyStretch`: as design-r1 §4.3
-- `HasComplexity S dPub dPriv`: as r1, over `MvPolynomial (Fin (pubLen κ) ⊕ Fin (privLen κ)) (ZMod _)`

/-- Eval is efficient, uniformly (S11): one polynomial-time map, reading `κ` from `1^κ` and the
modulus from its input. -/
def SPRG.EvalEfficient (S : SPRG) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧ ∀ κ I sd,
    f (NUPPT.advInput κ (pairEncode (S.encPP κ) (pairEncode (S.encIdx κ I) (S.encSeed κ sd)))) =
      List.ofFn (S.eval κ I sd)

/-- Definition 3.3 with "Q_I efficiently generated from I" (Q-S4 class; efficiency form): one
polynomial-time map outputs, from `⟨1^κ, ⟨pp, ⟨I, j⟩⟩⟩`, a term list whose denotation has public
degree ≤ dPub, private degree ≤ dPriv, and computes `Eval` on every seed `SdSamp(I)` can output. -/
def SPRG.HasComplexityEff (S : SPRG) (dPub dPriv : ℕ) : Prop := …   -- implies `HasComplexity`
theorem SPRG.HasComplexityEff.hasComplexity …
```

Docstring deviations: as r1 Dv1, Dv2, Dv6, plus Dv9 (p public and an input, not "an efficiently
computable function of λ") and Dv14 (no sampler efficiency predicate: the samplers' efficiency
comes with the sampler bridge).

### 4.5 Degree notions

Unchanged from design-r1 §4.4.

### 4.6 Parameters

```lean
structure Params where
  d : ℕ;  one_le_d : 1 ≤ d
  δ : ℝ;  δ_pos : 0 < δ;  δ_lt_one : δ < 1
  E : ℕ;  one_le_E : 1 ≤ E
  G : BoolPRG;  R : G.MultilinearRep d
-- no prime: the prime is an input (§4.1)
-- derived, each with an `_eq` reader: D ℓ n m w W t rc cap B Γ (§3), κOf, κOfN
-- readers: κOf_pow : κOf (κ ^ E) = κ; κOf_le : κOf L ≤ L; κOfN_n : κOfN (n κ) = κ; κOfN_le
-- lpnFamily (π : PrimeSchedule) : LPNFamily   (C11)
-- side conditions (M0 statements, M3 proofs): Γ_le_B, le_log_n, le_n (as design-r1 §4.5)
```

### 4.7 The construction (pp-parametrised)

As design-r1 §4.6, with every definition taking `(κ : ℕ) (pp : PrimeParam κ)` and `ZMod pp.p` in
place of `ZMod (p κ)`, and with C13–C14:
- `Idx' κ pp := G.Idx (n κ) × (Fin (m κ) → Fin (B κ)) × Matrix (Fin (n κ)) (Fin (ℓ κ)) (ZMod pp.p)`.
- `oneSd`, `badSet`, `errSet`, `corr`, `bucketMatrix`, `sparseFactor`: as r1, at `pp`.
- `sdCore κ pp I' (x : Draw κ pp)`: the deterministic part of SdSamp′ (the κ runs of `oneSd`, err,
  k*, zeroed flags, P′, S′, the private seed transported by `privEquiv`); `sdSampFull` returns the
  draw and the core's output (the hybrids need both); `sdSamp'` its seed.
- `G1 … G4 κ pp I' j`: as r1, built over the structured variables, then renamed to
  `Fin (pubLen κ) ⊕ Fin (privLen κ)` (C13). `eval' κ pp I' sd j := decide (eval … (G4 …) = 1)`.
- Encodings: `encIdx' κ pp I'` (`G.encIdx` of I, then φ_bkt as fixed-width numerals, then
  `encodeMatrix (κ + 1) A`), with a `PolyExpr` length bound.
- `jlsSPRG P π : SPRG` with modulus `fun κ => (π κ).p`, `residueBits := .add .var (.const 1)`, and
  the algorithms above at `π κ`.

### 4.8 Reductions as functions; realisation

**The non-uniform hardwiring route** (design-r1 §4.8, first two bullets) is unchanged: every hop
averages out everything but the challenged coordinate and fixes the best value ω* in the reduction's
**advice**; the hop index is chosen by advice (option (a), recommended; (b) allowed with disclosure).
The advantage is an absolute value (`Games.advantage`), so no sign bit is needed. The reductions
never sample.

**Shape of every reduction function (binding: it is the interface Phase B must meet).** A reduction
`X ∈ {lpn, prg}` consists of
- a parameter map `φX : ℕ → ℕ` with `φX m ≤ m` (`κOf` for LPN, `κOfN` for the PRG);
- the assumption's typed challenge `XChal m` and its encoding `encX m : XChal m → List Bool`, **exactly**
  the string the assumption's game hands its distinguisher (`LWE.encodeChallenge` at
  `(P.lpnFamily π)`'s width; `pairEncode (G.encIdx N I) (List.ofFn w)` for the PRG);
- a finite, **inhabited at every `m`** advice type `XAdvice m` (C13) with an explicit encoding
  `encXAdvice m` that starts with `(π (φX m)).enc` and has an explicit `PolyExpr` length bound;
- a deterministic **pre-processing** `XPre m (ω : XAdvice m) (x : XChal m) : List Bool`: the
  sPRG challenge string (`(jlsSPRG P π).challengeStr` at `φX m`) of the hop's hybrid sample built
  from ω and x (mod-p arithmetic in `ZMod`, no encoding gymnastics);
- the reduction function
  ```lean
  def XRed (A : NUPPT) (m : ℕ) (ω : XAdvice m) (x : XChal m) (r : List Bool) : List Bool :=
    A.runAtL (φX m) (XPre m ω x) (r.take (A.coinLen (φX m)))
  ```
  i.e. a function of the input `x`, the advice `ω` and the coins `r`, using the adversary only through
  its input/output map `A.runAtL`; coins `A.coins.subst .var`.

This is the conclusion shape of `Complexity.NUPPT.exists_reparam_pre_post`
(`Asymptotic/UniversalLemmas.lean:79`) with `post := id` and `β := encXAdvice ∘ ω`, so a
polynomial-time string map agreeing with `XPre` on encodings yields a realiser (Q-S11 A).

LPN advice at `L` (κ := κOf L, pp := π κ; meaningful when `L = ℓ κ`, a default otherwise): the
chain (tail y or tail r), the hop index in `Fin (κ + 1)`, and ω* = (I, φ_bkt, σ, the tail string
(y = Eval_I(σ) itself, hardwired, so the pre-processing never evaluates G), `(s, noise coins)` of the
real instances, `u` of the uniform ones). The challenge `(A, b)` supplies the shared matrix A and the
hop instance; later instances are computed as `A s + e + σ` from A and the hardwired values. PRG
advice at `N` (κ := κOfN N): φ_bkt, A, the uniform `u⁽ᵏ⁾`. Lengths and casts between
`Fin (L ^ D)` and `Fin (n κ)` when `L = κ ^ E`: through `finCongr` and the `κOf` readers.

**The realisation predicate** (Q-S9; home `Asymptotic/Realization.lean` if A, else
`StructuredSeed/Realization.lean` under the same name inside the job's namespace; to be reconciled
with the PHFE draft's `NUPPT.Realizes`, see Q-S9):

```lean
/-- `B` realises the reduction function `R` on the encoded challenges `enc`, with coin polynomial
`c`: `B.coins = c` and, at every parameter `m`, on the encoding of every challenge `x` and every coin
string `r`, `B`'s output is `R m x r`. Only the behaviour on well-formed challenges is constrained.
Phase A states security for every such `B`; Phase B constructs one. -/
def Complexity.NUPPT.RealizesOn (B : NUPPT) {X : ℕ → Type} (enc : ∀ m, X m → List Bool)
    (c : PolyExpr) (R : ∀ m, X m → List Bool → List Bool) : Prop :=
  B.coins = c ∧ ∀ m (x : X m) (r : List Bool), B.runAtL m (enc m x) r = R m x r
theorem NUPPT.realizesOn_iff …
/-- A realiser's verdict on an encoded challenge is `R`'s (`distinguisherL_eq`, `runAt_eq`). -/
theorem NUPPT.RealizesOn.distinguisherL_eq …
```

**Hop lemmas (M4).** For each hop, every realiser's advantage dominates the hop's gap at the chosen
advice: e.g. `|accept (hyb … k) − accept (hyb … (k+1))| ≤ (P.lpnFamily π).adv B (P.ℓ κ)` for every
`B` realising `lpnRed π A · (ω ·)` with `ω (ℓ κ)` the averaging choice
(`abs_expect_sub_le_expect`, `exists_expect_sample_le`, `Bridge.distAdv_eq`, the uniform-prefix law
of the coins).

### 4.9 Results

```lean
-- M1–M3: as design-r1 §4.7, at (κ, pp); for instance
theorem G4_eval_eq (P) (κ) (pp : PrimeParam κ) (I' : P.Idx' κ pp) :
    (P.sdSampFull κ pp I').AllOutputs fun x => ∀ j, … = if x.err then 0 else …
theorem jls_hasComplexity (P : Params) (π : PrimeSchedule) : (jlsSPRG P π).HasComplexity P.d 2
theorem jls_hasPolyStretch (P) (π) {τ} (hτ : 1 < τ) (hs : P.G.HasStretch τ)
    (hE : E₀ P.d P.δ τ ≤ P.E) : (jlsSPRG P π).HasPolyStretch
noncomputable def Params.errProb (P : Params) (κ : ℕ) (pp : PrimeParam κ) : ℝ :=
  prob ((P.idSamp' κ pp).bind fun I' => P.sdSampFull κ pp I') (·.err = true)
theorem claim42 (P : Params) {cLoc} (hLoc : P.R.HasLocality cLoc) :
    ∃ κ₀, ∀ κ ≥ κ₀, ∀ pp : PrimeParam κ, P.errProb κ pp ≤ (2 : ℝ)⁻¹ ^ κ

/-- THE CORE THEOREM [JLS26, Proposition 4.1 with Lemma 4.2; Claim 4.2's event left explicit]:
for every sPRG adversary `A` there is advice for the two reductions such that EVERY NUPPT
realising them satisfies, at EVERY κ, the explicit inequality below. -/
theorem prop41 (P : Params) (π : PrimeSchedule) (A : NUPPT) :
    ∃ (ωL : ∀ L, P.LPNAdvice π L) (ωG : ∀ N, P.PRGAdvice π N),
      ∀ BL BG : NUPPT,
        BL.RealizesOn (P.lpnEnc π) (A.coins.subst .var) (fun L x r => P.lpnRed π A L (ωL L) x r) →
        BG.RealizesOn (P.prgEnc) (A.coins.subst .var) (fun N x r => P.prgRed π A N (ωG N) x r) →
        ∀ κ, (jlsSPRG P π).adv A κ ≤
          2 * κ * (P.lpnFamily π).adv BL (P.ℓ κ) + P.G.adv BG (P.n κ) + 2 * P.errProb κ (π κ)

/-- Phase B obligations, as propositions (S10): for every adversary and every advice, some NUPPT
realises the reduction. -/
def Params.LPNRealizable (P) (π) : Prop := ∀ (A : NUPPT) (ω : ∀ L, P.LPNAdvice π L),
  ∃ B : NUPPT, B.RealizesOn (P.lpnEnc π) (A.coins.subst .var) (fun L x r => P.lpnRed π A L (ω L) x r)
def Params.PRGRealizable (P) (π) : Prop := …
def Params.Realizable (P) (π) : Prop := P.LPNRealizable π ∧ P.PRGRealizable π

-- M5: corollaries of `prop41` and `claim42`
theorem jls_secure (P) (π) {cLoc} (hLoc) (hR : P.Realizable π)
    (hG : P.G.Secure) (hLPN : (P.lpnFamily π).Assumption) : (jlsSPRG P π).Secure
/-- Explicit exponent: with `m := min (E·cL) (min (E·D·cG) 1)`, the sPRG advantage is
`SubexpSmall (m / 2)` (any exponent below `m` would do; disclose if a stronger form is stated). -/
theorem jls_subexpSmall (P) (π) {cLoc} (hLoc) (hR : P.Realizable π) {cL cG : ℝ}
    (hcL : 0 < cL) (hcG : 0 < cG) (hG : ∀ D, SubexpSmall cG (P.G.adv D))
    (hLPN : ∀ D, SubexpSmall cL ((P.lpnFamily π).adv D)) (A : NUPPT) :
    SubexpSmall (min (P.E * cL) (min (P.E * P.D * cG) 1) / 2) ((jlsSPRG P π).adv A)
theorem jls_subexpSecure (P) (π) {cLoc} (hLoc) (hR : P.Realizable π)
    (hG : SubexpHard P.G.adv) (hLPN : SubexpHard (P.lpnFamily π).adv) :
    SubexpHard (jlsSPRG P π).adv
theorem theorem41 (P) (π) {cLoc τ} (hLoc) (hτ : 1 < τ) (hs : P.G.HasStretch τ)
    (hE : E₀ P.d P.δ τ ≤ P.E) (hR : P.Realizable π) (hG : P.G.Secure)
    (hLPN : (P.lpnFamily π).Assumption) :
    (jlsSPRG P π).Secure ∧ (jlsSPRG P π).HasComplexity P.d 2 ∧ (jlsSPRG P π).HasPolyStretch
theorem theorem41_subexp … (hG : SubexpHard P.G.adv) (hLPN : SubexpHard (P.lpnFamily π).adv) :
    SubexpHard (jlsSPRG P π).adv ∧ (jlsSPRG P π).HasComplexity P.d 2 ∧ (jlsSPRG P π).HasPolyStretch
theorem exists_sprg {d cLoc : ℕ} (hd : 1 ≤ d) {δ τ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hτ : 1 < τ)
    (G : BoolPRG) (R : G.MultilinearRep d) (hLoc : R.HasLocality cLoc) (hs : G.HasStretch τ)
    (hG : G.Secure) (π : PrimeSchedule) (hLPN : ∀ E, 1 ≤ E → (lpnFamilyOf d δ E π).Assumption)
    (hR : ∀ P : Params, P.Realizable π) :
    ∃ S : SPRG, (∀ κ, S.modulus κ = (π κ).p) ∧ S.Secure ∧ S.HasComplexity d 2 ∧ S.HasPolyStretch
theorem exists_sprg_subexp … (hG : SubexpHard G.adv)
    (hLPN : ∀ E, 1 ≤ E → SubexpHard (lpnFamilyOf d δ E π).adv) (hR : ∀ P : Params, P.Realizable π) :
    ∃ S : SPRG, (∀ κ, S.modulus κ = (π κ).p) ∧ SubexpHard S.adv ∧ S.HasComplexity d 2 ∧
      S.HasPolyStretch
```

**Corollary routes.**
- *Negligible*: from `prop41` with the realisers given by `hR`; `Negligible.comp_of_le`
  (`Foundations/Negligible.lean:237`) along `ℓ κ ≥ κ` and `n κ ≥ κ`; `Negligible.polyExpr_mul`
  (`Asymptotic/ReductionSupport.lean:267`) for `2κ`; `.add`; `claim42` with
  `negligible_two_pow_neg` and `Negligible.mono`.
- *Subexponential*: take `cL`, `cG` from the two `SubexpHard` hypotheses (fixed before the adversary).
  For the realisers of `A`: `SubexpSmall.comp_of_rpow_le` with `a = E` (`(κ:ℝ)^E ≤ ℓ κ`) gives
  exponent `E·cL`, then `.mul_pow` (k = 1) and `.const_mul` (factor 2) to `3m/4`; the PRG term
  along `n κ = κ^{E·D}` gives `E·D·cG`, then `.mono_exponent` to `3m/4`; the slack: `claim42`,
  `subexpSmall_two_pow_neg` (exponent 1), `.mono`, `.const_mul`, `.mono_exponent` to `3m/4`; two
  `.add` to `m/2`; `.mono` with `0 ≤ adv ≤` the sum (for every κ). The exponent `m/2` depends only on
  `cL`, `cG`, E and D, so `SubexpHard` follows (`subexpHard_iff`).
  `eventually_const_mul_rpow_mul_two_rpow_neg_le` is available for any direct estimate.
- `exists_sprg(_subexp)`: E := max 1 (E₀ d δ τ) and `theorem41(_subexp)`; non-vacuity of the
  schedule hypothesis by `PrimeSchedule.nonempty`.
- The docstrings of every corollary say that the realisability hypothesis is the Phase B obligation
  (S10), discharged later by Phase B's programs (or, with Q-S11 A, by the targets of §4.10).

### 4.10 Efficiency statements (written, not proved; Phase B targets)

Recommended form (Q-S10 A): **named propositions** in `Targets.lean`, each with an `_iff` reader and
a docstring "Phase B obligation; not proved in this development". No `sorry` anywhere. Every target
is a uniform `PolyTimeComputable` statement (S11) with the map quantified before κ, `pp`, and the
schedule:

```lean
/-- T1, Eval′ (uniform; p from the input). -/
def Params.evalTarget (P : Params) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ κ (pp : PrimeParam κ) (I' : P.Idx' κ pp) sd,
      f (NUPPT.advInput κ (pairEncode pp.enc (pairEncode (P.encIdx' κ pp I') (P.encSeed' κ pp sd)))) =
        List.ofFn (P.eval' κ pp I' sd)
/-- T2, Q_I generation [JLS26, Definition 3.3, "efficiently generated from I"]: some term list
denoting `G⁽⁴⁾_j`. -/
def Params.qGenTarget (P : Params) : Prop :=
  ∃ f, PolyTimeComputable f ∧ ∀ κ (pp : PrimeParam κ) I' (j : Fin (P.m κ)),
    ∃ ts, f (NUPPT.advInput κ (pairEncode pp.enc (pairEncode (P.encIdx' κ pp I') (encFin j)))) =
      encTerms (encZMod (κ + 1)) encFin ts ∧ denote ts = P.G4 κ pp I' j
/-- T3, the samplers' deterministic cores (`sdCore`; IdSamp′'s core is the identity, C14), on the
encodings of their exact-law draws: what the sampler bridge composes with. -/
def Params.coreTarget (P : Params) : Prop := …
/-- T4, the reductions' pre-processing, one map for every schedule, length and adversary; the prime
comes in the advice. -/
def Params.lpnPreTarget (P : Params) : Prop :=
  ∃ f, PolyTimeComputable f ∧ ∀ (π : PrimeSchedule) L (ω : P.LPNAdvice π L) (x : P.LPNChal π L),
    f (pairEncode (P.encLPNAdvice π L ω) (P.lpnEnc π L x)) = P.lpnPre π L ω x
def Params.prgPreTarget (P : Params) : Prop := …
def Params.ReductionTargets (P : Params) : Prop := P.lpnPreTarget ∧ P.prgPreTarget
```

Phase A proves only the cheap derivations, sorry-free:
- `evalEfficient_of_target : P.evalTarget → ∀ π, (jlsSPRG P π).EvalEfficient` and the same for
  `HasComplexityEff` from T2 and `jls_hasComplexity`'s degree bounds (Q-S10 A);
- with Q-S11 A, `realizable_of_targets : P.ReductionTargets → ∀ π, P.Realizable π`
  (`NUPPT.exists_reparam_pre_post` with `post := id`, `φ := κOf` or `κOfN`, `p := .var`,
  `β := encXAdvice ∘ ω` and its length bound, then the target's equation on encodings), and
  `theorem41_of_targets`, `exists_sprg_of_targets` (the classical "∃ NUPPT" statements under the
  targets). This is TM-level (`PolyTimeComputable`), commits to no RAM interface, and checks that the
  reduction shapes are realisable.

The jobs that make the targets true are Phase B's (§9). The job must not try to prove T1–T4, nor
build machines for them.

## 5. Milestones (Phase A)

Each milestone ends with a commit on `fill/io-sprg` and a checkpoint push. M1–M3 are independent;
M4 needs M1 (`G4_eval_eq` for the statistical hops; `errProb` is an M0 definition, so M4 does not
need M3); M5 needs M2–M4; M6 needs M4 and the targets of M0.

| M | Content | Exit criterion | Lines (cum.) |
|---|---|---|---|
| **M0** statements | every file of §2.2 with module docstring; **every definition final**: LPN, BoolPRG (+ efficiency predicates), degree notions, `PolyTerms`, `PrimeParam`/`PrimeSchedule`, `SPRG` and its predicates (incl. `EvalEfficient`, `HasComplexityEff`), `Params` and derived quantities, buckets, sparse factor, polynomials, samplers and cores, encodings with explicit equivalences, `jlsSPRG`, `errProb`, hybrids, advice types and encodings, `lpnPre`/`prgPre`, `lpnRed`/`prgRed`, `RealizesOn` (if local), realisability propositions, targets T1–T4; readers proved; `PrimeSchedule.nonempty` proved; **every theorem stated with `sorry`** under its `**Proof sketch.**`; REPORT fidelity table | all modules elaborate (rc 0, 0 errors), `sorry` only in listed theorems; coe-A seals and controls on the definitions; lint; StmtDump | 1,900–2,900 |
| **M1** algebra | degree closure lemmas, buckets, sparse factor, G⁽¹⁾–G⁽⁴⁾ evaluation and degrees (through the renaming), `G4_eval_eq`, `jls_hasComplexity`, `lpnNoise_law` | listed theorems sorry-free, standard axioms | +800–1,450 |
| **M2** stretch | `jls_seedBits_le`, `jls_hasPolyStretch` (confirm C10) | same | +250–450 |
| **M3** Claim 4.2 | Markov step, balls-in-bins, binomial bound, independence over k, side conditions, `claim42` (uniform in `pp`) | same | +600–1,000 |
| **M4** hybrids and core | statistical hops (`abs_prob_sub_le_of_agree` + `errProb`), the hop lemmas for every realiser, `prop41` | same | +650–1,200 |
| **M5** Theorem 4.1 | `jls_secure`, `jls_subexpSmall`, `jls_subexpSecure`, `theorem41`, `theorem41_subexp`, `exists_sprg`, `exists_sprg_subexp` | same | +220–420 |
| **M6** targets link | advice length bounds, `realizable_of_targets`, `theorem41_of_targets`, `exists_sprg_of_targets` (Q-S11 A), `evalEfficient_of_target`, `hasComplexityEff_of_target` (Q-S10 A) | **0 `sorry`** in the job; full evidence | +180–480 |
| **Total** | | | **4,600–7,900** (central ≈ 6,000) |

## 6. Proof sketches the statements must carry (M0)

As design-r1 §6 (`claim42`, `jls_hasComplexity`, `jls_seedBits_le`), with r2 additions:
- `prop41`: H₀ (real game at `π κ`) ≈ H₁ (err published as 0) costs `errProb` (agree off
  `err = 1`); H₁ → H₂ is the LPN chain with tail y (κ hops), the PRG hop, and the LPN chain with tail
  r (κ hops); H₂ ≈ H₃ (the random game) costs `errProb`. `advantage_hybrid` and
  `exists_advantage_hybrid_gap` bound the 2κ LPN hops by 2κ times the worst; the worst hop and its
  ω* go into `ωL (ℓ κ)`; each realiser's advantage dominates its hop by the hop lemma. The PRG hop
  likewise with `ωG (n κ)`. No step uses efficiency.
- `jls_subexpSmall`: the route of §4.9 with the exponent arithmetic written out.
- `realizable_of_targets`: `exists_reparam_pre_post` instantiation; the coin identification
  `A.coins.subst .var`; the target's equation on `pairEncode (encXAdvice ω) (encX x)`.
- `PrimeSchedule.nonempty`: Bertrand at `2^κ` (`Nat.exists_prime_lt_and_le_two_mul`), with
  `2^κ < p ≤ 2^(κ+1)`.

## 7. Risks

1. **Elaboration cost of the polynomials** (design-r1 §7.1). The renaming to `Fin` variables (C13)
   adds a layer: prove degrees and evaluations on the structured form, transfer once.
2. **Rule 10 across the job's files** (design-r1 §7.2), now also for the reduction functions, advice
   encodings and targets (each needs its reader at M0).
3. **Vacuity traps.** (i) An advice type empty at some parameter makes `∀ L, LPNAdvice π L` empty and
   `prop41` vacuous: every advice type must be inhabited at every `m` (use `Fin (κ + 1)`, defaults).
   (ii) `PrimeSchedule` must be inhabited (C2, `PrimeSchedule.nonempty`). (iii) A realisation
   predicate that also pins `B`'s advice or behaviour off the encodings would be stronger than Phase B
   can deliver; constrain only well-formed challenges.
4. **Classical encodings** (C13): any `Fintype.equivFin`, `Finset.toList` or `Classical.choose` inside
   an encoding or a pre-processing map makes a target false or unprovable. Statements-gate check.
5. **Dependent casts** between the LPN family's `Fin (L ^ D)` and the sPRG's `Fin (n κ)`: keep them
   behind `κOf` readers and `finCongr`; never `rfl` across `κOf`.
6. **Constants of Claim 4.2** (design-r1 §7.4): eventually-statements only.
7. **Statement changes after M0**: only as separate, disclosed commits (Q-S8, ruled).

## 8. Disclosed deviations (docstrings must say each where it applies)

Dv1–Dv8, Dv10, Dv11, Dv13 as design-r1 §8. Changed or new:
- **Dv9** p is a public input: a (κ+1)-bit prime from an arbitrary schedule (`2^κ ≤ p ≤ 2^(κ+1)`,
  p = 2 at κ = 0), not "an efficiently computable function in λ" (Def 3.3); every statement holds for
  every schedule; the adversary receives p.
- **Dv12** Reductions are Lean functions of input, advice and coins; they hardwire averaged values in
  their advice and never sample; the paper's reductions sample (§4.8).
- **Dv14** Phase A: no efficiency is proved. Security is stated for every NUPPT realising the
  reductions, and the assumption-level corollaries assume realisability; efficiency of Eval′, Q_I
  generation, the samplers' cores and the reductions are named Phase B targets (§4.10). Sampler
  efficiency waits for the sampler bridge.
- **Dv15** Seeds of the generic sPRG are `Fin`-indexed ℤ_p vectors (C13); the construction's
  structured private seed is transported by an explicit equivalence.

## 9. Phase B outlook (not this job)

- **When**: after the RAM bridge's deliverables (a) and (b) of `ram-bridge-assessment.md` exist on a
  base that has both `Complexity/Randomized/PPT.lean` and the RAM layer (main ≥ #364 plus the RAM
  branch; the records branch's own RAM files are stale). Seyoon's bridge branch and its final API
  names are not known yet (row *Word-RAM bridge: held*).
- **What**: single uniform word-RAM programs (one program for all κ, p and advice read from the
  input) for Eval′, Q_I generation, the samplers' cores and `lpnPre`/`prgPre`; their halting bounds
  on every input and correctness on well-formed inputs; then (a1) `polyTimeComputable_of_computes`
  discharges T1–T4. With Q-S11 A, `theorem41_of_targets` turns T4 into the unconditional "∃ NUPPT"
  Theorem 4.1 with no further crypto work; otherwise Phase B builds the realisers itself through
  `exists_reparam_pre_post`. The samplers' efficiency comes from the in-house sampler bridge
  (`UniformSampler`, `bucketRaw`) composed with T3; the prime from the later prime-sampler bridge.
- **Axioms**: theorems built on the RAM simulation carry `sorryAx` through `WordRAM.exists_simulation`
  (then the tier-2 statements) until those fills land; they stay separate from the Phase A
  theorems, which remain standard-axiom.
- **Moved out of this dispatch** (from r1 M4): `matVecPoly` at a non-wrapping width, `BinArith.mod`,
  `addPoly`, `toLE`, the H16 loop, `NUPPT.wrap`-based hop machines, their run and efficiency lemmas.
  The duplication sweep keeps them in its Phase B appendix.
- **Size**: not estimated here; it depends on the authoring language chosen for (a5).

## 10. Questions

### 10.1 Settled since r1 (rows of 2026-11-18 in the decision log)

| r1 question | Status | Ruling (decision-log row) | Consequence in r2 |
|---|---|---|---|
| ★Q-S1 LPN hypothesis | **settled: A** | *sPRG rulings (Seyoon)*: "LPN for the construction's own ℓ-indexed family (the literal Def 2.3 bridge later)" | §4.2, C11; the bridge is out of scope (S6) |
| ★Q-S2 modulus | **settled: A, refined** | *sPRG rulings*: fixed prime schedule p(κ) in both jobs; *Strategy and uniformity* (3): p an input, every schedule of κ+1 bits, prime-sampler bridge later | S12, §4.1, C2, C12 |
| ★Q-S3 efficiency of Eval/Q_I | **superseded** | *sPRG rulings* (Q-S3 changed: efficiency now, via word RAM); *Efficiency rulings* (1); *Strategy and uniformity* (1): Phase A writes, Phase B proves | S10, §4.10 |
| ★Q-S4 Def 3.3's class | **settled: A** | *sPRG rulings*: degree-d public / degree-2 private, one polynomial | `HasComplexity` as r1; `HasComplexityEff` its efficiency form |
| Q-S5 code home | **settled: A** | *Efficiency rulings* (4): `TCSlib/Cryptography/Obfuscation/StructuredSeed/`, one line in `TCSlib.lean` | §2.1 |
| Q-S6 reduction arithmetic | **superseded** | *Efficiency rulings* (2): reductions are word-RAM programs; *Strategy and uniformity* (1): Phase A writes reductions as Lean functions | no machines in Phase A; r1 M4 machine parts → §9 |
| Q-S7 subexponential clause | **withdrawn in r1** | *Subexponential security*; API: *`Foundations/Subexponential.lean` written* | S7, §4.9 |
| Q-S8 gate repairs | **settled: A** | *Efficiency rulings*: Codex continues after checkpoint 0; majors relayed and applied as disclosed statement-change commits | prompt item 6 |

### 10.2 Open (multiple choice, recommended option first)

- **Q-S9. Where the realisation predicate lives.** The PHFE job needs the same notion. Its r2 draft
  (in progress, `briefs/io-components/phfe/design-r2.md` §4.4 and its Q5) proposes a `ReductionFn`
  structure and `NUPPT.Realizes B R`, constraining `B` on **every** input with the advice read from
  `B.advice`. The sPRG needs two things that form does not give: only **encoded challenges** are
  constrained (Phase B's programs are correct on well-formed inputs only, the `progOut` form of
  `ram-bridge-assessment.md` (a1)), and the advice is **fixed by the theorem** (the averaging choice
  ω*). `RealizesOn B enc c R` covers both and contains the PHFE form as the instance
  `enc := fun _ y => y`, `R := fun κ y r => R.run κ y (B.advice κ) r`. Recommendation for the shared
  file: `RealizesOn` as in §4.8 (optionally with `ReductionFn` and `Realizes` defined through it).
  (A) One shared owner file `TCSlib/Cryptography/Asymptotic/Realization.lean` (`NUPPT.RealizesOn`,
  its readers, the verdict lemma; ≈ 80–150 lines), written in-house and stacked on #374 before
  dispatch; `<BASE>` is that head and both jobs reuse it. If it is not at `<BASE>`, the job writes the
  same declarations in `StructuredSeed/Realization.lean` (inside its namespace) for a mechanical move
  later. (B) Each job defines its own, unified after both land (a disclosed duplication).
  (C) No predicate: each theorem carries the agreement hypothesis inline (longer statements, no
  shared vocabulary).
- **Q-S10. How Phase A writes the efficiency statements.**
  (A) Named propositions (targets T1–T4 of §4.10, uniform `PolyTimeComputable` forms) for Eval′,
  Q_I generation (via `PolyTerms`), the samplers' deterministic cores and the reductions'
  pre-processing, plus the generic `SPRG.EvalEfficient`/`HasComplexityEff`; no `sorry`.
  (B) As A without Q_I generation and the cores (docstring disclaimers instead; −150–300 lines, no
  `PolyTerms`, no `MultilinearRep.TermsEfficient`, no `HasComplexityEff`). (C) Theorems with `sorry` in a quarantined file excluded from the 0-`sorry` check.
  (D) Prose only (docstrings and REPORT).
- **Q-S11. Phase A proves the link "targets ⇒ realisers ⇒ ∃ NUPPT".**
  (A) Yes: `realizable_of_targets` through `NUPPT.exists_reparam_pre_post` (TM level, no RAM) and
  the classical `theorem41_of_targets`/`exists_sprg_of_targets` (+180–400 lines, M6). Phase B then
  only proves the `PolyTimeComputable` targets, and the reduction shapes are checked realisable now.
  (B) No: Phase B builds the realisers and the final theorems.
- **Q-S12. Where the schedule lives in the generic sPRG.**
  (A) The generic `SPRG` keeps a modulus schedule (Def 3.3's fixed p(λ)), publishes it in the
  challenge (C12) and reads it from the input in `EvalEfficient`; the construction's algorithms are
  defined for an arbitrary `pp : PrimeParam κ` and assembled per schedule (`jlsSPRG P π`); every jls
  theorem is `∀ π` and every jls target quantifies its map before `pp`. (B) The generic `SPRG` takes a
  public-parameter type with the algorithms as functions of it, and `Secure`/`HasComplexity` quantify
  over schedules inside the predicate: closer to "p is an input" at the interface, heavier for every
  consumer (Theorem 5.1 composes at one schedule anyway).
