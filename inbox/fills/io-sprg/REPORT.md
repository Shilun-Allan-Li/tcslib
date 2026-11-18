# io-sprg Phase A — M5 PARTIAL CHECKPOINT — M5 complete

All seven frozen M5 proof bodies are complete at the committed source below. Fresh exact-owner builds, selected axiom prints, source freeze and static checks pass. M6 and the final canonical/census/kernel gates remain pending.

Source: `990eba8673c73bce6c739d3fe61848d44b2fdb7c` on `fill/io-sprg`, pinned base
`5ed465f62e4ae0f93ded1a1ba49e807591b589eb`, without rebasing. M5 fills the seven
frozen raw security/existence bodies and introduces no theorem helper, algorithm,
sampler, assumption or efficiency implementation. M6's nine original target links
remain to be proved. T1–T6 truth stays Phase B; this is not end-to-end completion.
M5 packaging/publication is prepared for the authorized exchange publication. A future exchange hash cannot
be embedded in its own package; later delivery records remain the authority.

| Current M5 quantity | Bound value/evidence |
| --- | --- |
| Exact source owners/lines/largest/width | 34 owners; 10807 lines; largest 801; maximum width 100 |
| Explicit headers / frozen headers+prose / helpers / moves | 703 explicit headers; all 670 frozen headers/prose preserved; 33 previously added helpers; 93 recorded moves |
| Saved proof checks / original bodies / residual original holes | 170 saved owner checks; 137 original bodies and 33 helpers; 9 M6 original holes |
| Exact-owner fresh compilation and warning scope | 34/34 fresh owner checks: rc0, both error forms0; exactly 9 expected Targets sorry warnings, no other warnings |
| Selected current public theorem axioms | All 10 public Security theorems standard-only, including the 7 newly proved M5 declarations |
| Current headline axioms | 19 fresh prints; 14 standard-only, 5 depend on the 9 pending M6 bodies; full rows below and in compact axioms.tsv |
| Static/style/name/PDF/import scope | 703 ADDED, 0 CHANGED/REMOVED; style/sk15/clash pass; campaign rc1 matches baseline, 0 new FAIL/WARN; widths pass; PDF0 throughout source history; allowed import/export scope only |
| Tagged slot history | 1519 tagged acquisitions; historical maximum2/serial=false; exact old 3-second overlap retained; post-correction serial=true; active0 |


## Milestones and publication

| Milestone | Source head | Published exchange commit |
| --- | --- | --- |
| M0 | d10a560b34d58919bc1a5206ce66a444613f94c7 | 15946b52d0615fda8afad9ed3c57cfaf5beaaa8d |
| M1 | 19dde91afc384656e7e47cb018057e088d4ded0a | 10da7fdefd9a44023cc117a672f19e8a3617b81d |
| M2 | 4ecc40c04a001bc87349b7ec368ece309774c28a | c1d4f422f071f4a8e346d71a0f00ea3525941eee |
| M3 | 04249b85e80a007dc5845077a18a365d5150e14b | 2a9ccadc2772789ace445490f6df8d231ff1221b |
| M4 | 428c7eb117b51fe512348f226284df247e98c00c | 33e944e359da71e42c15f922513b4da2f217cad4 |
| M5 | 990eba8673c73bce6c739d3fe61848d44b2fdb7c | This prepared checkpoint; future push hash is recorded downstream |

The complete 35-commit source ledger, author/committer metadata and exact patch
series are in patches/COMMITS.tsv. Every source hash is replay-checked from the pinned
base before publication. The old bundle and old evidence remain historical and
unchanged; no refreshed bundle or bulk evidence is added. The old evidence/SHA256SUMS
is preserved as the M4 snapshot manifest. The current top SHA256SUMS covers the
complete retained exchange tree; evidence/compact/M5/SHA256SUMS covers the new results.

## Current headline axiom prints

Area prefix: TCSlib.Cryptography.Obfuscation.StructuredSeed.

| Declaration | Exact axiom list |
| --- | --- |
| `prop41` | Classical.choice, Quot.sound, propext |
| `Params.claim42` | Classical.choice, Quot.sound, propext |
| `Params.G4_eval_eq` | Classical.choice, Quot.sound, propext |
| `jls_hasComplexity` | Classical.choice, Quot.sound, propext |
| `jls_hasPolyStretch` | Classical.choice, Quot.sound, propext |
| `lpnNoise_law` | Classical.choice, Quot.sound, propext |
| `jls_secure` | Classical.choice, Quot.sound, propext |
| `jls_subexpSmall` | Classical.choice, Quot.sound, propext |
| `jls_subexpSecure` | Classical.choice, Quot.sound, propext |
| `theorem41` | Classical.choice, Quot.sound, propext |
| `theorem41_subexp` | Classical.choice, Quot.sound, propext |
| `exists_sprg_raw` | Classical.choice, Quot.sound, propext |
| `exists_sprg_raw_subexp` | Classical.choice, Quot.sound, propext |
| `PrimeSchedule.nonempty` | Classical.choice, Quot.sound, propext |
| `Params.realizable_of_targets` | Classical.choice, Quot.sound, propext, sorryAx |
| `jlsSPRG` | Classical.choice, Quot.sound, propext, sorryAx |
| `theorem41_of_targets` | Classical.choice, Quot.sound, propext, sorryAx |
| `exists_sprg_of_targets` | Classical.choice, Quot.sound, propext, sorryAx |
| `exists_sprg_of_targets_subexp` | Classical.choice, Quot.sound, propext, sorryAx |

## Frozen original bodies and shared reuse

The following anchors are from the captured working source; bind or refresh them
against FINAL_SOURCE_HEAD before packaging. Saved steps are distinct from fresh
complete owner builds and final canonical gates.

| Original declaration (area prefix omitted) | Current source anchor | Saved step |
| --- | --- | --- |
| `jls_secure` | `Security.lean:250` | 164: CHECKED_PASS |
| `jls_subexpSmall` | `Security.lean:297` | 165: CHECKED_PASS |
| `jls_subexpSecure` | `Security.lean:394` | 166: CHECKED_PASS |
| `theorem41` | `Security.lean:419` | 167: CHECKED_PASS |
| `theorem41_subexp` | `Security.lean:434` | 168: CHECKED_PASS |
| `exists_sprg_raw` | `Security.lean:451` | 169: CHECKED_PASS |
| `exists_sprg_raw_subexp` | `Security.lean:475` | 170: CHECKED_PASS |

`jls_secure` selects the actual advised realisers from prop41 and reindexes the
assumption advantages along ℓ≥κ and n≥κ using shared negligibility closure APIs.
It absorbs the factor2κ and Claim42's twice-error slack; it does not assume an
arbitrary negligible majorant is nonnegative. Claim42's cutoff precedes all primes
and is specialized only afterwards to πκ.

For subexponential security let M=min(E*cL,min(E*D*cG,1)). The shared reindex API
produces E*cL and E*D*cG; polynomial and constant factors consume strict gaps
M→7M/8→3M/4, the first sum consumes3M/4→5M/8, and the final sum yields EXACTLY
M/2. M>0 and M≤1 make the error gap3M/4<1 strict even at M=1. Only shared
SubexpSmall reindex/monotonicity/mul_pow/const_mul/add/mono and two-pow APIs are
used. Both assumption exponents are chosen before the adversary, so the output
exponent is common; no custom decay predicate or repeated generic analytic proof
is introduced. The existence witnesses use E=max1E0 and the construction's own
LPN family and realisability hypotheses. Rationalδ follows SP-W1.

## Current Phase B, statement changes and non-vacuity

The exact frozen target definitions/readers in Targets.lean remain the authority.
The following is a concise quantifier/field map, not a claim that target truth has
been proved. Current anchors must be refreshed after M6 proof-body insertion.

| Target | Frozen scope and witness order | Reader / consequence |
| --- | --- | --- |
| T1 evalTarget | ∃ONE f, PolyTimeComputable f, then ∀κ/pp/I/sd; computes Eval' on unaryκ and prime/index/seed code. | `evalTarget_iff`, `Targets.lean:80`; sPRG eval_eff. |
| T2 qGenTarget | ∃ONE f, PolyTimeComputable f, then ∀κ/pp/I/j, ∃explicit finite term list ts; output code denotes actual G4κppIj. | `qGenTarget_iff`, `Targets.lean:102`; HasComplexityEff d2 via the existing G4 correctness witness. |
| T3 coreTarget | Two shared CoreComputable halves, one uniform map EACH for the actual index core and seed core; each map precedes all its κ/public-input/draw arguments. | `coreTarget_iff`, `Targets.lean:126`; combined with T5 for both sPRG sampler fields. |
| T4 ReductionTargets | Two preprocessing maps, one LPN and one PRG map, each chosen before EVERY schedule, size, advice and challenge. Shared RealizesOn/preTarget APIs are unchanged. | `lpnPreTarget_iff`/`prgPreTarget_iff`/`reductionTargets_iff`, `Targets.lean:145,160,172`; conditional realisers. |
| T5 drawSamplerTarget | Two shared DrawSamplable halves, each ∃U/c/e before allκ/public inputs, exact encoding equation and ≤2^-κ failure. Each is ONE complete draw, including products. | `drawSamplerTarget_iff`, `Targets.lean:186`; no constructed product fair-coin sampler. |
| T6 lpnSamplerTarget | SamplesEfficiently with parameter `fun _ => PrimeSchedule`: ONE U/c/f before allL AND allπ, for the exact joint matrix/secret/noise draw and core. Restrict only e/equations atπ afterwards. | `lpnSamplerTarget_iff`, `Targets.lean:205`; LPNFamily.sample_eff. |

`Params.Targets` is exactly T1∧T2∧T3∧T4∧T5∧T6. A primitive value still requires
all mandatory efficiency fields; Raw algorithms do not claim efficiency. M6 links
and assemblies remain conditional on those targets and do not establish them.

| Statement/design item | Current status and exact retained meaning |
| --- | --- |
| M5 changes | Seven existing proof bodies only; no added helper/algorithm/sampler and no frozen statement, hypothesis, encoding, definition, import or attribute change. Fresh source/freeze binding: Fresh global freeze matches every committed owner SHA; all 670 original headers/prose preserved; source diff adds only M5 proof bodies. |
| SP-W1 | δ is rational data, coerced to real only for analysis/E0. |
| SP-W2 | Two acceptance-probability equalities, never false free-oracle program equalities for unused queries. |
| SP-W3 / non-vacuity | Raw.HasPolyStretch is `∃τ:ℝ,1<τ ∧ ∃κ₀,∀κ≥κ₀,κ≤seedBitsκ ∧ (seedBitsκ:ℝ)^τ≤outLenκ`; growing seed bits exclude constant/zero-length existential vacuity. The construction's M2 proof retains this. All algorithms still accept κ=0. |
| Own-family/realisers | LPN assumptions and raw realisability range over the actual E-indexed construction family; advice families precede all realisers/allκ; common SubexpHard exponent precedes the adversary. |
| Earlier deviations | All Dv1–Dv18, finite encodings/coordinates, transposed canonical LPN convention, rounding, composite bidegree d/2, exact joint draws and efficiency/prime-input judgments remain as detailed in the retained fidelity table and published M4 StatementChanges section. No new M5 deviation is introduced. |

## Required mathematical tables (retained detail)

The four tables below are extracted byte-for-byte from the published M4 report.
Their M0 line anchors are explicitly historical; the frozen names/statements,
fidelity/deviations, mandatory uniform fields, target selection and non-vacuity
remain applicable. Current M5 proof anchors appear above; root will refresh a
separate current owner/name map after M6. This is the required table material,
not the full historical report or raw-gate appendix.

## Frozen fidelity, Rule15 and non-vacuity tables

All four mathematical tables below are byte-exact M0 snapshots. Their line numbers
are **historical M0 anchors**; current committed-source anchors are indexed separately.

### Archived M0 fidelity table

| Paper item / page | Lean names and locations | Fidelity and deviations |
| --- | --- | --- |
| Multilinear representation, §2 p.8; efficient polynomial descriptions, Def.3.3 p.10 | `PolyTerms` (`PolyTerms.lean:45`); `PolyTerms.denote` (`PolyTerms.lean:56`); `PolyTerms.encTerms` (`PolyTerms.lean:85`) | Explicit finite term lists with repeated variable occurrences encode powers. Coefficients and finite coordinates have faithful sign/numeral encodings. `BoolCircuit.encodeList` and `pairEncode` delimit terms. This is a disclosed representation choice for T2, not a new polynomial semantics. |
| Scalar noise; Def.2.3, pp.9-10 | `lpnNoise` (`LPN.lean:49`); `lpnNoise_law` (`LPN.lean:67`) | One exact selector/residue draw gives `(1-1/W) delta_0 + (1/W) Uniform(ZMod p)`. Triggered noise may also be zero. Dv3 fixes the exact rounded rate. |
| LPN family and assumption; Def.2.3, pp.9-10 | `LPNFamily.Raw` (`LPN.lean:79`); `LPNFamily.Raw.toLWE` (`LPN.lean:136`); `LPNFamily.Raw.adv` (`LPN.lean:166`); `LPNFamily.Raw.Assumption` (`LPN.lean:175`) | Canonical `LWE.Parameters`, `LWE.Noise`, `LWE.Family`, `advantageAt`, and `DLWEAssumption` are reused. Dv3 assumes the construction's own l-indexed family, with transposed row/sample convention and canonical challenge encoding; no literal Def.2.3 bridge is claimed. |
| Honest LPN sampling; Def.2.3, pp.9-10 | `LPNFamily.Raw.Draw` (`LPN.lean:189`); `LPNFamily.Raw.sampleCore` (`LPN.lean:306`); `LPNFamily.Raw.sampleLaw` (`LPN.lean:317`); `LPNFamily` (`LPN.lean:400`) | One finite product draw includes the matrix, common secret, and all scalar noise seeds. `LPNFamily` adds mandatory shared `SamplesEfficiently`; Raw does not claim efficiency. Dv17/Dv18. Explicit draw coordinates are composition data, with no chosen enumeration. |
| Boolean PRG; Def.3.4, p.11 | `BoolPRG` (`BoolPRG.lean:50`); `BoolPRG.idSamp` (`BoolPRG.lean:124`); `BoolPRG.game` (`BoolPRG.lean:162`); `BoolPRG.Secure` (`BoolPRG.lean:191`); `BoolPRG.SubexpSecure` (`BoolPRG.lean:199`); `BoolPRG.HasStretch` (`BoolPRG.lean:207`) | Evaluation and exact index-core sampling both carry uniform efficiency fields. Every assumption quantifies NUPPT adversaries. Dv5 uses the settled pointwise stretch lower bound rather than an exact real-power output length; Dv13 uses the shared subexponential-advantage notion. |
| Multilinear degree and locality; Def.3.4, p.11 | `BoolPRG.MultilinearRep` (`BoolPRG.lean:217`); `BoolPRG.MultilinearRep.HasLocality` (`BoolPRG.lean:234`); `BoolPRG.MultilinearRep.TermsEfficient` (`BoolPRG.lean:245`) | Integer multilinear polynomials have degree <=d and equal output bits on Boolean inputs. Dv4 measures locality on the supplied representation at every index. Term-generation efficiency is a Phase B hypothesis, not proved here. Faithful input encoding and explicit finite-coordinate data are disclosed pre-M0 refinements. |
| sPRG syntax; Def.3.1, p.10 | `SPRG.Raw` (`Defs.lean:97`); `SPRG.Raw.idSamp` (`Defs.lean:179`); `SPRG.Raw.sdSamp` (`Defs.lean:188`); `SPRG` (`Defs.lean:397`) | Exact samplers are deterministic cores applied to one uniform complete draw. Raw stores the algorithms; the primitive adds evaluator and two shared sampler efficiency fields. Dv2 finite modular seed vectors; Dv9 modulus schedule; Dv15 explicit coordinates; Dv17/Dv18. |
| Security; Def.3.2, p.10 | `SPRG.Raw.challengeStr` (`Defs.lean:218`); `SPRG.Raw.game` (`Defs.lean:234`); `SPRG.Raw.adv` (`Defs.lean:251`); `SPRG.Raw.Secure` (`Defs.lean:260`); `SPRG.Raw.SubexpSecure` (`Defs.lean:267`) | Challenges publish prime, index, public seed, and real or uniform output. Dv9/Dv13/Dv18. Primitive property wrappers read the raw bundle through proved readers. |
| Complexity; Def.3.3, p.10 | `pubDegree` (`Degree.lean:45`); `privDegree` (`Degree.lean:56`); `SPRG.Raw.HasComplexity` (`Defs.lean:298`); `SPRG.Raw.HasComplexityEff` (`Defs.lean:352`) | Dv6 specializes to the composite output polynomial with separate public/private bounds. Efficient complexity uses one uniform map that outputs explicit term lists for actual polynomials. Dv10 takes public degree d from p.17, not the overview's d+1 wording on p.14. |
| Prime field / parameter convention; Def.2.3 pp.9-10 and §4 p.15 | `PrimeParam` (`Defs.lean:48`); `PrimeSchedule` (`Defs.lean:72`); `PrimeSchedule.nonempty` (`Defs.lean:82`) | Public p satisfies `2^kappa <= p <= 2^(kappa+1)` and primality. Params stores no prime. Dv9 accepts every schedule, with the prime supplied as input. Bertrand is used only for non-vacuity; no prime algorithm is defined. |
| Construction dimensions and rounding; §4 p.15 | `Params` (`Params.lean:50`); `Params.D` (`Params.lean:64`); `Params.ℓ` (`Params.lean:70`); `Params.n` (`Params.lean:76`); `Params.m` (`Params.lean:83`); `Params.noiseWidth` (`Params.lean:90`); `Params.W` (`Params.lean:111`); `Params.t` (`Params.lean:120`); `Params.rc` (`Params.lean:126`); `Params.cap` (`Params.lean:132`); `Params.B` (`Params.lean:138`); `Params.Γ` (`Params.lean:146`) | Dv1 one parameter and exact power schedules; Dv3 integer floors/ceilings with positive bucket/noise widths; Dv5 output stretch lower bound; Dv11 positive degree. SP-W1 stores rational delta and coerces it to real for analysis. Gamma uses integer base-two log and integer division. |
| Reindexing assumption dimensions; Remark2.1 p.9 | `Params.kappaOf` (`Params.lean:155`); `Params.kappaOfN` (`Params.lean:164`); `Params.kappaOf_pow` (`Params.lean:305`); `Params.kappaOfN_n` (`Params.lean:315`); `Params.lpnFamily_raw` (`Params.lean:339`) | Bounded greatest searches invert the fixed power schedules, with inverse <=identity and exact on-image equations. Dv1/Dv3 define the own l-indexed LPN family; arbitrary public prime schedule is read at the inverse parameter. |
| Public/private seed layout; SdSamp', pp.15-16 | `Params.Pub` (`Params.lean:247`); `Params.Priv` (`Params.lean:201`); `Params.SVar` (`Params.lean:180`); `Params.pubLen` (`Params.lean:173`); `Params.privLen` (`Params.lean:209`); `Params.pubEquiv` (`Params.lean:255`); `Params.privEquiv` (`Params.lean:232`) | Public seed contains kappa public vectors and error; private seed contains per-instance flag, data, and precomputed flag*data. Dv2 counts residue coordinates before fixed-width bits; Dv15 explicit Fin equivalences replace implicit enumeration. |
| Bucket placement; IdSamp', p.15 | `Buckets.bucket` (`Buckets.lean:52`); `Buckets.load` (`Buckets.lean:61`); `Buckets.rank` (`Buckets.lean:77`); `Buckets.indexMap` (`Buckets.lean:87`); `Buckets.bucketMatrix` (`Buckets.lean:147`) | Increasing ranks give deterministic injective positions. Pre-M0 refinement uses `Option (Fin rc x Fin rc)` and `none` on overfull/empty grids: at kappa=0 the required grid is empty, so a total default point cannot exist. All successful placements/capacity conventions are preserved. Matrix coordinates sum matching corrections without a choice. |
| Sparse correction factors; 1SdSamp, p.16 | `sparseEntries` (`SparseFactor.lean:48`); `sparseLeft` (`SparseFactor.lean:61`); `sparseRight` (`SparseFactor.lean:76`); `sparseFactor` (`SparseFactor.lean:91`); `sparseFactor_mul_of_card_le` (`SparseFactor.lean:146`) | Deterministic row-major nonzero listing fixes the paper's unspecified factor choice. One stored entry per factor slot reconstructs a matrix with <=t nonzeros. Total over semirings, zero padding, no rank theorem or classical enumeration. |
| Finite coordinates and encodings; §4 pp.15-17 | `Params.IdDraw` (`Encoding.lean:135`); `Params.Draw` (`Encoding.lean:147`); `Params.Seed` (`Encoding.lean:160`); `Params.idxEquiv` (`Encoding.lean:196`); `Params.idDrawEquiv` (`Encoding.lean:214`); `Params.drawEquiv` (`Encoding.lean:232`); `Params.encIdx'` (`Encoding.lean:263`); `Params.encIdDraw` (`Encoding.lean:275`); `Params.encDraw` (`Encoding.lean:308`); `Params.encSeed'` (`Encoding.lean:320`) | Dv15/Dv17 use supplied Boolean coordinates and canonical residue/function/product equivalences. Named injectivity obligations retain every field. Encoding is split into its own module, a disclosed modular refinement. No `Fintype.equivFin` or chosen enumeration. |
| Explicit polynomial size bounds; §4 p.15 and Claim4.1 p.18 | `Params.ellBound` (`Encoding.lean:331`); `Params.nBound` (`Encoding.lean:337`); `Params.mBound` (`Encoding.lean:343`); `Params.bucketBound` (`Encoding.lean:349`); `Params.rcBound` (`Encoding.lean:356`); `Params.sVarBound` (`Encoding.lean:371`); `Params.seedBound` (`Encoding.lean:382`); `Params.idxBound` (`Encoding.lean:392`) | Syntactic `PolyExpr` values bound every concrete size and code. Bucket numerals use numeric B bits (generous but polynomial); noise selectors use ell+1 bits; residues use kappa+1 bits. All bounds include kappa=0. |
| Equation(3), G(1), p.17 | `Params.linearCoeff` (`Polys.lean:146`); `Params.halfForm` (`Polys.lean:169`); `Params.prgPoly` (`Polys.lean:189`); `Params.G1` (`Polys.lean:229`); `Params.G1_eval` (`Polys.lean:371`) | Sorted monomial supports are padded with constants, split at D, and tensor-expanded. Dv3 transposes the public LPN matrix; Dv4 uses supplied multilinear representation; Dv15 uses explicit output-coordinate casts. |
| Equation(3), G(2), p.17 | `Params.correctionPoly` (`Polys.lean:208`); `Params.G2` (`Polys.lean:241`) | UV correction terms add the discrepancy between Boolean evaluation and noisy-input polynomial evaluation at the bucket position. Optional absent positions contribute zero, including the empty-grid boundary. |
| Equation(4), G(3), p.17 | `Params.G3` (`Polys.lean:253`); `Params.G3_eval_of_scaled` (`Polys.lean:389`) | One tensor half and U use the precomputed scaled copy; the other half and V are unscaled. This realizes flag*G2 while keeping private degree <=2. Dv6/Dv10/Dv15. |
| G(4), p.16; degree calculation p.17 | `Params.G4struct` (`Polys.lean:265`); `Params.G4` (`Polys.lean:277`); `Params.G4_degrees` (`Polys.lean:343`) | Sum G3 over repetitions and explicitly rename structured coordinates to Fin public/private coordinates. No public error multiplier is introduced. Dv10 gives degree d in public variables and two in private variables. |
| 1SdSamp, p.16 | `Params.noiseValue` (`Samplers.lean:45`); `Params.errSet` (`Samplers.lean:58`); `Params.badSet` (`Samplers.lean:69`); `Params.oneFlag` (`Samplers.lean:82`); `Params.corr` (`Samplers.lean:97`); `Params.lpnVector` (`Samplers.lean:116`); `Params.oneSd` (`Samplers.lean:140`) | Exact noise, representation-dependent BAD, all three success conditions, A*s+e+sigma, and deterministic sparse correction factors follow the algorithm. Dv3 rounded thresholds/transposed matrix; Dv4 locality; Dv15 finite layout. |
| SdSamp', pp.15-16 | `Params.firstGood` (`Samplers.lean:186`); `Params.packSeed` (`Samplers.lean:196`); `Params.sdCore` (`Samplers.lean:236`); `Params.sdSampFull` (`Samplers.lean:292`); `Params.sdSamp'` (`Samplers.lean:302`) | First successful repetition has selected flag one; others zero. Private seed stores flags and scaled/unscaled copies; error is true exactly if no repetition succeeds. All output data comes from one exact joint draw. Dv15/Dv17. Empty repetition families at kappa=0 are total. |
| IdSamp' and Eval', pp.15-17 | `Params.idCore` (`Samplers.lean:274`); `Params.idSamp'` (`Samplers.lean:283`); `Params.eval'` (`Samplers.lean:313`); `jlsSPRG_raw` (`Samplers.lean:353`) | Exact index draw contains underlying generator index draw, independent buckets, and public matrix. Eval' evaluates G4 and recognizes the field value one; correctness proves this is Boolean on sampled seeds. Raw publishes the fixed arbitrary modulus schedule. Dv8/Dv9/Dv17/Dv18. |
| Correctness, Equations(3)-(4), pp.16-17 | `Params.firstGood_none_iff` (`Correctness.lean:56`); `Params.oneSd_factors_mul` (`Correctness.lean:154`); `Params.G1_eval_of_good` (`Correctness.lean:171`); `Params.G2_eval_of_flag` (`Correctness.lean:201`); `Params.G4_eval_sdCore` (`Correctness.lean:219`); `Params.G4_eval_eq` (`Correctness.lean:232`); `Params.eval'_correct` (`Correctness.lean:244`); `jls_hasComplexity` (`Correctness.lean:259`) | Specialized reader glue proves good-output correction, sparse reconstruction, unique selected flags, packed coordinates, and exact sampled-seed correctness. All pp and all kappa, including zero. Dv3/Dv4/Dv6/Dv10/Dv15/Dv17/Dv18. |
| Claim4.1, p.18 | `E0` (`Stretch.lean:51`); `Params.seedBitsAt` (`Stretch.lean:64`); `Params.seedBitsAt_le` (`Stretch.lean:82`); `jls_seedBits_le` (`Stretch.lean:103`); `jls_hasPolyStretch` (`Stretch.lean:122`) | Explicit sufficient threshold `floor(max(10/delta,5/(tau-1)))+1`; uniform fifth-power payload estimate and eventual power stretch. Dv1/Dv3/Dv5/Dv18; SP-W1 rational delta. The estimate is uniform in all pp because lengths depend only on kappa. |
| Claim4.2, pp.19-21 | `Params.Cond1` (`Claim42.lean:45`); `Params.Cond2` (`Claim42.lean:58`); `Params.Cond3` (`Claim42.lean:73`); `Params.errProb` (`Claim42.lean:93`); `Params.badSet_expect_le` (`Claim42.lean:114`); `Params.cond1_prob_le` (`Claim42.lean:126`); `Params.errProb_le_decomposition` (`Claim42.lean:139`); `Params.claim42` (`Claim42.lean:155`) | Exact error probability at every pp/kappa, strict integer Markov denominator Gamma+1, shared capacity failure, conditional-noise independence, and common eventual threshold before forall pp. Dv3/Dv7. No false unconditional independence of index-dependent events is asserted. |
| Bucket tail estimates used in Claim4.2, p.20 | `Internal.binomial_bound` (`Claim42/Load.lean:54`); `Internal.bucket_tail` (`Claim42/Load.lean:67`); `Internal.some_bucket_tail` (`Claim42/Load.lean:78`); `Internal.full_bucket_tail` (`Claim42/Load.lean:88`); `Internal.some_full_bucket_tail` (`Claim42/Load.lean:98`) | Fixed bad set independent of uniform buckets. Load >t uses the exact stronger t+1 witness bound, handles t=0, assumes B nonzero. Existing public union-bound APIs and factorial/exponential facts are reused; no generic probability calculus is copied. |
| H0-H3 / Proposition4.1, pp.18-19 | `HybridStage` (`Hybrids.lean:43`); `Params.publicSeed` (`Hybrids.lean:53`); `Params.hyb` (`Hybrids.lean:112`); `Params.hyb_real_eq_raw` (`Hybrids.lean:142`); `Params.hyb_random_eq_raw` (`Hybrids.lean:148`); `Params.hyb_real_prg_le` (`Hybrids.lean:176`); `Params.hyb_uniform_random_le` (`Hybrids.lean:184`) | Same exact index/seed laws; H1/H2 clean the error flag, H1 uses G(sigma), H2/H3 use uniform tail. Each statistical step costs exact errProb. Dv7/Dv8/Dv18. |
| Semantic chain-start correspondence; Lemma4.2, p.19 | `Params.hyb_prg_accept_eq_chain_zero` (`Hybrids.lean:157`); `Params.hyb_uniform_accept_eq_chain_zero` (`Hybrids.lean:167`) | SP-W2 replaces the two false equalities of free oracle programs by equalities of acceptance probabilities. At chain index zero, an extra uniform public-vector query is unused; it changes the query tree while leaving acceptance unchanged. The probability-level statements suffice through advantage_eq. No algorithm or headline inequality changes. |
| Di chain / Lemma4.2, p.19 | `Params.chainPublic` (`Hybrids.lean:69`); `Params.chainGame` (`Hybrids.lean:86`); `lemma42` (`Security.lean:62`) | First i public LPN vectors become uniform; both real and uniform tails are represented. The direct endpoint lemma costs kappa LPN and one PRG advantage. Dv8 retains independent published buckets; Dv12 hardwires averages; Dv14 every-realiser typed statement. |
| LPN hops / Lemma4.2, p.19 | `Params.LPNChal` (`Reductions/LPN.lean:51`); `Params.lpnEnc` (`Reductions/LPN.lean:68`); `Params.LPNAdvice` (`Reductions/LPN.lean:135`); `Params.encLPNAdvice` (`Reductions/LPN.lean:243`); `Params.lpnPre` (`Reductions/LPN.lean:321`); `Params.lpnRed` (`Reductions/LPN.lean:353`); `Params.lpn_hop` (`Reductions/LPN.lean:398`) | Exact canonical LWE challenge remains unaltered. Advice fixes hop/index/buckets/draw/tail/uniforms, with inhabited sentinel at zero; matrix stays challenge-supplied. Deterministic guarded preprocessing calls A with required coin prefix. One advice family before every realiser/all kappa. Dv3/Dv8/Dv9/Dv12/Dv14/Dv15/Dv16. Coarse explicit advice-bound coefficient 4096 is disclosed. |
| PRG hop / Lemma4.2, p.19 | `Params.PRGChal` (`Reductions/PRG.lean:54`); `Params.prgEnc` (`Reductions/PRG.lean:83`); `Params.PRGAdvice` (`Reductions/PRG.lean:93`); `Params.encPRGAdvice` (`Reductions/PRG.lean:206`); `Params.prgPre` (`Reductions/PRG.lean:248`); `Params.prgRed` (`Reductions/PRG.lean:271`); `Params.prg_hop` (`Reductions/PRG.lean:338`) | Canonical G challenge; advice fixes buckets/matrix/uniform vectors, retaining challenged Boolean index/output. Guarded preprocessing neither samples nor calls G.eval. All-zero advice inhabits every parameter. Bound coefficient 100 is explicit. Dv8/Dv9/Dv12/Dv14/Dv15/Dv16. |
| Proposition4.1, pp.18-19 | `prop41` (`Security.lean:84`) | For each P/pi/A, exists advice families, then forall BL/BG realisers, then forall kappa: `adv <=2*kappa*ownLPNadv(ell)+Gadv(n)+2*errProb`. Dv12 selects a largest LPN gap among both chains; Dv16 shared layout-length predicate is weaker, so the universal-realiser bound is stronger. |
| Theorem4.1, p.11; security consequence p.18 | `jls_secure` (`Security.lean:102`); `jls_subexpSmall` (`Security.lean:115`); `jls_subexpSecure` (`Security.lean:129`); `theorem41` (`Security.lean:141`); `theorem41_subexp` (`Security.lean:153`) | Raw results assume realisability and own-family LPN. Fixed exponent is `min(E*cL,min(E*D*cG,1))/2`, with positive common assumption exponents before all NUPPT. Dv3/Dv13/Dv14/Dv18. Degree d/2 and stretch match the settled statement. |
| Theorem4.1 existence, p.11 | `exists_sprg_raw` (`Security.lean:167`); `exists_sprg_raw_subexp` (`Security.lean:184`) | Choose sufficiently large E from the supplied G/R/rational-delta data, for arbitrary supplied prime schedule. LPN and realisability range only over this E-indexed construction family. Dv1/Dv3/Dv13/Dv14/Dv18; SP-W1. Narrowing raw realisability to these Params is explicitly disclosed. |
| Phase B honest efficiency targets, Defs.3.1-3.3 p.10 / construction pp.15-17 | `Params.evalTarget` (`Targets.lean:72`); `Params.qGenTarget` (`Targets.lean:91`); `Params.coreTarget` (`Targets.lean:116`); `Params.drawSamplerTarget` (`Targets.lean:179`); `Params.lpnSamplerTarget` (`Targets.lean:197`); `Params.Targets` (`Targets.lean:216`) | T1/T2 each choose one map before all kappa/pp. T3 and T5 are shared halves on the same complete draw. T6 chooses one U/c/f before all dimensions and prime schedules. Dv17/Dv18. Targets are named Props with proved readers and the explicit unproved-Phase-B notice; no target truth is asserted. |
| Phase B reduction target / Lemma4.2 p.19 | `Params.lpnPreTarget` (`Targets.lean:139`); `Params.prgPreTarget` (`Targets.lean:154`); `Params.LPNRealizable` (`Reductions/LPN.lean:413`); `Params.PRGRealizable` (`Reductions/PRG.lean:288`); `Params.Realizable` (`Security.lean:45`); `Params.realizable_of_targets` (`Targets.lean:232`) | One preprocessing map precedes all schedules/advice/challenges. Shared RealizesOn is reused unchanged. Its public preTarget theorem supplies realisers conditionally on T4; no machine is constructed. Dv14/Dv16. |
| Primitive assembly / conditional Theorem4.1 | `Params.lpnFamily` (`Targets.lean:279`); `jlsSPRG` (`Targets.lean:301`); `Params.hasComplexityEff_of_target` (`Targets.lean:293`); `theorem41_of_targets` (`Targets.lean:319`); `exists_sprg_of_targets` (`Targets.lean:333`); `exists_sprg_of_targets_subexp` (`Targets.lean:349`) | T1, T3+T5, and T6 fill all mandatory fields; T2 supplies actual polynomial generation. Only these target assemblies construct new SPRG/LPNFamily values. Efficient existence keeps `forall P, P.Targets`; raw existence uses its own E-indexed realisability. Dv18. |

### Archived M0 rule15 table

| Primitive / algorithm layer | Exact uniform efficiency fields | Raw layer and actual sampler law | Construction from targets |
| --- | --- | --- | --- |
| `BoolPRG` (`BoolPRG.lean:50`) | `eval_eff` (`:94`) chooses one `PolyTimeComputable` string map before all `n`, indices, and Boolean seeds. `idSamp_eff` (`:99`) is the shared `CoinSampling.SamplesEfficiently` contract for its supplied `IdDraw`, `encIdDraw`, `encIdx`, and `idCore`. | The input primitive itself carries the algorithm data. `BoolPRG.idSamp` (`:124`) is exactly the pushforward of one uniform `IdDraw` through `idCore`, with proved reader `idSamp_eq` (`:128`). It is not a disconnected arbitrary sampler field. | This job assumes a `BoolPRG`; it constructs no new value of that type. Its evaluator and sampler witnesses are mandatory input data. |
| `LPNFamily` (`LPN.lean:400`) | `sample_eff` (`:402`) is shared `SamplesEfficiently` for the exact joint matrix/secret/noise draw, parameter word `sampleWord`, draw/output encodings, and `sampleCore`. | `LPNFamily.Raw` (`:79`) fixes samples, public modulus, exact noise denominator, polynomial bounds, canonical `toLWE` (`:136`), `adv` (`:166`), and `Assumption` (`:175`). Its complete draw is `Raw.Draw` (`:189`), its actual core is `sampleCore` (`:306`), and `sampleLaw` (`:317`) is the exact one-draw pushforward. | `Params.lpnFamily` (`Targets.lean:279`) extends `P.lpnFamily_raw pi` with the field furnished by `lpnSamplerEfficient_of_target` (`:269`), from T6. `lpnFamily_toRaw` (`:285`) is proved `rfl`. |
| `SPRG` (`Defs.lean:397`) | `eval_eff` (`:398`) is `toRaw.EvalEfficient`; `idSamp_eff` (`:399`) and `sdSamp_eff` (`:402`) are shared `SamplesEfficiently` contracts on the exact raw index and seed draws and their cores. | `SPRG.Raw` (`:97`) stores all honest algorithm data, explicit finite-coordinate equivalences, and encodings. `Raw.idSamp` (`:179`) and `Raw.sdSamp` (`:188`) are derived exact uniform-draw pushforwards. `Raw.EvalEfficient` (`:318`) chooses one map before all parameters, with the public modulus in its input. | `jlsSPRG` (`Targets.lean:301`) extends `jlsSPRG_raw P pi`; T1 supplies `eval_eff` via `evalEfficient_of_target` (`:238`), T3 and T5 supply both sampler fields via `idSampEfficient_of_targets` (`:245`) and `sdSampEfficient_of_targets` (`:257`). `jlsSPRG_toRaw` (`:308`) is proved `rfl`. |

### Archived M0 target-selection table

| Field / consequence | Target witness selected |
| --- | --- |
| sPRG `eval_eff` | `hT.1` (T1) |
| sPRG `idSamp_eff`, `sdSamp_eff` | `hT.2.2.1` (T3) and `hT.2.2.2.2.1` (T5) |
| LPN `sample_eff` | `hT.2.2.2.2.2` (T6) |
| `HasComplexityEff P.d 2` | T2, through `hasComplexityEff_of_target` (`Targets.lean:293`) |
| reduction realisers | T4, through `realizable_of_targets` (`Targets.lean:232`) |

### Archived M0 nonvacuity table

| Object | Source witness and finite-coordinate data | Zero/off-image behavior and scope |
| --- | --- | --- |
| `PrimeSchedule` (`Defs.lean:72`) | `PrimeSchedule.nonempty` (`:82`) is proved using existing `Nat.exists_prime_lt_and_le_two_mul`. | At `kappa=0`, `p=2` is admitted by the weak interval endpoints. This is an existence proof, not a prime algorithm. `Classical.choose` occurs only in this non-vacuity proof (`:86`), outside encodings, draw equivalences, preprocessing maps, and targets. |
| `P.LPNAdvice pi L` (`Reductions/LPN.lean:135`) | `instLPNAdviceNonempty` (`:235`) maps the component product through `lpnAdviceProductEquiv.symm`. `lpnAdviceEquiv` (`:197`) gives explicit `Fin (lpnAdviceCard pi L)` coordinates; `instLPNAdviceFintype` (`:226`) transports from them. | The hop component is `Fin (kappaOf L + 1)`, so the sentinel remains nonempty at zero and at independent dimensions off the schedule image. Boolean indices are nonempty by the input `BoolPRG`; bucket/noise widths are positive; function products with empty domains remain nonempty. The hop inequality is required only when its value is below `kappa`. `lpnPre` (`:321`) returns `[]` off image. |
| `P.PRGAdvice pi N` (`Reductions/PRG.lean:93`) | `instPRGAdviceInhabited` (`:187`) supplies all-zero buckets, matrix, and public vectors, using `P.B_pos`. `prgAdviceEquiv` (`:156`) is an explicit coordinate equivalence and `instPRGAdviceFintype` (`:178`) transports finiteness. | Valid for every `N`, including zero and off-image dimensions. No choice is used to obtain the explicit default. `prgPre` (`:248`) returns `[]` off image. |
| Input Boolean indices and index draws | `BoolPRG.idxNonempty` (`BoolPRG.lean:60`) and `idDrawNonempty` (`:70`) are mandatory supplied fields; their instances are at `:105`/`:108`. `idxEquiv` (`:56`) and `idDrawEquiv` (`:66`) are explicit data. | Honest Boolean index sampling never samples an empty type. These hypotheses describe the input primitive rather than an additional construction assumption. |
| Generic sPRG index/index draw/seed draw | `SPRG.Raw.idxNonempty`, `idDrawNonempty`, `sdDrawNonempty` (`Defs.lean:104`, `:109`, `:129`) are mandatory raw data; the public instances are at `:143`, `:145`, `:149`. | Every exact uniform law has a nonempty draw; every raw family includes explicit cardinal/equivalence data (`:105`/`:106`, `:110`/`:111`, `:130`/`:131`). |
| Construction's exact draws | `Params.IdDraw`, `Params.Draw` (`Encoding.lean:135`, `:147`) are concrete finite products; `idDrawEquiv`, `drawEquiv` (`:214`, `:232`) compose supplied Boolean and canonical modular/function/product equivalences. | Empty vector domains at zero do not make the function type empty. Positive bucket/noise widths and nonzero prime modulus provide nonempty codomains. |
| LPN exact joint draw | `LPNFamily.Raw.Draw` (`LPN.lean:189`) is the concrete matrix/secret/noise-seed product. `drawEquiv` (`:278`) gives explicit `Fin (drawCard ell)` coordinates; nonzero modulus and noise denominator instances are at `:101`/`:102`. | It remains nonempty when the secret dimension or sample count is zero. It is one product draw, not an illicit product fair-coin sampler construction. |
| Shared realiser predicate | Existing `Complexity.NUPPT.realizesOn_self` and `realizesOn_self_take` (`TCSlib/Cryptography/Asymptotic/Realization.lean:167`, `:179`) establish generic satisfiability, including the required coin-prefix shape. | These do **not** by themselves realize the actual LPN/PRG preprocessing. Actual reduction realisers are obtained conditionally from T4 by the existing `exists_realizesOn_of_preTarget` (`:220`) through the M0 `realizable_of_targets` obligation. |



## Scoped overlap evidence

Seven public component/abstract-core pairs give14 search runs. No StructuredSeed
module is directly imported by these goals. These are recorded mathematical
components/cores, not claims that a full construction-specific theorem was already
public. Current outcomes:6 NO_CLOSING_PROOF,6 PARTIAL_NOT_PROOF and2
DIAGNOSTIC_FAILURE (the corrected subexpSmall v2 bounded/time-budget diagnostics).
The invalid original subexpSmall pair inferred a real size before ell/n and is
retained locally, excluded from these14runs. Its v2 explicitly types sizes as Nat.
Partial suggestions, bounded diagnostics and no-hits are not proofs or global
lemma-absence results. Seven active paired records and name/shape outputs are in the local raw archive. No raw search inputs, transcripts or preparation packets are copied into this checkpoint.

## Compact delivery and retained raw authority

SPRG-C0-F01 limits the new M5 checkpoint to compact material: at most20MB and
50,000 inserted lines outside src/ and patches/. New delivery includes only the
compact report and nine actual build/decls2/axiom/freeze/lint result files.
Host numbers and qualifications are in this report; raw bindings stay local. Full raw probes/logs/tools,
preparation packets, unrun inputs and every saved raw step remain local only.
Existing delivered legacy files are retained; nothing is deleted to hide history.
Budget audit: Outside src/ and patches/: 1.364276 MB (1364276 charged bytes), 1520 inserted UTF-8 lines. Limits: 20 MB and 50,000 inserted lines. Legacy unchanged files are retained and excluded from this incremental accounting.

Complete raw evidence archive (LOCAL ONLY): `/private/tmp/io-sprg-raw-evidence/M5-evidence.tar.gz`.
Archive SHA-256: `a2250d9a778f407f1a40245f81e6d445cf0922497ecd88a2c2436e35fa2c91b6`. Capture scope/manifest:
Full raw folder: `/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange/evidence`. The complete folder was captured after the M5 check suite and before this report/publication; archive size72,539,641 bytes. It stays local and will be sent only if the gate requests it.. The archive is closed and its digest was computed after tar completed.
No raw archive or LOCAL-ONLY preparation directory is added to compact delivery.

The complete historical M4 report, including M0–M3 records and all fidelity,
Rule15, target-selection, non-vacuity, Phase B, StatementChanges and design
judgments, remains at exchange commit
`33e944e359da71e42c15f922513b4da2f217cad4`, path
`inbox/fills/io-sprg/evidence/REPORT.md`; captured report SHA-256
`919787bba1e8458bf5439a5c020c3a2df83d17077345fa3c647b151601c6dc3b`. M4 source was
`428c7eb117b51fe512348f226284df247e98c00c`. Its actual delivery record reports
7,859 exact committed payload paths, no SHA mismatches and a successful non-force
push. Its old report's publication-pending wording predates that push and has
historical scope. The preserved published M4 delivery record is `evidence/delivery/M4.json` at the next local snapshot; the exchange commit/path above is the historical authority.

Both earlier process breaches stay disclosed: the extra research descendant was
interrupted after exceeding the two-subagent limit (no-mutation account based on
task reports, not independent process audit), and wrappers93883/93983 overlapped
15:07:45–15:07:48UTC, followed by child termination/prior release15:08:34UTC.
Their unchanged correction records and full raw histories remain in the local
archive and historical delivery. Whole-history seriality remains false/max2;
only a freshly verified post-correction tagged suffix may be called serial.
Wrapper records do not prove a global host process cap or full child history.

## Statements, Phase B and remaining gates

All670 M0 global FQNs/kinds/headers/pre-sketch prose and the explicit93 moves must
remain unchanged under the fresh bound guard; M5 changes proof bodies only.
Fresh global freeze matches every committed owner SHA; all 670 original headers/prose preserved; source diff adds only M5 proof bodies. SP-W1 rationalδ, SP-W2 acceptance equalities only,
SP-W3 growing seeds, every-realiser/all-κ quantifiers, canonical assumption
encodings and mandatory primitive efficiency fields remain fixed. T6 still asks
for ONE sampler/map witness before every schedule, never separate per-π witnesses.
No Phase B target is proved by assembling these conditional theorems.

M0's complete stored-root/kernel-type/Rule10 matrix remains historical until all
fresh final gates. Selected M5 source theorem prints do not replace the complete
stored-constant graph, exact public print comparison, full frozen kernel types,
all four required variants with conservative closures, every paired reader
control, request/runtime masks/chunks/EOF and exact source/import bindings.
Final dynamic inventory must include every new owner. Current full Rule10, stored census and frozen kernel-type checks are pending final M6 source; no fresh canonical final result is claimed here.

Continue M6, then complete the fresh final gate suite and exact patch replay,
PDF-all-trees and manifest verification; no new bundle is delivered under SPRG-C0-F01. Paper SHA-256 remains
`bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d`;
no PDF is copied, committed or delivered. The external report binding carries
this report's SHA; no circular self-hash or future push hash is invented.

Open questions: none awaiting Seyoon. SP-W1–SP-W3 and the slot-check authorization are settled. Phase B targets remain explicit obligations. Modular M4 splits and the strict M5 exponent budget are the retained judgment calls; M5 needs no further source split (Security494 lines).
