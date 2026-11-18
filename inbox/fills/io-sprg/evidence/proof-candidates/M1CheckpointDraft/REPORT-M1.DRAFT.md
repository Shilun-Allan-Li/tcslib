# io-sprg Phase A — M1 algebraic correctness checkpoint

M1 proof work and local checks are complete at `19dde91afc384656e7e47cb018057e088d4ded0a`. All 100 original bodies in
this checkpoint and three new theorem-only helpers are filled, with 103 checked step
records. All 23 owned modules pass a fresh full build at this source head. Across
11 affected owners, 297 public theorem axiom prints contain only standard axioms.
Forty-six original theorem bodies remain for M2–M6. T1–T6 remain named, unproved
Phase B obligations. This is an M1 checkpoint, not final Phase A completion.

M0 remains frozen at `d10a560b34d58919bc1a5206ce66a444613f94c7`; its report and delivery
are preserved under `evidence/checkpoints/M0/`. Current static checks pass as detailed
below. M1 packaging/push receipts are bound by the root delivery metadata. The final
full kernel census, transitive sorry graph and complete Rule10 matrix have not been
rerun for M1 and remain final-completion gates; the M0 results are historical only.

## Bases, scope and milestones

- Lean base: `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`.
- Records: `dbea2807532392781304e004715f3b0190025f5e`.
- Host inputs: `bc9d982b83cb35ea351e2fb373752e8688945b1c`.
- Rule10 provenance: `2467bc3befdad8472b1f359337bf3a203e3651e1`.
- M1 source head: `19dde91afc384656e7e47cb018057e088d4ded0a`.
- Source: 23 owned Lean files, 7,244 lines; existing root export import retained.
- Fresh decls2: 673 ADDED. Frozen M0 declarations: zero CHANGED/REMOVED, three helpers added.

| Milestone | Status |
| --- | --- |
| M0 statements | Complete and frozen; archived checks and payload preserved. |
| M1 algebraic correctness | Complete proof/local-check checkpoint: original100 + helpers3. |
| M2 stretch | Next: all four remaining Stretch obligations, including SP-W3 seed growth. |
| M3 Claim4.2 | Pending; common cutoff must remain before every public prime. |
| M4 reductions / prop41 | Pending; every-realizer inequalities and exact nuisance law. |
| M5 raw Theorem4.1 | Pending; conditional security/existence. |
| M6 links / assembly | Pending; early Encoding17 support is proved, target truth is not asserted. |

## Completed proof work and current checks

| Owner / group | Original bodies filled | New helpers | Public theorem prints, standard-only |
| --- | ---: | ---: | ---: |
| Raw LPN | 3 | 0 | 34 |
| Degree | 24 | 0 | 26 |
| Params | 14 | 0 | 45 |
| Basic | 0 | 2 | 2 |
| Encoding | 17 | 0 | 48 |
| Buckets | 7 | 0 | 13 |
| SparseFactor | 5 | 0 | 11 |
| Polys | 10 | 0 | 27 |
| Correctness | 18 | 1 | 19 |
| Defs | 1 | 0 | 29 |
| Samplers | 1 | 0 | 43 |
| Total | 100 | 3 | 297 |

The Defs efficiency-forgetting bridge and Samplers prime-width bound are included.
The two new Basic results specialize the actual fixed-width tagged-list code; the
new G4_seed_allOutputs theorem preserves the specific G4 witness for later T2 links.
They introduce no algorithm, sampler, machine, encoder or efficiency assumption.
Basic imports the already-used Uniform owner and adds no Mathlib root. The private
prefix-free/variable-size overlap and public append/list/vector reuse remain disclosed.

| Check | Current evidence |
| --- | --- |
| Full owner build | 23 records, rc0/errors0 in both forms; all source hashes and head match. `evidence/build/M1/all-owners/results.jsonl`. |
| Filled/remaining bodies | 103 CHECKED_PASS steps; original100 filled, original46 direct holes remain. `evidence/steps/`, `source-obligations.tsv`. |
| Owner axioms | All297 standard-only, no sorryAx; current source-hash-matched `evidence/checks/M1-*/summary.json`. |
| Headline axioms | Fresh19 prints; G4_eval_eq, jls_hasComplexity, lpnNoise_law and PrimeSchedule.nonempty are standard-only. The other15 later-phase/assembly headlines retain sorryAx. `evidence/checkpoints/M1/headline-axioms.json`. |
| Frozen declarations | M0 changed0/removed0; exactly the three new helpers. `evidence/checks/m1-final/freeze-summary.json`. |
| Static gates | decls2/style/sk15/clash rc0; 673 ADDED, zero clashes; zero new individual campaign FAIL/WARN lines against base. Campaign aggregate rc1 reflects baseline findings. `evidence/checks/m1-final/summary.json`. |
| Widths/sizes | All widths pass; 23files/7244lines; maximum file801lines and maximum width100. |
| Tagged slots | V2 audit covers1068 acquisitions; max2 retains the exact known incident. Post-correction tagged acquisitions are serial and no reservation remains active. `evidence/host/M1-final/slot-summary.json`. |

All full-build and owner-summary bindings above were read from saved root-run evidence;
this report preparation ran no Lean. Owner theorem prints are not represented as a
complete new kernel census. M0's1036 stored constants/948 public types/511 theorem
prints and265 transitive sorry dependents are not current M1 counts. The remaining
full-graph, implicit-axiom and final public-type census must be regenerated at completion.

M0's88 seal probes and96 paired controls (184 runtime probes) passed at M0. Those
runs bind the M0 source/olean environment and are retained as historical results.
The complete four-variant matrix, requests/masks/EOF attribution, controls and final
import-environment binding have not been rerun at M1. Include Basic and every later
new owned helper file in the final collectors and seals. No current M1 full-seal
success is claimed. Final replay/bundle/manifest and exchange receipts belong to the
root checkpoint packaging; they are not inferred from the M0 delivery.

## Remaining inventory and next milestone

The 46 original direct holes consist of M2:4, M3:10, M4:8, M4/M6 advice support:8,
M5:7 and M6 links:9. Seventeen Encoding support obligations are completed early.
The complete current per-body list is `source-obligations.tsv`; this source inventory
does not estimate the remaining transitive sorry graph.

The next M2 scope is ALL four remaining declarations in Stretch.lean:

- Params.seedBitsAt_le.
- jls_seedBits_eq.
- jls_seedBits_le.
- jls_hasPolyStretch, retaining eventual kappa<=seedBits and the common power bound.

No existing mathematical definition, theorem statement or target quantifier order
changed after M0. Current frozen-declaration checks preserve every existing name and
header. The rational-delta SP-W1 ruling, acceptance-level SP-W2 correspondence and
growing-seed SP-W3 predicate remain as frozen. Optional empty grids, deterministic
sparse factors, faithful canonical encodings and the uniform-prime scopes are retained.
The proposed future LPN module split is a plan, not a delivered M1 source change.

## Overlap searches and corrections

The saved-log snapshot at 2026-11-18T16:59:07.367544+00:00 contains218 searches, each with matching
saved source/log hashes: 20 closed;68 valid partial suggestions;92 completed exact
searches without a closing proof;9 clean apply no-hits;17 bounded timeouts;8 statement
elaboration errors;4 scope errors. These are per-log categories in
`overlap-log-review.tsv/json`, not a claim of mathematical theorem absence.

record_overlap.py's DIAGNOSTIC_FAILURE label covers several outcomes. Clean apply
no-hits differ from heartbeat timeouts and malformed goal statements. Failed candidate
attempts can appear before a valid final partial suggestion; rc0/errors0/sorry1 remains
partial, never a closing proof. Bounded searches use100000 heartbeats and cannot
establish absence or success. Owner proofs retain their separate unrestricted budget.
The original seven timeout rows are a historical subset; later Algebra/LPN logs are
classified individually. Source/header errors never count as completed overlap searches.

All old faulty records remain saved, with exact superseding source/log hashes in
`supersession.tsv/json`:

- Algebra_firstGood_none_iff/some_flag -> their AlgebraV2 names, both modes. Remove
  the unnecessary BigOperators scope opening rather than adding an unused import.
- BucketsSparse_sparseFactor_mul and sparseFactor_mul_of_card_le -> the respective
  BucketsSparseV2 names; Algebra_oneSd_factors_mul -> AlgebraMatrixV2_oneSd_factors_mul.
  Explicit Matrix annotations repair the HMul goal errors. New exact runs do not
  close; new apply runs give partial suggestions. Actual SparseFactor source proofs
  separately have standard11 owner prints.
- Algebra_G4_eval_eq -> AlgebraSupportV2_G4_eval_eq, both modes. The old Type* binders
  violated the Type0 OracleSpec/OracleComp API. The corrected finite-construction
  Type0 goals elaborate but BOTH searches time out; this is not a no-hit result.

Other corrected SupportV2 goals were used directly; no older executed errors are
claimed for them. eval'_correct and Params.G4_seed_allOutputs have clean exact
nonclosure/partial apply outcomes; the expanded jls_hasComplexity goal closes by
existing witness logic. The bridge goals import no owned modules and abstract only
relevant reader predicates or the actual prime upper-width field. All library
self-hit exclusions and public API reuse remain recorded alongside the probes.

## Host/process history and qualifications

The whole-job two-subagent limit was breached when a child started a third research
descendant. Root interrupted it and prohibited further spawning/resumption. Reported
activity was source reading, rg and temporary notes, with no reported Lean/Lake/cache/
push/implementation mutation. This is task-context reporting, not an independent
process audit; duration was not established and is not characterized as brief.
See `evidence/host/team-limit-correction.json` and the archived M0 disclosure.

During M1 root also overlapped Params_B_pos apply with step029's owner check after
printing only exec_command.output and losing an ongoing session_id. The recorded
search runner93880/wrapper93883/child93887 overlaps owner wrapper93983 during the
confirmed15:07:45–15:07:48UTC interval. Root sent SIGTERM only to the recorded own
child; the search wrapper release is recorded at15:08:34UTC. The correction is to
preserve full session metadata, poll running sessions, bound diagnostic searches,
and start no new Lean until the existing runner exits. Exact facts are in
`evidence/host/search-process-correction.json`; no wider child-process history is inferred.

The fresh tagged-slot audit preserves that violation:1068 acquisitions, maximum2,
with299 post-correction acquisitions serial, maximum1 and no active reservation at
its snapshot. It audits tagged wrapper reservations, not all host jobs, actual
simultaneous child counts or a complete process history. It does not erase the earlier
violation or justify an unqualified whole-job seriality claim. Its source/log hashes
and REAP qualifications are in `evidence/host/M1-final/`.

The verified source remains jls26.pdf with SHA-256
`bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d`, read in place only.
The PDF is not copied or delivered. M0's delayed memory-preflight and pinned tool/cache
provenance remain historical facts. The job retains the pinned slot wrapper/tag.
This preparation used source/evidence reads and temporary writes only, with no
Lean/git/cache command, source edit, spawn, or active/archived REPORT overwrite.

## Preserved fidelity, Rule15 and non-vacuity tables

The four tables below are reproduced VERBATIM from `evidence/checkpoints/M0/REPORT.md`.
Their source locations are explicitly FROZEN M0 anchors, not current M1 line numbers.
Their mathematical contracts and deviations remain unchanged. The current declaration
identity appendix resolves present M1 source locations, including shorthand fields.
`archived-table-bindings.json` records each original range and exact table hash.

Rule15 remains mandatory: Raw bundles claim no efficiency; BoolPRG supplies its
mandatory witnesses; efficient LPNFamily/SPRG values are constructed only through
conditional targets. T3/T5 concern the SAME complete draw. T6 selects one U/coin
polynomial/core before every dimension and prime schedule. No target is asserted true,
no product fair-coin sampler is built, and no Phase B efficiency proof is attempted.

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


## M1 theorem-only additions to the fidelity inventory

Basic's two fixed-width tagged-list results are shared mathematical encoding glue,
not additional paper theorems. G4_seed_allOutputs joins the exact algebraic/Boolean
support facts and retains the specific G4 witness. Their current anchors are in the
appendix. The pre-M0 SP-W1/SP-W2/SP-W3 rulings and all Dv1–Dv18 disclosures remain in
the archived report and route records; this checkpoint introduces no new assumption,
algorithm or changed binding statement.

The target definitions below are also reproduced from the archive; Targets.lean is
byte-identical to its frozen M0 source. They remain unproved Phase B propositions.
Their conditional M6 bridge theorems are among the remaining named obligations.

## Phase B target statements (unproved)

These are the exact frozen definitions, with parameters in their enclosing Params namespace.

### T1

```lean
def evalTarget (P : Params) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ κ (pp : PrimeParam κ) (I : P.Idx' κ pp) (sd : P.Seed κ pp),
      f (NUPPT.advInput κ (pairEncode pp.enc
        (pairEncode (P.encIdx' κ pp I) (P.encSeed' κ pp sd)))) =
          List.ofFn (P.eval' κ pp I sd)
```

### T2

```lean
def qGenTarget (P : Params) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ κ (pp : PrimeParam κ) (I : P.Idx' κ pp) (j : Fin (P.m κ)),
      ∃ ts : PolyTerms (Fin (P.pubLen κ) ⊕ Fin (P.privLen κ)) (ZMod pp.p),
        f (NUPPT.advInput κ (pairEncode pp.enc
          (pairEncode (P.encIdx' κ pp I) (PolyTerms.encFin j)))) =
            PolyTerms.encTerms (fun z => Candidates.natToList (κ + 1) z.val)
              (fun v => PolyTerms.encFin (finSumFinEquiv v)) ts ∧
        PolyTerms.denote ts = P.G4 κ pp I j
```

### T3

```lean
def coreTarget (P : Params) : Prop :=
  CoreComputable (P := PrimeParam)
      (fun κ pp => P.idWord κ pp) (fun κ pp => P.encIdDraw κ pp)
      (fun κ pp => P.encIdx' κ pp) (fun κ pp => P.idCore κ pp) ∧
    CoreComputable (P := P.SdParam)
      (fun κ q => P.sdWord κ q) (fun κ q => P.encDraw κ q.1)
      (fun κ q => P.encSeed' κ q.1)
      (fun κ q d => (P.sdCore κ q.1 q.2 d).seed)
```

### T4

```lean
def lpnPreTarget (P : Params) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ (π : PrimeSchedule) L (ω : P.LPNAdvice π L) (x : P.LPNChal π L),
      f (pairEncode (P.encLPNAdvice π L ω) (P.lpnEnc π L x)) = P.lpnPre π L ω x

def prgPreTarget (P : Params) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ (π : PrimeSchedule) N (ω : P.PRGAdvice π N) (x : P.PRGChal N),
      f (pairEncode (P.encPRGAdvice π N ω) (P.prgEnc N x)) = P.prgPre π N ω x

def ReductionTargets (P : Params) : Prop :=
  P.lpnPreTarget ∧ P.prgPreTarget
```

### T5

```lean
def drawSamplerTarget (P : Params) : Prop :=
  DrawSamplable (P := PrimeParam)
      (fun κ pp => P.idWord κ pp) (fun κ pp => P.encIdDraw κ pp) ∧
    DrawSamplable (P := P.SdParam)
      (fun κ q => P.sdWord κ q) (fun κ q => P.encDraw κ q.1)
```

### T6

```lean
def lpnSamplerTarget (P : Params) : Prop :=
  SamplesEfficiently (P := fun _ => PrimeSchedule)
    (fun L π => (P.lpnFamily_raw π).sampleWord L)
    (fun L π => (P.lpnFamily_raw π).encDraw L)
    (fun L π => (P.lpnFamily_raw π).encSample L)
    (fun L π => (P.lpnFamily_raw π).sampleCore L)
```

### Conjunction

```lean
def Targets (P : Params) : Prop :=
  P.evalTarget ∧ P.qGenTarget ∧ P.coreTarget ∧ P.ReductionTargets ∧
    P.drawSamplerTarget ∧ P.lpnSamplerTarget
```


## Current declaration anchors for the archived tables
The tables above preserve M0 bytes and therefore retain HISTORICAL line references.
This appendix gives current M1 anchors by declaration identity. The adjacent TSV
contains every explicit owned declaration and structure field; generated constructors,
recursors and inherited fields remain represented by their owning structure. This is
a source anchor index, not a replacement for the final typed kernel census.

| Current full name (area prefix omitted) | M1 source anchor |
| --- | --- |
| `BoolPRG` | `BoolPRG.lean:50` |
| `BoolPRG.HasStretch` | `BoolPRG.lean:207` |
| `BoolPRG.IdDraw` | `BoolPRG.lean:62` |
| `BoolPRG.Idx` | `BoolPRG.lean:52` |
| `BoolPRG.MultilinearRep` | `BoolPRG.lean:217` |
| `BoolPRG.MultilinearRep.HasLocality` | `BoolPRG.lean:234` |
| `BoolPRG.MultilinearRep.TermsEfficient` | `BoolPRG.lean:245` |
| `BoolPRG.MultilinearRep.eval_poly` | `BoolPRG.lean:225` |
| `BoolPRG.MultilinearRep.poly` | `BoolPRG.lean:219` |
| `BoolPRG.MultilinearRep.poly_mem_restrictDegree` | `BoolPRG.lean:221` |
| `BoolPRG.MultilinearRep.totalDegree_poly_le` | `BoolPRG.lean:223` |
| `BoolPRG.Secure` | `BoolPRG.lean:191` |
| `BoolPRG.SubexpSecure` | `BoolPRG.lean:199` |
| `BoolPRG.encIdDraw` | `BoolPRG.lean:74` |
| `BoolPRG.encIdDraw_injective` | `BoolPRG.lean:76` |
| `BoolPRG.encIdx` | `BoolPRG.lean:78` |
| `BoolPRG.encIdx_injective` | `BoolPRG.lean:80` |
| `BoolPRG.encIdx_length_le` | `BoolPRG.lean:84` |
| `BoolPRG.eval` | `BoolPRG.lean:92` |
| `BoolPRG.eval_eff` | `BoolPRG.lean:94` |
| `BoolPRG.game` | `BoolPRG.lean:162` |
| `BoolPRG.idCore` | `BoolPRG.lean:72` |
| `BoolPRG.idDrawCard` | `BoolPRG.lean:64` |
| `BoolPRG.idDrawEquiv` | `BoolPRG.lean:66` |
| `BoolPRG.idDrawFintype` | `BoolPRG.lean:68` |
| `BoolPRG.idDrawNonempty` | `BoolPRG.lean:70` |
| `BoolPRG.idSamp` | `BoolPRG.lean:124` |
| `BoolPRG.idSamp_eff` | `BoolPRG.lean:99` |
| `BoolPRG.idxBits` | `BoolPRG.lean:82` |
| `BoolPRG.idxCard` | `BoolPRG.lean:54` |
| `BoolPRG.idxEquiv` | `BoolPRG.lean:56` |
| `BoolPRG.idxFintype` | `BoolPRG.lean:58` |
| `BoolPRG.idxNonempty` | `BoolPRG.lean:60` |
| `BoolPRG.outBound` | `BoolPRG.lean:88` |
| `BoolPRG.outLen` | `BoolPRG.lean:86` |
| `BoolPRG.outLen_le` | `BoolPRG.lean:90` |
| `Buckets.bucket` | `Buckets.lean:52` |
| `Buckets.bucketMatrix` | `Buckets.lean:192` |
| `Buckets.indexMap` | `Buckets.lean:87` |
| `Buckets.load` | `Buckets.lean:61` |
| `Buckets.rank` | `Buckets.lean:77` |
| `E0` | `Stretch.lean:51` |
| `HybridStage` | `Hybrids.lean:43` |
| `Internal.binomial_bound` | `Claim42/Load.lean:54` |
| `Internal.bucket_tail` | `Claim42/Load.lean:67` |
| `Internal.encodeList_injective_of_fixedWidth` | `Basic.lean:49` |
| `Internal.encodeList_length_of_fixedWidth` | `Basic.lean:82` |
| `Internal.full_bucket_tail` | `Claim42/Load.lean:88` |
| `Internal.some_bucket_tail` | `Claim42/Load.lean:78` |
| `Internal.some_full_bucket_tail` | `Claim42/Load.lean:98` |
| `LPNFamily` | `LPN.lean:512` |
| `LPNFamily.Raw` | `LPN.lean:120` |
| `LPNFamily.Raw.Assumption` | `LPN.lean:216` |
| `LPNFamily.Raw.Draw` | `LPN.lean:230` |
| `LPNFamily.Raw.adv` | `LPN.lean:207` |
| `LPNFamily.Raw.modulus` | `LPN.lean:124` |
| `LPNFamily.Raw.modulus_le_pow` | `LPN.lean:138` |
| `LPNFamily.Raw.modulus_prime` | `LPN.lean:128` |
| `LPNFamily.Raw.noiseDen` | `LPN.lean:126` |
| `LPNFamily.Raw.noiseDen_pos` | `LPN.lean:130` |
| `LPNFamily.Raw.residueBits` | `LPN.lean:134` |
| `LPNFamily.Raw.sampleCore` | `LPN.lean:347` |
| `LPNFamily.Raw.sampleLaw` | `LPN.lean:358` |
| `LPNFamily.Raw.samples` | `LPN.lean:122` |
| `LPNFamily.Raw.samplesBound` | `LPN.lean:132` |
| `LPNFamily.Raw.samples_le` | `LPN.lean:136` |
| `LPNFamily.Raw.toLWE` | `LPN.lean:177` |
| `LPNFamily.sample_eff` | `LPN.lean:514` |
| `Params` | `Params.lean:50` |
| `Params.B` | `Params.lean:138` |
| `Params.Cond1` | `Claim42.lean:45` |
| `Params.Cond2` | `Claim42.lean:58` |
| `Params.Cond3` | `Claim42.lean:73` |
| `Params.D` | `Params.lean:64` |
| `Params.Draw` | `Encoding.lean:148` |
| `Params.E` | `Params.lean:56` |
| `Params.G` | `Params.lean:58` |
| `Params.G1` | `Polys.lean:261` |
| `Params.G1_eval` | `Polys.lean:649` |
| `Params.G1_eval_of_good` | `Correctness.lean:253` |
| `Params.G2` | `Polys.lean:273` |
| `Params.G2_eval_of_flag` | `Correctness.lean:315` |
| `Params.G3` | `Polys.lean:285` |
| `Params.G3_eval_of_scaled` | `Polys.lean:753` |
| `Params.G4` | `Polys.lean:309` |
| `Params.G4_degrees` | `Polys.lean:541` |
| `Params.G4_eval_eq` | `Correctness.lean:413` |
| `Params.G4_eval_sdCore` | `Correctness.lean:351` |
| `Params.G4_seed_allOutputs` | `Correctness.lean:453` |
| `Params.G4struct` | `Polys.lean:297` |
| `Params.IdDraw` | `Encoding.lean:136` |
| `Params.LPNAdvice` | `Reductions/LPN.lean:135` |
| `Params.LPNAdvice.I` | `Reductions/LPN.lean:137` |
| `Params.LPNAdvice.buckets` | `Reductions/LPN.lean:138` |
| `Params.LPNAdvice.draw` | `Reductions/LPN.lean:139` |
| `Params.LPNAdvice.hop` | `Reductions/LPN.lean:136` |
| `Params.LPNAdvice.tail` | `Reductions/LPN.lean:140` |
| `Params.LPNAdvice.uniform` | `Reductions/LPN.lean:141` |
| `Params.LPNChal` | `Reductions/LPN.lean:51` |
| `Params.LPNRealizable` | `Reductions/LPN.lean:413` |
| `Params.OneSdOut.flag` | `Samplers.lean:133` |
| `Params.OneSdOut.priv` | `Samplers.lean:135` |
| `Params.OneSdOut.pub` | `Samplers.lean:134` |
| `Params.PRGAdvice` | `Reductions/PRG.lean:93` |
| `Params.PRGAdvice.buckets` | `Reductions/PRG.lean:95` |
| `Params.PRGAdvice.matrix` | `Reductions/PRG.lean:97` |
| `Params.PRGAdvice.uniform` | `Reductions/PRG.lean:100` |
| `Params.PRGChal` | `Reductions/PRG.lean:54` |
| `Params.PRGRealizable` | `Reductions/PRG.lean:288` |
| `Params.Priv` | `Params.lean:201` |
| `Params.Pub` | `Params.lean:247` |
| `Params.R` | `Params.lean:59` |
| `Params.Realizable` | `Security.lean:45` |
| `Params.SVar` | `Params.lean:180` |
| `Params.SdCoreOut.draw` | `Samplers.lean:228` |
| `Params.SdCoreOut.err` | `Samplers.lean:231` |
| `Params.SdCoreOut.first` | `Samplers.lean:230` |
| `Params.SdCoreOut.instances` | `Samplers.lean:229` |
| `Params.SdCoreOut.seed` | `Samplers.lean:232` |
| `Params.SdCoreOut.σ` | `Samplers.lean:227` |
| `Params.Seed` | `Encoding.lean:161` |
| `Params.Targets` | `Targets.lean:216` |
| `Params.W` | `Params.lean:111` |
| `Params.badSet` | `Samplers.lean:69` |
| `Params.badSet_expect_le` | `Claim42.lean:114` |
| `Params.bucketBound` | `Encoding.lean:350` |
| `Params.cap` | `Params.lean:132` |
| `Params.chainGame` | `Hybrids.lean:86` |
| `Params.chainPublic` | `Hybrids.lean:69` |
| `Params.claim42` | `Claim42.lean:155` |
| `Params.cond1_prob_le` | `Claim42.lean:126` |
| `Params.coreTarget` | `Targets.lean:116` |
| `Params.corr` | `Samplers.lean:97` |
| `Params.correctionPoly` | `Polys.lean:240` |
| `Params.d` | `Params.lean:51` |
| `Params.drawEquiv` | `Encoding.lean:233` |
| `Params.drawSamplerTarget` | `Targets.lean:179` |
| `Params.ellBound` | `Encoding.lean:332` |
| `Params.encDraw` | `Encoding.lean:309` |
| `Params.encIdDraw` | `Encoding.lean:276` |
| `Params.encIdx'` | `Encoding.lean:264` |
| `Params.encLPNAdvice` | `Reductions/LPN.lean:243` |
| `Params.encPRGAdvice` | `Reductions/PRG.lean:206` |
| `Params.encSeed'` | `Encoding.lean:321` |
| `Params.errProb` | `Claim42.lean:93` |
| `Params.errProb_le_decomposition` | `Claim42.lean:139` |
| `Params.errSet` | `Samplers.lean:58` |
| `Params.eval'` | `Samplers.lean:313` |
| `Params.eval'_correct` | `Correctness.lean:431` |
| `Params.evalTarget` | `Targets.lean:72` |
| `Params.firstGood` | `Samplers.lean:186` |
| `Params.firstGood_none_iff` | `Correctness.lean:56` |
| `Params.halfForm` | `Polys.lean:201` |
| `Params.hasComplexityEff_of_target` | `Targets.lean:293` |
| `Params.hyb` | `Hybrids.lean:112` |
| `Params.hyb_prg_accept_eq_chain_zero` | `Hybrids.lean:157` |
| `Params.hyb_random_eq_raw` | `Hybrids.lean:148` |
| `Params.hyb_real_eq_raw` | `Hybrids.lean:142` |
| `Params.hyb_real_prg_le` | `Hybrids.lean:176` |
| `Params.hyb_uniform_accept_eq_chain_zero` | `Hybrids.lean:167` |
| `Params.hyb_uniform_random_le` | `Hybrids.lean:184` |
| `Params.idCore` | `Samplers.lean:274` |
| `Params.idDrawEquiv` | `Encoding.lean:215` |
| `Params.idSamp'` | `Samplers.lean:283` |
| `Params.idxBound` | `Encoding.lean:393` |
| `Params.idxEquiv` | `Encoding.lean:197` |
| `Params.kappaOf` | `Params.lean:155` |
| `Params.kappaOfN` | `Params.lean:164` |
| `Params.kappaOfN_n` | `Params.lean:332` |
| `Params.kappaOf_pow` | `Params.lean:316` |
| `Params.linearCoeff` | `Polys.lean:178` |
| `Params.lpnEnc` | `Reductions/LPN.lean:68` |
| `Params.lpnFamily` | `Targets.lean:279` |
| `Params.lpnFamily_raw` | `Params.lean:367` |
| `Params.lpnPre` | `Reductions/LPN.lean:321` |
| `Params.lpnPreTarget` | `Targets.lean:139` |
| `Params.lpnRed` | `Reductions/LPN.lean:353` |
| `Params.lpnSamplerTarget` | `Targets.lean:197` |
| `Params.lpnVector` | `Samplers.lean:116` |
| `Params.lpn_hop` | `Reductions/LPN.lean:398` |
| `Params.m` | `Params.lean:83` |
| `Params.mBound` | `Encoding.lean:344` |
| `Params.n` | `Params.lean:76` |
| `Params.nBound` | `Encoding.lean:338` |
| `Params.noiseValue` | `Samplers.lean:45` |
| `Params.noiseWidth` | `Params.lean:90` |
| `Params.oneFlag` | `Samplers.lean:82` |
| `Params.oneSd` | `Samplers.lean:140` |
| `Params.oneSd_factors_mul` | `Correctness.lean:206` |
| `Params.one_le_E` | `Params.lean:57` |
| `Params.one_le_d` | `Params.lean:52` |
| `Params.packSeed` | `Samplers.lean:196` |
| `Params.prgEnc` | `Reductions/PRG.lean:83` |
| `Params.prgPoly` | `Polys.lean:221` |
| `Params.prgPre` | `Reductions/PRG.lean:248` |
| `Params.prgPreTarget` | `Targets.lean:154` |
| `Params.prgRed` | `Reductions/PRG.lean:271` |
| `Params.prg_hop` | `Reductions/PRG.lean:338` |
| `Params.primeWidthBound` | `Samplers.lean:343` |
| `Params.privEquiv` | `Params.lean:232` |
| `Params.privLen` | `Params.lean:209` |
| `Params.pubEquiv` | `Params.lean:255` |
| `Params.pubLen` | `Params.lean:173` |
| `Params.publicSeed` | `Hybrids.lean:53` |
| `Params.qGenTarget` | `Targets.lean:91` |
| `Params.rc` | `Params.lean:126` |
| `Params.rcBound` | `Encoding.lean:357` |
| `Params.realizable_of_targets` | `Targets.lean:232` |
| `Params.sVarBound` | `Encoding.lean:372` |
| `Params.sdCore` | `Samplers.lean:236` |
| `Params.sdSamp'` | `Samplers.lean:302` |
| `Params.sdSampFull` | `Samplers.lean:292` |
| `Params.seedBitsAt` | `Stretch.lean:64` |
| `Params.seedBitsAt_le` | `Stretch.lean:82` |
| `Params.seedBound` | `Encoding.lean:383` |
| `Params.t` | `Params.lean:120` |
| `Params.Γ` | `Params.lean:146` |
| `Params.δ` | `Params.lean:53` |
| `Params.δ_lt_one` | `Params.lean:55` |
| `Params.δ_pos` | `Params.lean:54` |
| `Params.ℓ` | `Params.lean:70` |
| `PolyTerms` | `PolyTerms.lean:45` |
| `PolyTerms.denote` | `PolyTerms.lean:56` |
| `PolyTerms.encTerms` | `PolyTerms.lean:85` |
| `PrimeParam` | `Defs.lean:48` |
| `PrimeParam.le_two_pow` | `Defs.lean:52` |
| `PrimeParam.p` | `Defs.lean:49` |
| `PrimeParam.prime` | `Defs.lean:50` |
| `PrimeParam.two_pow_le` | `Defs.lean:51` |
| `PrimeSchedule` | `Defs.lean:72` |
| `PrimeSchedule.nonempty` | `Defs.lean:82` |
| `SPRG` | `Defs.lean:402` |
| `SPRG.Raw` | `Defs.lean:97` |
| `SPRG.Raw.HasComplexity` | `Defs.lean:298` |
| `SPRG.Raw.HasComplexityEff` | `Defs.lean:352` |
| `SPRG.Raw.HasComplexityEff.hasComplexity` | `Defs.lean:388` |
| `SPRG.Raw.IdDraw` | `Defs.lean:107` |
| `SPRG.Raw.Idx` | `Defs.lean:102` |
| `SPRG.Raw.SdDraw` | `Defs.lean:127` |
| `SPRG.Raw.Secure` | `Defs.lean:260` |
| `SPRG.Raw.SubexpSecure` | `Defs.lean:267` |
| `SPRG.Raw.adv` | `Defs.lean:251` |
| `SPRG.Raw.challengeStr` | `Defs.lean:218` |
| `SPRG.Raw.encIdDraw` | `Defs.lean:113` |
| `SPRG.Raw.encIdDraw_injective` | `Defs.lean:114` |
| `SPRG.Raw.encIdx` | `Defs.lean:115` |
| `SPRG.Raw.encIdx_injective` | `Defs.lean:116` |
| `SPRG.Raw.encIdx_length_le` | `Defs.lean:118` |
| `SPRG.Raw.encSdDraw` | `Defs.lean:134` |
| `SPRG.Raw.encSdDraw_injective` | `Defs.lean:135` |
| `SPRG.Raw.eval` | `Defs.lean:136` |
| `SPRG.Raw.game` | `Defs.lean:234` |
| `SPRG.Raw.idCore` | `Defs.lean:112` |
| `SPRG.Raw.idDrawCard` | `Defs.lean:110` |
| `SPRG.Raw.idDrawEquiv` | `Defs.lean:111` |
| `SPRG.Raw.idDrawFintype` | `Defs.lean:108` |
| `SPRG.Raw.idDrawNonempty` | `Defs.lean:109` |
| `SPRG.Raw.idSamp` | `Defs.lean:179` |
| `SPRG.Raw.idxBits` | `Defs.lean:117` |
| `SPRG.Raw.idxCard` | `Defs.lean:105` |
| `SPRG.Raw.idxEquiv` | `Defs.lean:106` |
| `SPRG.Raw.idxFintype` | `Defs.lean:103` |
| `SPRG.Raw.idxNonempty` | `Defs.lean:104` |
| `SPRG.Raw.modulus` | `Defs.lean:98` |
| `SPRG.Raw.modulus_le_pow` | `Defs.lean:101` |
| `SPRG.Raw.modulus_prime` | `Defs.lean:99` |
| `SPRG.Raw.outBound` | `Defs.lean:123` |
| `SPRG.Raw.outLen` | `Defs.lean:121` |
| `SPRG.Raw.outLen_le` | `Defs.lean:126` |
| `SPRG.Raw.privLen` | `Defs.lean:120` |
| `SPRG.Raw.privLen_le` | `Defs.lean:125` |
| `SPRG.Raw.pubLen` | `Defs.lean:119` |
| `SPRG.Raw.pubLen_le` | `Defs.lean:124` |
| `SPRG.Raw.residueBits` | `Defs.lean:100` |
| `SPRG.Raw.sdCore` | `Defs.lean:132` |
| `SPRG.Raw.sdDrawCard` | `Defs.lean:130` |
| `SPRG.Raw.sdDrawEquiv` | `Defs.lean:131` |
| `SPRG.Raw.sdDrawFintype` | `Defs.lean:128` |
| `SPRG.Raw.sdDrawNonempty` | `Defs.lean:129` |
| `SPRG.Raw.sdSamp` | `Defs.lean:188` |
| `SPRG.Raw.seedBound` | `Defs.lean:122` |
| `SPRG.eval_eff` | `Defs.lean:403` |
| `SPRG.idSamp_eff` | `Defs.lean:404` |
| `SPRG.sdSamp_eff` | `Defs.lean:407` |
| `exists_sprg_of_targets` | `Targets.lean:333` |
| `exists_sprg_of_targets_subexp` | `Targets.lean:349` |
| `exists_sprg_raw` | `Security.lean:167` |
| `exists_sprg_raw_subexp` | `Security.lean:184` |
| `jlsSPRG` | `Targets.lean:301` |
| `jlsSPRG_raw` | `Samplers.lean:355` |
| `jlsSPRG_toRaw` | `Targets.lean:308` |
| `jls_hasComplexity` | `Correctness.lean:489` |
| `jls_hasPolyStretch` | `Stretch.lean:122` |
| `jls_secure` | `Security.lean:102` |
| `jls_seedBits_le` | `Stretch.lean:103` |
| `jls_subexpSecure` | `Security.lean:129` |
| `jls_subexpSmall` | `Security.lean:115` |
| `lemma42` | `Security.lean:62` |
| `lpnNoise` | `LPN.lean:49` |
| `lpnNoise_law` | `LPN.lean:67` |
| `privDegree` | `Degree.lean:56` |
| `prop41` | `Security.lean:84` |
| `pubDegree` | `Degree.lean:45` |
| `sparseEntries` | `SparseFactor.lean:48` |
| `sparseFactor` | `SparseFactor.lean:91` |
| `sparseFactor_mul_of_card_le` | `SparseFactor.lean:202` |
| `sparseLeft` | `SparseFactor.lean:61` |
| `sparseRight` | `SparseFactor.lean:76` |
| `theorem41` | `Security.lean:141` |
| `theorem41_of_targets` | `Targets.lean:319` |
| `theorem41_subexp` | `Security.lean:153` |

