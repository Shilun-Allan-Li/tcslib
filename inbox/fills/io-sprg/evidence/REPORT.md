# io-sprg Phase A — checkpoint 0, M0 statements

M0 is complete and frozen at `d10a560b34d58919bc1a5206ce66a444613f94c7`. This is a statements checkpoint:
146 named Phase A theorem proofs remain. Readers and PrimeSchedule.nonempty are proved;
T1–T6 remain named Phase B obligations. M1–M6 are pending. No final proof-completion
claim is made. Work continues after this checkpoint without waiting for the statements gate.

## Bases, heads, and milestones

- Lean base: `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`; local branch `fill/io-sprg` remains on that base.
- M0 head: `d10a560b34d58919bc1a5206ce66a444613f94c7`.
- Records: `dbea2807532392781304e004715f3b0190025f5e`.
- Host inputs: `bc9d982b83cb35ea351e2fb373752e8688945b1c`.
- Rule 10 tool provenance: `2467bc3befdad8472b1f359337bf3a203e3651e1`.
- Gate source revision: `d286bafc4b1754e26ecae89c7f7f9c2a7cb7d7d3`.
  The empty M0 marker changes no source or imported olean; every source hash is rebound to HEAD.
- New source: 22 files, 5,911 lines. Existing edit: TCSlib.lean, one export import.

| Milestone | Status | Commit / scope |
| --- | --- | --- |
| M0 statements | Complete, frozen | `d10a560b34d58919bc1a5206ce66a444613f94c7`; all 22 owners and required M0 gates pass. |
| M1 algebraic correctness | Pending | No proof milestone claimed. |
| M2 stretch | Pending | Includes SP-W3 seed growth. |
| M3 Claim 4.2 | Pending | Common cutoff before every public prime. |
| M4 reductions / prop41 | Pending | Every-realiser inequalities. |
| M5 raw Theorem 4.1 | Pending | Conditional security and existence. |
| M6 links / assembly | Pending | Targets remain hypotheses. |

## Current checks

| Check | Result and evidence |
| --- | --- |
| Owned modules | 22 current-byte passes, rc0 and zero errors in both diagnostic forms; only declared sorry warnings. evidence/build/summary.txt binds every source to HEAD. |
| decls2 | 670 ADDED, zero CHANGED/REMOVED against the base; evidence/checks/m0-sp-w3/decls2.log. |
| Statements | 1036 stored constants, 948 public full kernel-expression types; evidence/axioms/m0-sp-w3/StmtDump.jsonl. |
| Axioms | 511 public theorem prints match the full graph. Zero nonstandard axioms; 146 direct holes and 265 transitive sorry dependents. Only propext, Classical.choice, Quot.sound, and declared M0 sorryAx. |
| Rule 10 | All 88 seal probes and 96 paired-control probes have verified runtime records, exact source/log/import-environment bindings, masks, and EOF coverage; complete-runtime-check.json. Both canonical variants have zero failing declarations. |
| Controls | All 48 current unsealed probes pass; each sealed negative fails exactly once and every positive passes. All four ctlcheck variants report ALL_OK True. |
| Explicit unfolding | 21 items, all actual theorems; zero foreign definition unfoldings; explicit-classified.json. |
| Lint | Style zero findings; zero new individual campaign FAIL/WARN lines against base. sk15 has one lexical statement-length false positive with Iff.rfl proof, recorded in sk15-triage.txt. |
| Sizes / names | Every file at most 1,000 lines, every line at most 100 characters; 670 names, zero clashes/duplicates. |
| Phase A / PDFs | Only the 23 permitted paths change; permitted sampler-contract imports only in designated owners; no sampler/machine construction, local contract/realiser variant, or PDF in any delivered or committed path. |
| Cache / host | 83 direct Mathlib roots, narrowed cache refreshes only when roots were added, pinned wrapper -k3. All Lean work is root-only, serial under LEAN_SLOT_TAG=io-sprg. Team-limit deviation is disclosed below. |
| Replay / bundle / manifests | Packaging verifies every commit hash by git am --empty=keep, verifies the bundle, and checks both manifests as exact path sets. See evidence/replay.json, bundle-verify.txt and payload-source-binding.json in this payload. |

Seal request totals: {'strict-A': 23333, 'strict-B': 23350, 'coe-A': 23315, 'coe-B': 23332}. Per-owner counts are in request-counts.tsv.
Strict-only failing probes: 0; declaration-level attribution is in
seals-strict-A.tsv and seals-strict-B.tsv. Canonical coe-A/coe-B pass with the single
FinDist coercion notation exception specified by the dispatch. Historical failed or
pre-repair checks are retained and are not counted as current passes.

## Source commits

| Commit | Subject |
| --- | --- |
| `03b157e974aed1021f920d3a954cc2dc43e7a5b4` | io-sprg: prepare Phase A module imports |
| `8679f7161261fb8294ffabdeee620ce859472cca` | io-sprg: draft raw syntax and construction cores |
| `83dda868993a846d278ffc0df7a1185f36f81490` | io-sprg: prepare complete M0 statement candidate |
| `b3712d241bf30130e9424b85c60c8223701be4cd` | io-sprg: complete public instance readers and lint names |
| `2af7d5111f63dcb24a498dbddcf76b1d26c591ef` | io-sprg: publish Boolean finiteness instance readers |
| `23f22a93d8ea100132baedeb04014d291e287be6` | io-sprg: prove derived sampler correspondence readers |
| `b80bfb9011f7bf39ec1548467c27dda102e2d0e9` | io-sprg: complete M0 reference and facade headers |
| `bb3455c5015031a9b03a4013fbe8d372fc09791d` | io-sprg: import shared floor bound for rounded stretch proofs |
| `4efedfad01b049abd1a393e1c449c6e49552119a` | io-sprg: repair sampler readers under canonical seals |
| `1a941e8ffc8f6ca5b104990f21e4bbbabecebcb0` | io-sprg: pre-M0 SP-W2 compare hybrid acceptance probabilities |
| `cd916ad868f1b921d1716d618f2fa1f9f8bbfdcf` | io-sprg: reuse existing bounded power inverse API |
| `55cb1147ff84f750a6b94f48103f6cc72d4fa036` | io-sprg: order parameter bounds for direct reuse |
| `18bfd824aa27796148a76a211ba7e75f65d225b4` | io-sprg: make raw bound transports robust to eval seals |
| `d286bafc4b1754e26ecae89c7f7f9c2a7cb7d7d3` | io-sprg: require growing seeds in polynomial stretch |
| `d10a560b34d58919bc1a5206ce66a444613f94c7` | io-sprg: M0 statements (all proofs sorry) |

## Source and host

jls26.pdf was read in place only after SHA-256 matched
`bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d`.
No PDF is copied, committed, or delivered. Base/head tree checks found no PDF paths.

Initial memory headroom3.918167GiB failed the4GiB floor; the delayed retry passed at
4.368317GiB. Disk95.748741GiB exceeded12GiB; hardware12CPUs/18GiB RAM.
The initial preflight log is dated08:48:10UTC and the successful retry08:58:49UTC,
more than ten minutes later. Wrapper acquisitions/releases and recorded dead-wrapper
reaps are attached; their audit does not invent unlogged wait or termination times.
The host limit is “at most3Lean processes across ALL jobs”; io-sprg holds at most one.
Root runs every Lean/lake/probe/seal through the exact pinned lean-slot.sh with
LEAN_SLOT_TAG=io-sprg. Narrowed cache alone holds-k3. No lake build or unfiltered
cache fetch ran. The user explicitly authorized the dispatch's slot-wrapped shell checks
over the generic AGENTS.md prohibition; its initial automatic-review rejection is resolved.

**Team-limit deviation.** A child started a third research descendant, exceeding the
whole-job two-subagent limit. Root interrupted it on discovery and prohibited further
spawning/resumption. Its recorded activity was source reading, rg, and temporary notes;
no Lean, Lake, cache, push, or implementation-source mutation was reported. This is based
on the parent's task/activity context, not an independent process-history audit. Duration
was not established. The breach and correction are in evidence/host/team-limit-correction.json.
The active team is now root plus the two original children; the extra descendant stays stopped.
Tagged slot history is attached in evidence/host/slots-io-sprg.log. Its wrapper-event
audit accounts for dead-wrapper REAP records before new acquisitions. One historical
wrapper has a REAP without a RELEASE; its end time, termination cause, and child-process
history are not inferred. This is not an independent audit of all host processes.

## Statement changes

All listed statement refinements were completed before the M0 freeze; no post-M0 statement change is reported. SP-W1 is resolved by
the user's exact ruling: “Use rational δ throughout, coercing it to real values for analysis”.
SP-W2 repairs two false free-oracle syntax equalities at acceptance-probability level;
its exact obligations, four-vs-five-query counterexample, minimal change, and authorization
are in evidence/route-requests/SP-W2.txt. No algorithm or headline security inequality changes.
SP-W3 strengthens HasPolyStretch by requiring eventual kappa<=seedBits, ruling out
zero/constant-length existential witnesses. The actual construction has the stronger
all-parameter bound kappa+1<=seedBits; no hypothesis or algorithm changes.

Additional pre-M0 choices: faithful injective index/draw encodings; explicit finite
coordinates; optional empty-grid bucket positions; complete public parameter words;
canonical assumption challenge encodings; one T6 sampler/map before all schedules;
precise reuse imports for existing floor and bounded-inverse APIs. These are detailed below.
Proof-plan review found public PadQuad.exists_pow_dominates in an unavailable broader
owner. The proposed copy of its monic-normalization argument is marked superseded,
not approved or landed. The preferred untested stretch plan keeps the polynomial
coefficient and composes existing rpow growth facts to absorb it. No import changed.
No open approval or user-input question remains.

## Tool adaptations and evidence integrity

The reviewed runner's Linux flock was replaced by the pinned Mac slot wrapper and own
package/olean paths. Chunk size2048 preserves every requested name while avoiding repeated
whole-environment scans. Success records use IO.println of the same MessageData.toString;
the adapter verifies that reversing this transport restores every other byte and line count.
Every guard, instance mask, exact lookup-state check, component identity and EOF check remains.
Queues now bind every reused pass to the complete job-owned olean environment as well as
probe/log hashes. The SP-W3 change invalidated historical environment-free passes; all
current gates are rerun. No historical pass is represented as a current environment-bound pass.
The original1154-request pilot passed, and the faster equivalent pilot passed in53.29seconds
versus250.75seconds. Unsealed control syntax uses outer@ to suppress implicit lambdas;
positives use published readers and negatives use reflexivity under the stored telescope.
The wrapper archives failure probes/logs by hash. An overwritten old failed log was reproduced
exactly from its saved probe, matching its original SHA-256; this is explicitly dated evidence.

## Open questions

- SP-W1: resolved; recommended/selected option is rational delta with real analytic coercions.
- SP-W3: resolved under the same autonomy authorization; growing-seed stretch is selected.
- SP-W2: resolved under the user's autonomous-judgment authorization; recommended/selected
  option is acceptance equality. Adding dummy sampling to the algorithms was rejected.
- Source folder and shell-check exception: supplied/approved by the user; no pending request.

## Fidelity to JLS26 and the binding design

Snapshot: `1a941e8ffc8f6ca5b104990f21e4bbbabecebcb0 (review snapshot; line references remapped by root to d10a560b34d58919bc1a5206ce66a444613f94c7)`. Locations are relative to
`TCSlib/Cryptography/Obfuscation/StructuredSeed/`. The source is Jain, Lin, and Sahai,
*Indistinguishability Obfuscation from Well-Founded Assumptions*, J. ACM 73(1),
Article 1, February 2026. Its hash was verified before source reading. PDF page k is
article page 1:k. No PDF is part of the payload.

The table covers every paper definition, construction component, and main result in
scope, including the disclosed SP-W2 probability-level correspondence repair. `evidence/statements/fidelity-current.tsv` adds an exhaustive lexical inventory of the public
source declaration headers, including each reader/helper, its location, its actual
source tag, and its own deviation prose. Untagged reader/composition glue is marked
as such rather than assigned an invented paper claim. Structure fields/projections,
constructors, and generated constants are represented by their owning structure row;
the separate typed StmtDump/decls2 gate is the authority for elaborated declarations.

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

`Degree.Internal` closure lemmas, coordinate equivalence wrappers, polynomial-size
majorants, selection/packing lemmas, injectivity lemmas, and instance readers are
explicitly mathematical or interface glue. They are exhaustively listed in the
adjacent declaration inventory and proof-obligation appendix; their purpose is to
prove the paper-mapped statements above, not to add an independent paper theorem.


## Rule 15: primitives and their efficiency fields

Source snapshot: `1a941e8ffc8f6ca5b104990f21e4bbbabecebcb0 (review snapshot; line references remapped by root to d10a560b34d58919bc1a5206ce66a444613f94c7)` (committed candidate observed
read-only after the published Raw-instance-reader and inference-binder cleanup). Paths in the tables are relative to
`TCSlib/Cryptography/Obfuscation/StructuredSeed/`. These tables record source-level
contracts; this reviewer ran no Lean, Lake, cache fetch, build, seal, or axiom command.

| Primitive / algorithm layer | Exact uniform efficiency fields | Raw layer and actual sampler law | Construction from targets |
| --- | --- | --- | --- |
| `BoolPRG` (`BoolPRG.lean:50`) | `eval_eff` (`:94`) chooses one `PolyTimeComputable` string map before all `n`, indices, and Boolean seeds. `idSamp_eff` (`:99`) is the shared `CoinSampling.SamplesEfficiently` contract for its supplied `IdDraw`, `encIdDraw`, `encIdx`, and `idCore`. | The input primitive itself carries the algorithm data. `BoolPRG.idSamp` (`:124`) is exactly the pushforward of one uniform `IdDraw` through `idCore`, with proved reader `idSamp_eq` (`:128`). It is not a disconnected arbitrary sampler field. | This job assumes a `BoolPRG`; it constructs no new value of that type. Its evaluator and sampler witnesses are mandatory input data. |
| `LPNFamily` (`LPN.lean:400`) | `sample_eff` (`:402`) is shared `SamplesEfficiently` for the exact joint matrix/secret/noise draw, parameter word `sampleWord`, draw/output encodings, and `sampleCore`. | `LPNFamily.Raw` (`:79`) fixes samples, public modulus, exact noise denominator, polynomial bounds, canonical `toLWE` (`:136`), `adv` (`:166`), and `Assumption` (`:175`). Its complete draw is `Raw.Draw` (`:189`), its actual core is `sampleCore` (`:306`), and `sampleLaw` (`:317`) is the exact one-draw pushforward. | `Params.lpnFamily` (`Targets.lean:279`) extends `P.lpnFamily_raw pi` with the field furnished by `lpnSamplerEfficient_of_target` (`:269`), from T6. `lpnFamily_toRaw` (`:285`) is proved `rfl`. |
| `SPRG` (`Defs.lean:397`) | `eval_eff` (`:398`) is `toRaw.EvalEfficient`; `idSamp_eff` (`:399`) and `sdSamp_eff` (`:402`) are shared `SamplesEfficiently` contracts on the exact raw index and seed draws and their cores. | `SPRG.Raw` (`:97`) stores all honest algorithm data, explicit finite-coordinate equivalences, and encodings. `Raw.idSamp` (`:179`) and `Raw.sdSamp` (`:188`) are derived exact uniform-draw pushforwards. `Raw.EvalEfficient` (`:318`) chooses one map before all parameters, with the public modulus in its input. | `jlsSPRG` (`Targets.lean:301`) extends `jlsSPRG_raw P pi`; T1 supplies `eval_eff` via `evalEfficient_of_target` (`:238`), T3 and T5 supply both sampler fields via `idSampEfficient_of_targets` (`:245`) and `sdSampEfficient_of_targets` (`:257`). `jlsSPRG_toRaw` (`:308`) is proved `rfl`. |

`Raw` is expressly an algorithm bundle, not a primitive claiming efficiency. The only
new `SPRG`/`LPNFamily` structure expressions are these two target assemblies.
The concrete-to-raw sampler and public-prefix transport readers `jlsSPRG_raw_idSamp`,
`jlsSPRG_raw_sdSamp`, and `jlsSPRG_raw_encPP` (`Samplers.lean:503`, `:512`, `:523`)
have explicit proof bodies in this committed snapshot. The sampler transport proofs
read the published `SPRG.Raw.instIdDrawFintype_eq` and `instSdDrawFintype_eq`
equations (`Defs.lean:159`, `:163`) to expose their stored finite instances.
`instIdxFintype_eq` is also published beside its instance (`Defs.lean:155`).
Inference-only raw instance binders are named `_κ` to remove unused-variable warnings;
this cleanup changes no algorithm or field contract. This is a source inspection,
not an independent validation claim. The named assembly
bridge theorems are M0 proof obligations; the tables do not assert that their `sorry`
bodies have been filled.

Literal target selection in the assemblies is consistent with
`Targets = T1 /\ T2 /\ T3 /\ T4 /\ T5 /\ T6` (`Targets.lean:216`):

| Field / consequence | Target witness selected |
| --- | --- |
| sPRG `eval_eff` | `hT.1` (T1) |
| sPRG `idSamp_eff`, `sdSamp_eff` | `hT.2.2.1` (T3) and `hT.2.2.2.2.1` (T5) |
| LPN `sample_eff` | `hT.2.2.2.2.2` (T6) |
| `HasComplexityEff P.d 2` | T2, through `hasComplexityEff_of_target` (`Targets.lean:293`) |
| reduction realisers | T4, through `realizable_of_targets` (`Targets.lean:232`) |

T3 and T5 are predicates on the *same complete draw* for each honest algorithm.
`SamplesEfficiently.intro` joins their halves; it does not combine independent draw
samplers. No product `UniformSampler` is constructed. Data-instance readers are published beside
the supplied Boolean Fintype instances (`BoolPRG.lean:111`, `:115`) and advice
instances (`Reductions/LPN.lean:231`; `Reductions/PRG.lean:183`, `:195`).

T6 (`Targets.lean:197`) uses the shared contract with
`P := fun _ => PrimeSchedule`. Therefore one sampler `U`, one coin polynomial, and one
core map are quantified before **all** `L` and schedules `pi`. This is not the weaker
`forall pi, exists U/f` shape. `lpnSamplerEfficient_of_target` (`:269`) restricts this
single witness to a fixed `pi` and `Unit`, retaining its sampler, polynomial, and map.
The parameter word carries the public prime and unary dimension; no machine computes
a prime schedule.

The shared contract's equivalence need not itself be computable. Explicit supplied
finite-coordinate equivalences and faithful encodings are additional disclosed
pre-M0 interface data, not facts implied by `SamplesEfficiently`.

## Non-vacuity

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

`LPNRealizable` (`Reductions/LPN.lean:413`) and `PRGRealizable`
(`Reductions/PRG.lean:288`) quantify over every adversary and every typed advice family,
then ask for a realiser using the shared predicate and exact coin layout
`A.coins.subst .var`. `Params.Realizable` (`Security.lean:45`) is their conjunction;
it does not define a local variant of `RealizesOn`. The every-realiser security
inequalities choose advice before quantifying the realisers.

## Primitive and link helper plan

The named proof sketches and reuse notes support the following plan. It is pending
proof work, not a list of checks or completed proofs.

| Obligation | Existing API / intended argument | Current source-level status |
| --- | --- | --- |
| Exact scalar LPN noise law (`LPN.lean:67`, `lpnNoise_law`) | Existing finite uniform product/point-mass readers; partition the selector-zero and selector-nonzero cases. Reuse the canonical `LWE.Noise` interface. | M0 theorem hole. |
| Joint draw/output encoding injectivity (`LPN.lean:365`, `:390`) | Existing fixed-width residue/matrix injectivity and pair/list encoding facts, with modulus width bound and explicit coordinate encodings. | M0 theorem holes; the preceding bodies are still `by ... sorry`, not completed proofs. |
| Construction encoding injectivity and polynomial bounds (`Encoding.lean:408` onward) | Owner equations plus existing `Encoding.Modular` lengths/injectivity, `BoolCircuit.encodeList`, `pairEncode` facts, monotonicity of `PolyExpr.eval`, and explicit `Fin` maps. | M0 theorem holes. Do not replace them by classical enumerations. |
| Advice encoding injection and length bounds (`Reductions/LPN.lean:368`, `:376`, `:385`; `Reductions/PRG.lean:304`, `:311`, `:322`) | Canonical `LWE.encodeChallenge_injective`; pair/list/vector lengths; actual draw bounds; inverse-parameter bounds; shared syntactic polynomial monotonicity. | M0 theorem holes. LPN uses a disclosed coarse coefficient `4096`; PRG uses `100`. |
| Targets imply reduction realisers (`Targets.lean:232`) | Apply shared `NUPPT.exists_realizesOn_of_preTarget` with `kappaOf`/`kappaOfN`, `.var`, parameter bound, canonical assumption encoding, explicit advice encoding, length theorem, and T4 witness; use `RealizesOn.congr` only if necessary. | M0 theorem hole. No machine construction or efficiency proof is attempted. |
| T1/T3/T5/T6 assembly bridges (`Targets.lean:238`, `:245`, `:257`, `:269`) | Read target witnesses through the shared contract readers, restrict public parameters to supplied schedule, preserve the sampler/map witnesses, join same-draw halves using `SamplesEfficiently.intro`, and use owner encoding/core readers. | M0 theorem holes. The assembly definitions and `toRaw` readers are already explicit. |
| Efficient polynomial-complexity bridge (`Targets.lean:293`) | Use actual G4 polynomial witnesses, T2's denoting term lists, degree bound, and sampled-seed correctness. | M0 theorem hole; T2 itself remains an unproved Phase B proposition. |

Read-only reuse evidence inspected: `evidence/review/interfaces-notes.txt`,
`prg-notes.txt`, and `lpn-reduction-notes.txt`. They disclose name/shape searches and
reuse of canonical LWE, shared sampler contracts, approved finite equivalences,
`BoolCircuit.encodeList`, shared realiser readers, averaging, and coin-prefix APIs.
Their `exact?`/`apply?` probes are explicitly pending lead-only work; no such probe was
run by this reviewer. Corresponding search artifacts named by those notes are
`reuse-searches.json`, `prg-reuse-searches.json`, and the reduction owner notes.

At M0, named theorem holes used as stored fields can propagate `sorryAx` into raw and
primitive definition dependencies. The lead's actual axiom census/trace must report
that graph; this table makes no claim that only theorem constants depend on `sorryAx`.


## Helper plan

The following table records proof steps and their library searches.

## Overlap and reuse

This is the Phase A proof plan for candidate
`1a941e8ffc8f6ca5b104990f21e4bbbabecebcb0 (review snapshot; line references remapped by root to d10a560b34d58919bc1a5206ce66a444613f94c7)`. It does not claim proof completion.
`evidence/statements/proof-obligations-current.tsv` lists all 146 named M0 theorem bodies containing `sorry`, with
source locations, assigned milestone, and their full owner-side proof sketches.
Every listed obligation has a `**Proof sketch.**` in this snapshot. Definition-body/field readers, literal record/product inverse proofs,
`PrimeSchedule.nonempty`, and the three derived Samplers correspondence equations
`jlsSPRG_raw_idSamp`, `jlsSPRG_raw_sdSamp`, `jlsSPRG_raw_encPP` are now proved source
bodies rather than M0 holes. Kernel checks belong to the lead's evidence.

| Family and intended milestone | Plan and must-reuse API | Search evidence / status |
| --- | --- | --- |
| LPN law and canonical family, M1 | Use existing `LWE.Parameters`, `Noise`, `Family`, `Family.advantageAt`, `DLWEAssumption`, and `dlweAssumption_iff`; prove the one scalar-noise pushforward by finite product/point-mass readers. Do not create an alternate LPN game. | `interfaces-notes.txt`, `reuse-searches.json`; text name/shape searches recorded. Three nonreader LPN obligations remain. |
| Weighted public/private degrees, M1 | New local wrappers of Mathlib weighted degree. Reuse `AddMonoidAlgebra.sup_support_add_le`, `sup_support_mul_le`, `supDegree_sum_le`, `supDegree_prod_le`, public weighted homogeneity C/X facts and the zero-homogeneity iff, plus `weightedTotalDegree_rename_of_injective`. The weight map is already an AddMonoidHom. Do not rederive support bounds or finite-set inductions. Specialized public/private statements reuse the proved wrappers. | `math-primitives-notes.txt` plus `/private/tmp/io-sprg-proof-notes/README.md` and `reuse-searches.json` record precise generic public counterparts found in the follow-up search. Twenty-four unelaborated proof candidates are staged; required `exact?`/`apply?` probes remain lead-only and are not claimed here. |
| Bucket positions/correction matrices, M1 | Increasing finite ranks and `finProdFinEquiv`; prove rank bounds/injection, then exact matrix lookup under non-overfull placement and support-cardinality bound. Reuse finite-cardinality/injection and ordered Fin APIs. | `math-primitives-notes.txt`; no alternate rank or bucket injection theorem found in recorded text searches. Optional positions handle the empty grid. |
| Sparse factorization, M1 | Row-major `List.finRange` enumeration; reuse `mem_finRange`, `nodup_finRange`, finite-list indexing, and `Matrix.mul_apply`. Reconstruct one stored entry per slot, then translate list length to nonzero support cardinality. | `math-primitives-notes.txt`; no rank theorem or public sparse factorization was copied. |
| Tensor and correction polynomials, M1 | Reuse `prod_univ_sum` for the tensor product expansion; original representation's multilinearity/degree fields; `MvPolynomial.eval_map`, `eval₂_eq_eval_map`, `eval_rename`, `eval₂Hom_congr`; owner Degree bounds. Bound actual support cardinality to avoid the erroneous public-degree bound 2D>d for odd d. | `polys-notes.txt`; recorded names/shape searches, Finset sorting API inspection, explicit outputIndex transport. |
| Selection, packing, and correctness, M1 | Existing `List.find?` API and FinRange ordering; explicit equivalence cancellation; assignment equality on polynomial variables via `eval₂Hom_congr'`; sparse reconstruction; `eval_rename`; `Finset.sum_eq_single`/sum-ite; exact `AllOutputs` readers/combinators to lift deterministic-core correctness. | `correctness-notes.txt`; no generic finite-search, polynomial-evaluation, or support theorem is recreated. |
| Power/rounding growth and inverse dimensions, M1-M3/M6 | Read Params equations; use existing natural power monotonicity/root-search facts and source `PowAsymptotics` facts. Prove inverse <=identity and on-image recovery, positive widths, eventual Gamma<=B and log/n lower bounds. | `design-audit.txt`, `interfaces-notes.txt`, and named Params proof sketches. No prime search: Bertrand only proves schedule non-vacuity. |
| Finite encodings and syntactic size bounds, M6/supporting M1-M3 | Compose canonical `ZMod.finEquiv`, `finFunctionFinEquiv`, `finProdFinEquiv`, `finSumFinEquiv`, `finCongr`; reuse `Encoding.Modular` lengths/injectivity, numeral and pair readers, `BoolCircuit.encodeList`, and `PolyExpr.eval` monotonicity. Prove named component/top-level injectivity and polynomial inequalities. | `encoding-notes.txt`, `encoding-reuse-searches.json`; private BoolCircuit helpers are not cited as public API. Any missing composition glue needs its own overlap search before proof. |
| Stretch, M2 | All-parameter seed-count majorant, floor/rpow estimates for rational delta, then power-gap comparison under E>=E0. Reuse `PowAsymptotics` and shared real/natural power APIs; choose eventual stretch exponent using both the input lower stretch and polynomial output upper bound. | `stretch-load-notes.txt` plus the staged Stretch proof/import audit: Nat.div_two_lt_floor is reused via the new precise Floor.Semifield import; add_pow_le and PolyExpr.eval_le avoid generic reproofs. Four M0 obligations remain. E0 retains d for the interface but its sufficient threshold is independent of positive d. |
| Binomial and bucket tails, M3 | Reuse `Nat.choose_le_pow_div` and one exponential-series term (`Real.pow_div_factorial_le_exp`) for the missing standalone binomial estimate; `uprob_exists_le`, explicit uniform equivalence/product projections, and existing coordinate-independence API. Count t+1-element witnesses for load>t. | `stretch-load-notes.txt`, `stretch-load-reuse-searches.json`; no new Markov/union-bound/independence calculus. Inline/private predecessors were found and disclosed; no public standalone counterpart found. |
| Claim4.2 error probability, M3 | Locality union bound -> expected BAD; Markov with Gamma+1; condition on generator index before multiplying independent noise probabilities; condition on the fixed bad set before applying bucket tails; common Cond3 union bound; polynomial/exponential absorption with threshold independent of pp. | Source-level decomposition and proof sketch in `Claim42.lean`; exact public Markov/expectation and uniform-game bridge APIs must be reused. All five nonreader obligations are pending. |
| Hybrids and typed reductions, M4 | Existing agree-off-bad/hybrid inequalities; exact sampler laws; SP-W2 acceptance-probability correspondence at chain zero (not equality of free query trees), read through accept_eq / advantage_eq; real/uniform-tail chains; averaging by `ProbComp.abs_expect_sub_le_expect`, `LamportReduction.exists_expect_sample_le`; shared `RealizesOn` coin/run/verdict readers; existing uniform coin-prefix law; owner casts/readers for canonical challenges. | `lpn-reduction-notes.txt`, `prg-notes.txt`, `prg-reuse-searches.json`; no machine/sampler is built. Advice chooses the largest LPN gap and hardwires all averaged values. |
| Security and subexponential bounds, M5 | Use raw prop41, assumptions for the own LPN family, polynomial reindexing, shared negligibility closure; only shared `Foundations.Subexponential` facts for `SubexpSmall`, `SubexpHard`, factor/add closure, reindexing, `two_pow_neg`. Choose M=min(E*cL,min(E*D*cG,1)); LPN factor losses go M ->7M/8 ->3M/4, the two sums go 3M/4 ->5M/8 ->M/2, and other terms are weakened to match. Use pure two_pow_neg as error majorant at Claim4.2's threshold. | `design-audit.txt`, source proof sketches, and the staged Security/fixed-exponent.md notes identify the exact shared closure route. Unelaborated bodies are not validation against still-sorried prop41/claim42. No local subexponential notion is introduced. |
| Targets -> realisers and primitives, M6 | `exists_realizesOn_of_preTarget` with inverse parameter <=identity, canonical encoding, explicit advice bound, and `.var`; same-draw `SamplesEfficiently.intro`; restrict universal pp/schedule witnesses while preserving U/c/f; T2 supplies actual G4 term lists; exact toRaw readers transport properties. | `primitive-nonvacuity.md`, target proof sketches, shared contract/realisation reports. T1-T6 themselves remain unproved Phase B propositions. |

The read-only subagents did not run `exact?`, `apply?`, Lean, or Lake. Their recorded
text searches do not stand in for the dispatch's required scratch probes. Before
filling any nontrivial helper, the lead must record the remaining required search
probes and reuse the public counterpart if one is found. This report makes no claim
that those probes have already passed. No generic lemma is justified merely by
appearing inline in a new proof.


## Deviations from the design note

These pre-M0 refinements are now frozen. They are disclosed design choices and the
resolved user ruling, not post-M0 statement changes. No weakening is hidden.

| Choice / location | Exact scope and reason |
| --- | --- |
| SP-W1: rational delta (`Params.lean:53`; raw/efficient existence binders) | The user's exact ruling is: “Use rational δ throughout, coercing it to real values for analysis”. Params stores `delta : Q` in (0,1); rounded real-power definitions and E0 receive its real coercion. No theorem quantifies over arbitrary uncomputable real construction data. The initial arbitrary-real counterexample is resolved by this ruling. |
| SP-W2: acceptance correspondence (`Hybrids.lean:157`, `:167`) | The discarded draft assertions equated hyb .prg/.uniform with chainGame at zero as free OracleComp programs. Hyb has four queries and chainGame has five because its uniform public-vector query is unused at zero; singleton queries at kappa=0 still count. The minimal pre-M0 repair states equal accept probabilities and renames theorems to hyb_prg_accept_eq_chain_zero / hyb_uniform_accept_eq_chain_zero. This is the paper's semantic correspondence and suffices for advantage_eq. Exact obligation, counterexample, selected change and authorization are retained verbatim in evidence/route-requests/SP-W2.txt. |
| Faithful generic encodings (`BoolPRG`, `SPRG.Raw`) | Supplied index/draw encodings have injectivity fields, and finite equivalences/cardinalities are explicit data. This strengthens the input representation contract. It prevents hidden index or draw information from being erased by a constant code. The user authorized best judgment on these pre-M0 refinements. Shared `SamplesEfficiently` does not imply injectivity or computability of its abstract equivalence; do not conflate these facts. |
| Complete parameter words (LPN `sampleWord`, sPRG `idWord`/`sdWord`) | Prime first and explicit unary dimension/security parameter avoid collisions forcing a single `UniformSampler.Omega(y)` to stand for incompatible draw dimensions. The full typed public input determines draw and core encodings; no machine computes a prime. |
| Optional bucket grid positions (`Buckets.indexMap`) | At kappa=0, rc=0 while m(0) may be nonzero. A total `Fin m -> Fin rc x Fin rc` is impossible. `Option` with `none` on overfull/empty grids preserves all good placements and the settled exact capacity. Correction polynomials sum assigned coordinates and use zero for `none`. |
| Deterministic sparse factors (`SparseFactor`) | The paper leaves a valid factor choice unspecified. Row-major listing and zero padding give honest deterministic cores with no classical enumeration. The success-conditioned factorization statement is unchanged. |
| Explicit term syntax (`PolyTerms`) | `List (R x List sigma)` uses repeated variables for powers. Existing `BoolCircuit.encodeList` with pair delimiters encodes variable-length components. It denotes actual composite polynomials, not an opaque source code chosen after each parameter. |
| Encoding module split | The encoding portion of the planned Samplers module lives in `Encoding.lean`; it depends only on Params and existing equivalence roots. This is a disclosed modular split, not additional Phase B functionality. |
| Canonical assumption challenges | Mandatory reuse wins: `lpnEnc` is exactly existing `LWE.encodeChallenge` at the family's width, and `prgEnc` exactly `G.challengeStr`. Prime-first applies to the new construction challenges and reduction advice. This interpretation was explicitly selected and recorded before M0. |
| Actual assumption families | Raw/efficient existence only assume LPN for the E-indexed construction families built from the supplied G, representation, and rational delta. This is Q-S1 / Dv3, not a literal Def.2.3 bridge or an assumption for all unrelated LPN families. |
| Raw existence realisability scope (`Security`) | `hR` quantifies over the supplied data's E-indexed Params. It need not cover every unrelated Params. This reduces a sufficient hypothesis and strengthens the conditional raw existence statement. Efficient existence retains `hT : forall P : Params, P.Targets` as proposed. Record the distinction explicitly. |
| Advice bounds | PRG uses explicit coefficient 100; LPN uses the deliberately coarser 4096 to cover its extra nested complete-draw/list fields. Both are concrete syntactic PolyExpr bounds at all independent dimensions, not eventual or existential advice-polynomial claims. |
| Layout-only shared RealizesOn / Dv16 | Each universal-realiser inequality constrains realisers only on encoded challenges and coin strings of the declared layout length. This weaker predicate admits more realisers, making every-realiser security inequalities stronger. All uses are shared API, no local variant. |
| Subexponential security / Dv13 | Advantage against NUPPT has fixed exponent `min(E*cL,min(E*D*cG,1))/2`; assumption exponents precede all adversaries. The theorem is not about subexponential-time adversaries. |
| Exact and eventual bounds / Dv7 | prop41 and hop bounds are for every kappa. Claim4.2 and stretch state common eventual thresholds. Claim4.2's threshold precedes all public primes. Rounding and zero-parameter cases remain total. |
| Raw vs primitive / Dv18 | Raw security/correctness/stretch contain explicit algorithms without an unproved efficiency assertion. The only new primitive values are target assemblies with mandatory named field bridges. T1-T6 remain propositions with the exact Phase B notice, never unconditionally inhabited. |

The final source/quantifier review is qualified by the subsequent SP-W2 correction:
the earlier review missed the distinction between free-program syntax and acceptance.
This candidate incorporates that repair; no additional efficiency quantifier blocker
was found in the reviewed interfaces. In particular, prop41 chooses both advice families before every realiser
and every kappa; T1/T2 maps precede every pp; T4 maps precede every schedule; T6 uses
`SamplesEfficiently (P := fun _ => PrimeSchedule)` so ONE U/c/f precedes all schedules.
Assembly restricts its witnesses to fixed schedule/Unit while retaining those same
uniform objects. T3 and T5 are joined only on their matching complete draw types.

At M0, named sorried field proofs can make Raw/primitive definitions and instances
transitively depend on `sorryAx`. The actual axiom census must report this graph.
The permitted syntactic placement of holes in named theorem bodies does not imply
that only theorem constants have `sorryAx` dependencies.

No M0 freeze existed when SP-W1/SP-W2 and the listed interface refinements were
selected. There is no post-M0 statement-change commit to report at this point.
The earlier review snapshot is historical evidence and its two free-program
chain-zero correspondence claims are superseded by SP-W2.


## SP-W2: semantic hybrid correspondence before M0

The two discarded draft obligations were

```
P.hyb A .prg kappa pp = P.chainGame A true 0 kappa pp
P.hyb A .uniform kappa pp = P.chainGame A false 0 kappa pp
```

They are false as equalities in the inductive free oracle monad. After bind/map
normalization, hyb makes four queries (index draw, seed draw, uniform tail,
adversary coins); chainGame makes five, including an extra uniform public-vector
query that is unused at chain index zero. Following the first answer at each query
distinguishes tree depths four and five. At kappa=0 the added draw is a singleton
but still contributes a query. OracleComp is an inductive program representation;
semantic marginalization does not erase its query constructor.

The chosen minimal pre-M0 repair is

```
accept (P.hyb A .prg kappa pp) = accept (P.chainGame A true 0 kappa pp)
accept (P.hyb A .uniform kappa pp) = accept (P.chainGame A false 0 kappa pp)
```

The source names make the probability-level statement explicit:
`Params.hyb_prg_accept_eq_chain_zero` (Hybrids.lean:157) and
`Params.hyb_uniform_accept_eq_chain_zero` (:167). Their proofs should use published
acceptance/expectation laws to sum out the unused exact uniform draw, then rewrite
advantage through `Games.advantage_eq`. Neither proof should assert a free-program
equality or erase an unused query through an invalid monad law.

This matches the semantic distributions compared in JLS26 Lemma4.2, p.19, and is
sufficient for the headline hybrid advantage inequality. The algorithms, hybrid
definitions, assumptions, efficiency targets, prop41, and all main conclusions are
unchanged. M5 candidates consume prop41's interface and require no body update.

The exact obligation, counterexample, selected repair, and authorization record are
kept verbatim in `evidence/route-requests/SP-W2.txt`. The user authorized best judgment
while asleep with downstream disclosure; E-ROUTE requires this record and minimal
repair, while its rule does not demand a new approval question. Work remains within
owned new files. No M0 checkpoint/freeze had occurred, so this is a disclosed
pre-freeze refinement rather than a post-M0 statement amendment.

The earlier independent draft review missed this syntax/semantics distinction.
That immutable historical snapshot must be read with this superseding correction.
The current report and declaration/hole tables name and quote only the repaired
acceptance statements. No elaboration, seal, or axiom result is claimed by this
report refresh; the lead owns those actual gate logs.


## Size re-estimate and validation status

Candidate `1a941e8ffc8f6ca5b104990f21e4bbbabecebcb0 (review snapshot; line references remapped by root to d10a560b34d58919bc1a5206ce66a444613f94c7)` has 22 new Lean files, 5,911
lines and 301,131 UTF-8 bytes. The largest line is 100 characters. There are 146 named
M0 proof obligations, all with an owner-side Proof sketch. `sizes.tsv` records every
file's line/byte/width counts and SHA-256. The root `TCSlib.lean` import addition is
the one permitted existing-file change and is not included in the new-file total.

The textual public-header inventory has 674 rows: 670 named headers and four
anonymous-instance positions. This is not an elaborated declaration count: generated
structure/instance/projection declarations are accounted for by the lead's typed
StmtDump and decls2 outputs, not by this lexical table.

The initial 4,950–8,450-line expectation leaves about 2,600 lines above this M0.
Filling 146 holes within that upper estimate would allow only about 17 added lines
per hole on average. The main unknowns are rounding/stretch asymptotics, Claim4.2's
conditional product estimates and exponential absorption, and the typed hybrid
averaging/coin transports. A cautious revised completion estimate is roughly
8,500–11,500 Lean lines, including genuinely missing helper proofs and reader glue.
This is an estimate, not an expansion of scope. Keep each file below 1,000 lines;
if a proof-heavy owner approaches that limit, split supporting helpers into a new
inner-namespace module and disclose that import refinement before using it.

This subagent performed only read-only source inspections, targeted text searches,
and deterministic Python inventory/size/docstring checks. It did not run Lean,
Lake, a cache fetch, canonical seals, paired controls, axiom probes, full lint,
clash scan, decls2, or StmtDump for this report task. The lead is collecting those
M0 gate artifacts and must fill the validation table from the actual logs.

| Evidence item | Status in this report material |
| --- | --- |
| Source PDF hash | Lead verified the expected hash before reading; source was read in place, never copied. Hash log is owned by the lead. |
| Source inventory / widths | Independently measured at the stated candidate; all 22 new files, maximum width 100. |
| Fidelity / rule 15 / non-vacuity | Source-level tables incorporate the SP-W2 acceptance repair. Earlier free-oracle equality claims are superseded; this table is a review, not a kernel check. |
| M0 proof inventory | 146 named sorry bodies; all have Proof sketches. Targets are definitions with proved readers; their truth is not asserted. |
| Elaboration, all new modules and affected reruns | Lead-reported passing runs exist; bind final counts and source hashes to the final candidate from actual logs. No independent run was made here. |
| decls2 / typed StmtDump / clashes | Lead-owned; do not copy the lexical 674 count into these fields. Refresh from their actual outputs. |
| Canonical seals / paired controls / explicit-unfold scan | Lead-owned and pending report integration; do not mark complete based on source inspection. |
| Axiom census / headline prints / sorryAx graph | Lead-owned; M0 holes can propagate to stored definitions. Final graph must be empty of sorryAx after all Phase A proofs are filled. |
| Duplication scratch probes | Text searches recorded in owner notes; exact?/apply? are lead-only and were not run by this subagent. |
| Full lint / campaign diff / sk15 | Use lead's actual final-candidate logs. Historical staged-source lint results do not bind the final candidate. |
| Replay / bundle / source manifest / delivery ZIP | Lead-owned delivery checks; not run by this reviewer. |

The helper plan remains Phase A. No word-RAM program, RAM bridge, fair-coin product
sampler, efficiency proof of a target, or unconditional efficient primitive belongs
in this delivery.

The three derived Samplers correspondence equations `jlsSPRG_raw_idSamp`,
`jlsSPRG_raw_sdSamp`, and `jlsSPRG_raw_encPP` now have proved bodies in this candidate.
They have been removed from the hole appendix. The lead reports the affected prefix
checks passed; bind the actual logs and source hashes in the validation evidence.

Lead-reported final-candidate gate counts: decls2 ADDED 670, CHANGED 0, REMOVED 0.
The separate source-header count also has 670 named headers, plus four anonymous
instance positions. Equality of these named counts is not an independent elaboration
check; attach the lead's actual decls2 and typed StmtDump artifacts.

Pre-M0 source refinements since b80bfb901: the precise Floor.Semifield import in
Stretch; Samplers transport proofs now read Raw Fintype instance equations; twelve
inference-only binder warnings were addressed with _kappa binders; SP-W2 renames
and changes only two auxiliary hybrid correspondence statements to acceptance
equalities. Headline theorems, algorithms, targets, and assumptions are unchanged.
The declaration totals are still 670 ADDED / 0 CHANGED / 0 REMOVED relative to the
pinned Lean base, as reported by the lead; the two auxiliary replacements occurred
before any M0 freeze.


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

## Headline axiom prints at M0

```text
'TCSlib.Cryptography.Obfuscation.StructuredSeed.prop41' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.claim42' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.G4_eval_eq' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.jls_hasComplexity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.jls_hasPolyStretch' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.lpnNoise_law' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.jls_secure' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.jls_subexpSmall' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.jls_subexpSecure' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.theorem41' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.theorem41_subexp' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.exists_sprg_raw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.exists_sprg_raw_subexp' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.PrimeSchedule.nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.Params.realizable_of_targets' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.jlsSPRG' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.theorem41_of_targets' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.exists_sprg_of_targets' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.exists_sprg_of_targets_subexp' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
```

## Evidence status

The current gates above supersede pending-check language in the retained read-only review
material below. Those historical notes remain attributed to their actual source snapshots;
root remaps line references to the frozen source and records SP-W1/SP-W2/SP-W3 separately.
SP-W3 supersedes any historical statement that all generic definitions/conclusions stayed
unchanged: HasPolyStretch was strengthened before freeze, as its current source inventory shows.
All proof-candidate packets are explicitly untested and are not source or validation.
