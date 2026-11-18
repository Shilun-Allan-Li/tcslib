# io-sprg Phase A — checkpoint 1 (M1)

M1 algebraic correctness is proved and locally checked at `19dde91afc384656e7e47cb018057e088d4ded0a`. M0 remains
frozen at `d10a560b34d58919bc1a5206ce66a444613f94c7` and was delivered by exchange commit
`15946b52d0615fda8afad9ed3c57cfaf5beaaa8d`. This is an intermediate proof checkpoint:
M2–M6 remain unfinished, with **46 original direct proof holes**. T1–T6 are still
unproved Phase B targets. The whole end-to-end goal and final proofs gate are open.

## Bases, heads and milestone scope

The source branch is local `fill/io-sprg`, based on `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`
(`iO/phase-a-base`), without rebasing. The delivery branch writes only
`inbox/fills/io-sprg/` on `exchange/pass-shelat-ch5-8`.

| Milestone | Status | Source commit |
| --- | --- | --- |
| M0 | Frozen and published | `d10a560b34d58919bc1a5206ce66a444613f94c7` |
| M1 | All proof bodies and local milestone checks complete | `19dde91afc384656e7e47cb018057e088d4ded0a` |
| M2 | Stretch: four original obligations remain | Pending |
| M3 | Claim 4.2/load bounds: ten original obligations remain | Pending |
| M4 | Hybrids/reductions, including shared M4/M6 support | Pending |
| M5 | Raw security and existence | Pending |
| M6 | Targets links/conditional assemblies | Pending |

M1 fills **100 original bodies** (83 foundational/M1 plus 17 encoding support
obligations) and adds **three theorem-only helpers**. All103 saved step records are
CHECKED_PASS; failed attempts and their repairs remain in evidence. The scope is
Degree24, Params14, Encoding17, LPN3, Buckets7, SparseFactor5, Polys10,
Correctness18, the Defs efficiency-forgetting bridge, the Samplers prime-width
bridge, Basic2, and the G4 seed-support helper. Supporting encodings done early do
not complete M6. `evidence/proof-candidates/M1CheckpointDraft/source-obligations.tsv`
lists the original obligations by current declaration location and source status.

## Current local checks and their limits

| Check | Current result and evidence |
| --- | --- |
| Owner compilation | Exact set of23 owners, including both facades: rc0, zero errors in both forms. `evidence/build/M1/all-owners/`; source/log/object hashes bind to HEAD through `evidence/build/summary.txt`. |
| M1 theorem axioms | All297 public theorem prints in the11 affected modules use only propext, Classical.choice, Quot.sound (or subsets). `evidence/checkpoints/M1/axiom-summary.json`. |
| Headline axioms | G4_eval_eq, jls_hasComplexity, lpnNoise_law and PrimeSchedule.nonempty are standard-only. The later headlines retain sorryAx, printed below. |
| Source declarations | Base-to-head:673 ADDED, zero CHANGED/REMOVED. No clashes. All670 frozen M0 headers remain unchanged; exactly3 new helper headers. `evidence/checks/m1-final/`. |
| Style/campaign | Style: zero findings. No new individual campaign FAIL/WARN against the pinned base. The one sk15 lexical flag is the unchanged15-line hasComplexityEff_iff statement with Iff.rfl proof; triage retained. |
| Size/width | 23 owned files,7244 lines; maximum file801 lines, maximum width100. |
| Phase A boundary | No forbidden new import, sampler/realiser-contract variant, forbidden enumeration, machine or sampler construction. Only the two existing target-conditioned primitive assemblies. `evidence/checks/m1-final/boundary.json`. |
| Focused opacity diagnostic | Correctness compiled with the foreign jlsSPRG_raw definition opaque: zero errors. `evidence/meta/M1-focused-raw-opacity/`. This is NOT a full canonical seal. |

The **full stored-constant census, typed StmtDump, sorryAx dependency graph,
full four-variant canonical seals and paired controls have not been rerun at M1**.
Their delivered M0 artifacts are historical evidence for M0 only:22 owners,
88 seals plus96 control probes, all184 passed;1036 stored constants,948 public
kernel types and511 theorem prints were checked there. They are not current M1
counts or proof passes. The final gate must regenerate an exact dynamic owner
inventory (including Basic and any later split modules), all stored roots, controls,
request masks/environment bindings and all four variants. The detailed tooling
coverage audit is in `evidence/proof-candidates/tmpFinalAuditTools/`.

This checkpoint deliberately carries partial final-gate evidence, as allowed for
milestone checkpoints. It makes no claim that the46 remaining direct holes account
for an inferred number of transitive sorry dependents. Actual final transitive
counts must come from the fresh kernel graph, not subtraction from M0.

## Statement changes and judgment calls

There is **no post-M0 change to an existing definition, theorem header or statement
prose**. Proof sketches were synchronized where the implementation strategy changed.
The three new helpers are:

| Helper | Purpose |
| --- | --- |
| Internal.encodeList_injective_of_fixedWidth | A narrow fixed-width specialization using existing BoolCircuit nil/cons readers and List.append_inj. |
| Internal.encodeList_length_of_fixedWidth | Exact tagged-list length, counting every true tag and the final false marker. |
| Params.G4_seed_allOutputs | Retains the literal G4 polynomial witness on the exact seed law for both complexity links. |

Basic is a new theorem-only module importing the already-required Uniform owner.
It adds no external module or Mathlib cache root; the refreshed closure has128
modules and the same83 direct Mathlib roots. A later LPN reduction split into
Defs/Encoding/Transport/Hop is planned for modularity but **has not landed** in this
checkpoint. See `evidence/proof-candidates/LPNModularity/`.

The pre-M0 decisions remain unchanged and disclosed in the M0 report: SP-W1 uses
rational delta with real coercions for analysis, as explicitly ruled by the user;
SP-W2 states semantic accept-probability correspondence because free computations
with different unused queries are not literally equal; SP-W3 adds eventual
kappa≤seedBits to raw polynomial stretch to exclude constant/zero-seed vacuity.
Optional empty-grid positions, deterministic row-major sparse factors, explicit
finite coordinates, faithful encodings and prime-before-input quantifiers remain
frozen. No efficiency target, machine or sampler construction was added.

Current size is7244 lines. The remaining analytic/security proofs can exceed the
original4950–8450 estimate; plan roughly10000–13000 final lines, subject to actual
proofs. Keep each file below1000 lines and split coherent helpers rather than
compressing proofs or weakening statements. The user authorized routine judgment
calls favoring modular, adaptable code; the calls above are recorded for review.

## Overlap and reuse

Existing public APIs are reused for weighted polynomial degrees, finite support
counts, list/range products, modular encodings, bounded inverse schedules, scalar
probability laws, sparse reconstruction, selection and OracleComp support transport.
`evidence/lean_proof/search_log.md` and immutable paired probes record actual searches.
The shared realization/sampler/subexponential APIs remain the mandatory route;
34 required existing APIs were separately axiom-checked standard-only.

Private BoolCircuit prefix-free and variable-size list-length machinery overlaps
conceptually with the new fixed-width specializations. The private declarations
are not accessed or copied. The helpers use public readers and Core append/length
lemmas, introduce no parser or new encoder, and record the narrower statement and
unavailable public alternatives in FixedWidthList/OverlapEncoding notes. Raw LPN's
variable Nat.bits selector was retained and recovered through its existing pair
delimiter; it was not given a false fixed-width premise. The G4 support helper
uses published pure/query/bind readers once for the two complexity consumers.

The current immutable-log review covers218 search runs, all saved source/log hashes
matching:20 closed,68 partial suggestions,92 exact searches without a closing proof,
9 clean apply no-hits,17 bounded timeouts,8 statement-elaboration failures and4
scope failures. Timeouts and finite no-hits do not prove global absence. Partial
suggestions with diagnostic sorry warnings are not proofs. All faulty statement/scope
pairs are retained and explicitly superseded by corrected V2 pairs, including the
OracleComp Type0 repair. A new pre-insertion guard rejects statement-elaboration
errors. `evidence/proof-candidates/M1CheckpointDraft/overlap-log-review.json` and
`evidence/proof-candidates/M1CheckpointDraft/supersession.tsv` contain per-log details.
Other preparation mistakes, including a missing filename and an unquoted question
mark, are retained separately in the search/error notes and
`evidence/overlap/reproduced-missing/`; they are not counted as search outcomes.

## Source and host provenance; process-limit disclosures

The source PDF was verified in place before reading, SHA-256
`bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d`.
It is never copied or committed. The initial3.918167GiB headroom preflight was below
4GiB; the logged retry10m39s later passed at4.368317GiB, with95.748741GiB disk,
12 CPUs and18GiB RAM. These are historical measurements, not current-resource claims.

The prescribed host cap is three Lean processes across jobs and one for this job,
with only the narrowed cache-k3 exception. Root uses the pinned lean-slot wrapper,
LEAN_SLOT_TAG=io-sprg, foreground serial runners and retained process handles.
The user explicitly overrode the generic AGENTS shell-check prohibition for these
slot-wrapped dispatch checks; `evidence/scope-request/lean-check-approval.txt` records it.

**Two historical instruction breaches remain disclosed.** A third research descendant
was spawned beyond the whole-job two-subagent limit and was interrupted by root;
only the original two agents were reused thereafter. No Lean/cache/push or source
mutation was reported for that descendant, based on task reports rather than an
independent activity audit; duration is not independently established.
`evidence/host/team-limit-correction.json` retains the record.

Separately, root discarded an ongoing exec session_id by retaining only its output,
then launched the next owner check while the Params_B_pos apply search remained
active. Tagged wrappers93883 and93983 overlapped at15:07:45–15:07:48UTC. The recorded
search child alone was terminated; its wrapper release is15:08:34UTC. Evidence is
`evidence/host/search-process-correction.json`. This violated this job's one-process
rule. The checker in `evidence/host/M1-final/` preserves the exact incident and REAP
provenance:1068 tagged acquisitions, maximum two wrappers, historical seriality false,
post-correction tagged seriality true, zero active wrappers at its snapshot. Every
other overlap would fail the exact-exception checker. This is a tagged wrapper audit,
not a global host/child-process history proof. No unqualified whole-job seriality or
independent all-jobs-cap claim is made.

## Frozen fidelity, Rule15 and non-vacuity tables

The following mathematical tables are preserved byte-for-byte from the frozen M0
report. **Their line references are historical M0 anchors.** The current M1 anchor
appendix follows by declaration identity; its TSV includes structure fields. The
contracts/formulas are unchanged. Current proof status is given above, not inferred
from these historical location labels. Full M0 deviation details remain in
`evidence/checkpoints/M0/REPORT.md`.

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

## Current headline axiom prints

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
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.jls_hasComplexity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.jls_hasPolyStretch' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Obfuscation.StructuredSeed.lpnNoise_law' depends on axioms: [propext, Classical.choice, Quot.sound]
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

## Source commits

Every source commit from the pinned base is listed below. Exact author/committer metadata and signing status are in `patches/COMMITS.tsv`.

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
| `68469690bf021684214da60615a7c1aec282a876` | io-sprg: M1 degree bounds |
| `5f3ea1c5e6c28f34fa0493cd49528d2489a7ad3e` | io-sprg: M1 parameter bounds and inverse schedules |
| `778397fd929839cc82f6cd70d400770b52796b4a` | io-sprg: M1 shared fixed-width encoding lemmas |
| `19627198f8f279fe6fdf3f67d7d658a1b39e79f0` | io-sprg: M1 faithful encodings and polynomial bounds |
| `cd837aee4db19fa47362316e8b3ac8a5dda09e7b` | io-sprg: M1 exact LPN law and faithful encodings |
| `f2095b7625171b1b1a7a1877a9b9eb5d3a23bb9f` | io-sprg: M1 deterministic bucket placement and correction matrices |
| `8854cf709238defb459377fea0a1e2ff54db88b7` | io-sprg: M1 explicit sparse-factor reconstruction |
| `6477edc198ec33eec8c682bd62ff344be896d07c` | io-sprg: M1 polynomial bidegrees and tensor evaluation |
| `19dde91afc384656e7e47cb018057e088d4ded0a` | io-sprg: M1 algebraic correctness and complexity links |

## Delivery verification and continuation

The packager stages only this unit's payload, replays every patch at the pinned base
with exact hash equality (including the empty M0 marker), verifies the bundle, checks
all intermediate commit trees for PDFs, and checks exact manifest path sets and hashes.
It copies the committed source, not unstaged files. The delivered `evidence/replay.json`,
`bundle-verify.txt`, `pdf-commit-trees.json` and `payload-source-binding.json` are the
packaging authority. Packaging aborts before delivery if any assertion fails.

M1 is checkpoint1; its delivery commit/push record is saved after publication and
reported in chat, because a commit cannot contain its own hash. No final ZIP is
claimed at this intermediate milestone. Continue with all four M2 stretch obligations,
then M3–M6 and the full final gates. No user question is pending. SP-W1 is resolved;
SP-W2/SP-W3 and the disclosed organization/process decisions require downstream review.
