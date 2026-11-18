# Structured-seed pseudorandom generators — current Phase A account

Current source: `049067cb23eac1822fecdbc558ca5f31fc231982`, branch `fill/io-sprg`, pinned base
`5ed465f62e4ae0f93ded1a1ba49e807591b589eb`. PARTIAL M6 checkpoint: all original proof bodies and conditional links are complete. The final audit status is pending (suite not run); this checkpoint is saved for relocation and safe suspension.
The source includes the completed M6 conditional links and the single Gate52 minor
commit titled `gate52 r1 minors: G52-01..05, 07..09`. Phase B target truth is not
established. The complete final opacity/census/kernel validation status is given
below, separately from source proof completion and selected axiom prints.

## Current source and checks

| Measure or check | Current result | Delivered authority |
| --- | --- | --- |
| Owners / lines / largest / width | 34 owners / 10974 lines / largest801 / width100 | `evidence/compact/M6/build-summary.txt`; current `src/` |
| Source headers / original frozen headers | 703 headers; all 670 original kinds/headers unchanged; no public reader removed | `evidence/compact/M6/decls2.tsv` |
| Approved prose / exact moves / theorem helpers | 24 exact authorized declaration-prose updates, 4 module docs, 93 moves, 33 earlier helpers | `evidence/compact/M6/freeze.json`, `changed-headers.tsv` |
| Saved proof checks / original bodies / source holes | 179 saved owner checks: 146 original bodies +33 helpers; zero source holes | compact build/freeze summaries and current source |
| Fresh owner compilation / warnings | 34/34 at this exact head: rc0, errors0 in both forms, warnings0 | `evidence/compact/M6/build-summary.txt` |
| Selected public theorem axiom scope | 61 current declaration rows, all standard-only, covering every Targets theorem, Gate52 changed declaration/inverse readers/facts and the 19 headlines | `evidence/compact/M6/axioms.tsv` |
| Nineteen current headline prints | 19/19 fresh standard-only prints, including assembly definition jlsSPRG | `evidence/compact/M6/axioms.tsv` |
| Style / sk15 / names / campaign delta | style/sk15/clash rc0; campaign baseline rc1 with zero new FAIL/WARN; sizes/widths and source-history PDF checks pass | `evidence/compact/M6/lint-summary.json`, `style.txt`, `sk15.txt`, `clash.txt` |
| Exact declaration/header delta | 703 ADDED relative to pinned base; 0 CHANGED/REMOVED; all frozen global headers retained | `evidence/compact/M6/decls2.tsv`, `changed-headers.tsv` |
| Tagged wrapper audit | 1620 tagged acquisitions; historical maximum2/serial=false; post-correction serial=true; active0 | compact lint/freeze result summary; complete raw archive |

The executing agent ran the source/owner checks, isolated searches, axiom-print
probes and static diagnostics represented by those compact results. The received
sub-agent reviews were static fidelity/API/quantifier/prose reviews and untested
candidate preparation; receiving a review was not a compiler or gate pass.
The maintainer performs the Lean replay; no agent-run Lean replay is claimed.
The selected prints do not establish the complete stored graph or canonical opacity gates. No new long-running work was started after this checkpoint preparation.

## Milestones and delivery identity

| Checkpoint | Source commit | Actual published exchange commit |
| --- | --- | --- |
| M0 | d10a560b34d58919bc1a5206ce66a444613f94c7 | 15946b52d0615fda8afad9ed3c57cfaf5beaaa8d |
| M1 | 19dde91afc384656e7e47cb018057e088d4ded0a | 10da7fdefd9a44023cc117a672f19e8a3617b81d |
| M2 | 4ecc40c04a001bc87349b7ec368ece309774c28a | c1d4f422f071f4a8e346d71a0f00ea3525941eee |
| M3 | 04249b85e80a007dc5845077a18a365d5150e14b | 2a9ccadc2772789ace445490f6df8d231ff1221b |
| M4 | 428c7eb117b51fe512348f226284df247e98c00c | 33e944e359da71e42c15f922513b4da2f217cad4 |
| M5 | 990eba8673c73bce6c739d3fe61848d44b2fdb7c | c531c52de5cf4c93d8519e62b13cdad1fdb41ad3 |
| M6 proof checkpoint | 3da6977bc86df1687b0e1d4813157bc882e9cca9 | Included in this M6+Gate52 delivery; its own delivery hash is recorded externally after publication |
| Gate52 minors | 049067cb23eac1822fecdbc558ca5f31fc231982 | Current M6+Gate52 delivery; the actual hash is recorded externally after publication |

The M6 proof work and Gate52 minors have separate source commits. Source commit
hashes and author/committer/signing metadata are in `patches/COMMITS.tsv`; the Lean
replay belongs to the maintainer. Publication hashes are external delivery records,
so the current package does not contain its own future push hash. M5's verified
compact charge was 1,364,276 bytes, 1,520 custom inserted UTF-8 lines and 1,534 actual
Git-inserted lines; these historical quantities are not current package totals.

## Current fidelity to JLS26

Names are in `TCSlib.Cryptography.Obfuscation.StructuredSeed` unless qualified.
The delivered current `decls2.tsv` locates each name in `src/`; this table contains
current semantics and owners, not copied historical line numbers.

| Paper item / page | Principal current names and owner | Formalization and disclosed difference |
| --- | --- | --- |
| Polynomial descriptions, §2 p.8 and Def.3.3 p.10 | `PolyTerms`, `denote`, `encTerms` (`PolyTerms`) | Finite term lists use repeated variable occurrences, delimited coefficient/coordinate encodings and the existing polynomial semantics. |
| Noise / LPN, Def.2.3 pp.9–10 | `lpnNoise`, `lpnNoise_law`, `LPNFamily.Raw.toLWE/adv/Assumption` (`LPN`) | Exact selector/residue law, including triggered zero noise; canonical LWE advantage/challenge reused, transposed convention and construction's own rounded family. |
| Honest LPN sampling, pp.9–10 | `LPNFamily.Raw.Draw/sampleCore/sampleLaw`, `LPNFamily` (`LPN`) | One complete finite matrix/secret/noise draw; mandatory shared efficient-sampling field only on the primitive. |
| Boolean PRG / locality, Def.3.4 p.11 | `BoolPRG`, `MultilinearRep`, `HasLocality`, `HasStretch` (`BoolPRG`) | Actual index draw/core, uniform evaluator/sampler fields, supplied integer multilinear representation, and pointwise stretch lower bound. |
| sPRG syntax, Def.3.1 p.10 | `SPRG.Raw`, `SPRG`, raw `idSamp/sdSamp` (`Defs`) | Explicit finite modular seed vectors and exact core-pushforward laws; primitive adds mandatory evaluator/two sampler efficiencies. |
| Security, Def.3.2 p.10 | raw `challengeStr/game/adv/Secure/SubexpSecure` (`Defs`) | Public prime/index/public seed/output challenge, NUPPT advantage, shared negligible/subexponential predicates. |
| Complexity, Def.3.3 p.10 | `pubDegree`, `privDegree`, raw `HasComplexity/HasComplexityEff` (`Degree`, `Defs`) | One composite G4 polynomial with public degree d/private degree2; efficient form produces actual finite term descriptions. |
| Public field, §4 p.15 | `PrimeParam`, `PrimeSchedule`, `PrimeSchedule.nonempty` (`Defs`) | Supplied prime in weak power-of-two interval; no prime algorithm or prime stored in Params. |
| Dimensions / rounding, §4 p.15 | `Params.ℓ/n/m/W/t/rc/cap/B/Γ` (`Params`) | Fixed powers and rational noise exponent. Γ is m times integer base-two log of n, then natural division by W: extra downward log rounding is explicit. |
| Reindexing, Remark2.1 p.9 | `kappaOf`, `kappaOfN`, readers/inverse facts (`Params`) | Aliases use public PadQuad.nu with exponents E and E*D; existing headers/readers remain and facts use its public API. |
| Coordinates / encodings, pp.15–17 | `Idx'/IdDraw/Draw/Seed`, explicit equivalences and faithful codes (`Params`, `Encoding`) | Supplied Boolean and canonical residue/function/product coordinates; no chosen enumeration. Codes retain all fields, including index/draw data. |
| Bucket positions, p.15 | `Buckets.rank/indexMap/bucketMatrix` (`Buckets`) | Increasing positions with Option for absent/overfull/empty grids; total at κ=0. |
| Sparse correction, p.16 | `sparseEntries/sparseLeft/sparseRight/sparseFactor` (`SparseFactor`) | Row-major bounded-support reconstruction, zero padding and no generic rank claim. |
| Equation3 / G1, p.17 | `halfForm/prgPoly/G1/G1_eval` (`Polys`) | Sorted supports, padding by constants, explicit tensor split and coordinate transport. |
| Equations3–4 / G2–G4, p.17 | `correctionPoly/G2/G3/G4/G4_degrees` (`Polys`) | UV correction, precomputed flag-scaled private coordinates and public degree d and private degree2; absent positions contribute zero. |
| 1SdSamp/SdSamp', pp.15–16 | `oneSd/firstGood/packSeed/sdCore/sdSamp'` (`Samplers`) | Exact noise/BAD conditions, first-success flags and one joint draw; no independent index-dependent-event assumption. |
| Eval/correctness, pp.16–17 | `G4_eval_eq/eval'_correct/jls_hasComplexity` (`Correctness`) | Actual sampled-seed correctness, error behavior and packed coordinate transport for every prime/parameter. |
| Claim4.1 p.18 | `E0/seedBitsAt_le/jls_hasPolyStretch` (`Stretch`) | Explicit sufficient threshold, fifth-power payload bound, uniform pp scope and eventual growing seed bits. |
| Load tails p.20 / Claim4.2 pp.19–21 | `bucket_tail`, conditional bounds, `claim42` (`Claim42/Load`, `Bounds`, `Conditions`, facade) | Exact t+1-witness load bound, fixed-index conditional repetition, integer Markov denominator Γ+1 and one eventual cutoff before every pp. |
| H0–H3 / Lemma4.2 pp.18–19 | `hyb/chainGame`, endpoint acceptance and statistical-hop lemmas (`Hybrids`) | Same actual joint laws; unused queries are marginalized only in acceptance probability, not free-program identity. |
| LPN hop, Lemma4.2 p.19 | `LPNAdvice/lpnPre/lpnRed/lpn_hop` (`Reductions/LPN/*`) | Canonical challenged matrix/output, prime-first advice, zero/off-image sentinel and one advice family before all realisers/allκ. |
| PRG hop, Lemma4.2 p.19 | `PRGAdvice/prgPre/prgRed/prg_hop` (`Reductions/PRG/*`) | Actual challenged Boolean index/output, fixed nuisance data and guarded preprocessing; no sampling or G.eval inside preprocessing. |
| Proposition4.1 pp.18–19 | `prop41` (`Security`) | Exact 2κ own-LPN + Boolean-PRG + twice-error majorant, every encoded/layout-coin realiser and κ=0 included. |
| Theorem4.1 p.11 | `jls_secure/jls_subexpSmall/jls_subexpSecure/theorem41` (`Security`) | Shared closure/reindex APIs; exact common exponent min(E*cL,min(E*D*cG,1))/2 chosen before adversaries. |
| Existence / target links, p.11 | raw existence (`Security`); six targets, `jlsSPRG`, conditional efficient existence (`Targets`) | Own E-indexed family assumptions, rational computable parameter and explicit uniform-efficiency hypotheses; no arbitrary-real assumption bridge. |

The noise exponent is rational so that the rounded noise schedule is uniformly
computable. This is the computable-parameter version of the construction; no bridge
from the paper's arbitrary-real assumption is proved here. No loss-of-generality
argument is asserted.

## Uniform fields and conditional assembly (Rule15)

| Primitive | Mandatory uniform fields and exact algorithm law | Current assembly / scope |
| --- | --- | --- |
| `BoolPRG` | `eval_eff`: one polynomial-time map before n/I/seed. `idSamp_eff`: shared SamplesEfficiently on its supplied IdDraw/core; idSamp is the exact pushforward. | Input primitive; this development does not construct a new BoolPRG or omit its efficiency fields. |
| `LPNFamily` | `sample_eff`: one shared complete matrix/secret/noise draw/core contract. Raw specifies exact law and canonical assumption. | `Params.lpnFamily` uses T6 for the actual raw family; its raw reader is retained. |
| `SPRG` | `eval_eff`, `idSamp_eff`, `sdSamp_eff` are mandatory; both samplers derive from complete raw finite draws. | `jlsSPRG` uses T1 for evaluation and T3+T5 for both samplers; T2 supplies efficient polynomial generation. Its raw reader is retained. |

## Phase B statements and witness selection

For each fixed Params P the following are the exact current target definitions,
shown in their `namespace Params` context. They are propositions used as hypotheses,
not unconditional efficiency results. The nine conditional links do not prove them.

```lean
def evalTarget (P : Params) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ κ (pp : PrimeParam κ) (I : P.Idx' κ pp) (sd : P.Seed κ pp),
      f (NUPPT.advInput κ (pairEncode pp.enc
        (pairEncode (P.encIdx' κ pp I) (P.encSeed' κ pp sd)))) =
          List.ofFn (P.eval' κ pp I sd)

def qGenTarget (P : Params) : Prop :=
  ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ κ (pp : PrimeParam κ) (I : P.Idx' κ pp) (j : Fin (P.m κ)),
      ∃ ts : PolyTerms (Fin (P.pubLen κ) ⊕ Fin (P.privLen κ)) (ZMod pp.p),
        f (NUPPT.advInput κ (pairEncode pp.enc
          (pairEncode (P.encIdx' κ pp I) (PolyTerms.encFin j)))) =
            PolyTerms.encTerms (fun z => Candidates.natToList (κ + 1) z.val)
              (fun v => PolyTerms.encFin (finSumFinEquiv v)) ts ∧
        PolyTerms.denote ts = P.G4 κ pp I j

def coreTarget (P : Params) : Prop :=
  CoreComputable (P := PrimeParam)
      (fun κ pp => P.idWord κ pp) (fun κ pp => P.encIdDraw κ pp)
      (fun κ pp => P.encIdx' κ pp) (fun κ pp => P.idCore κ pp) ∧
    CoreComputable (P := P.SdParam)
      (fun κ q => P.sdWord κ q) (fun κ q => P.encDraw κ q.1)
      (fun κ q => P.encSeed' κ q.1)
      (fun κ q d => (P.sdCore κ q.1 q.2 d).seed)

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

def drawSamplerTarget (P : Params) : Prop :=
  DrawSamplable (P := PrimeParam)
      (fun κ pp => P.idWord κ pp) (fun κ pp => P.encIdDraw κ pp) ∧
    DrawSamplable (P := P.SdParam)
      (fun κ q => P.sdWord κ q) (fun κ q => P.encDraw κ q.1)

def lpnSamplerTarget (P : Params) : Prop :=
  SamplesEfficiently (P := fun _ => PrimeSchedule)
    (fun L π => (P.lpnFamily_raw π).sampleWord L)
    (fun L π => (P.lpnFamily_raw π).encDraw L)
    (fun L π => (P.lpnFamily_raw π).encSample L)
    (fun L π => (P.lpnFamily_raw π).sampleCore L)

def Targets (P : Params) : Prop :=
  P.evalTarget ∧ P.qGenTarget ∧ P.coreTarget ∧ P.ReductionTargets ∧
    P.drawSamplerTarget ∧ P.lpnSamplerTarget
```

| Consequence | Uniform hypotheses used |
| --- | --- |
| Evaluator field | T1 (`hT.1`), same map before allκ/pp/I/seed. |
| Index and seed sampler fields | T3 (`hT.2.2.1`) and T5 (`hT.2.2.2.2.1`), each shared draw/core witness specialized without selecting a new machine. |
| LPN sampler field | T6 (`hT.2.2.2.2.2`), ONE U/c/f before every L and prime schedule. |
| Efficient polynomial generation | T2 (`hT.2.1`), actual G4 finite terms and existing sampled correctness. |
| Actual reduction realisers | T4 (`hT.2.2.2.1`), via shared exists_realizesOn_of_preTarget and unchanged RealizesOn; one preprocessing map before schedules/advice/challenges. |

## Non-vacuity and finite boundaries

| Object | Concrete scope and witness |
| --- | --- |
| Public primes | PrimeSchedule.nonempty uses the existing prime-existence result; p=2 fits κ=0. This is existence, not a prime algorithm. |
| Boolean/index/draw domains | Nonempty fields and explicit finite-coordinate equivalences are supplied by primitives or built from canonical modular/function/product equivalences. Empty vector domains are valid function types. |
| Advice | LPN hop lives in Fin(kappaOf L+1), retaining a zero/off-image sentinel. PRG advice has an explicit zero default. Both remain finite/nonempty at all sizes; preprocessing returns[] off image. |
| LPN and construction draws | One complete finite product, nonzero modulus/positive widths and exact cores; no product fair-coin sampler is asserted. |
| Growing-seed stretch | Raw.HasPolyStretch is ∃τ>1,∃κ₀,∀κ≥κ₀, κ≤seedBitsκ ∧ (seedBitsκ:ℝ)^τ≤outLenκ. Constant/zero-length existential vacuity is excluded without imposing a positive-κ domain restriction. |
| Realisers / targets | Shared self/self_take readers establish generic predicate satisfiability, not actual LPN/PRG preprocessing efficiency. Actual realisers and efficient primitive existence remain conditional on T4/allTargets respectively. |

## Deviations and statement preservation

| Tags | Current substantive convention |
| --- | --- |
| Dv1–Dv3 | One-parameter exact powers, finite residue-vector payload and rounded own-family LPN/noise; rational computable parameter, transposed matrix convention and extra integer-log rounding in Γ. |
| Dv4–Dv6 | Supplied indexed multilinear locality, stretch lower bound and composite G4 bidegree. |
| Dv7–Dv11 | Explicit probability analysis, independent published buckets, supplied prime schedules, public degree d from the formal construction, positive degree. |
| Dv12–Dv14 | Fixed nuisance advice before all realisers, NUPPT advantage/common subexponential exponent, conditional realisability. |
| Dv15–Dv18 | Faithful finite coordinates, shared encoded/layout-length realization contract, one complete exact draw and Raw/efficient primitive separation with targets. |

All frozen statement kinds/headers and every public reader remain. The Gate52
commit changes approved prose and delegates inverse definitions/proofs to the
existing public PadQuad API; it does not strengthen/weaken any theorem hypothesis
or silently replace an assumption family. Exactly24 approved declaration prefixes and4 module docs changed; all670 original headers and all public readers remain. The same source commit moves two existing encoding-reader rewrites to the pointwise M6 output equation, clearing unused-hint warnings without changing a witness or statement.

## Gate52 dispositions

| Item | Current disposition |
| --- | --- |
| G52-01 | Exact rational-computability/computable-parameter/no-arbitrary-real-bridge disclaimer in Params and raw/efficient existence docs; no generality claim. |
| G52-02 | Γ doc gives m * Nat.log 2 n / W, integer log before multiplication and natural division, disclosing extra downward log rounding relative to JLS26 p.15; definition/reader retained. |
| G52-03 | kappaOf/kappaOfN delegate to PadQuad.nu at E/E*D. Existing readers use nu_eq; inverse facts use nu_le/nu_pow_le/le_nu, not private bounded-search proofs. |
| G52-04 | Both existing public equivalence families are retained, the approved option. Their five parallel residue/vector/matrix/noise-seed/noise-vector equivalences are explicit duplication. Consolidation plan: a neutral modulus-parametrized shared family with nonzero-modulus data and explicit dimensions, preserving these public names/readers as wrappers. No consolidation is claimed completed. |
| G52-05 | Imports remain: `TCSlib.Cryptography.Asymptotic.UniversalPadding.Parameter` for `PadQuad.nu` and `TCSlib.Cryptography.OneWayFunctions.Basic` for `OneWay.uprob_pi_forall`. Promotion requests seek neutral shared homes for the bounded inverse and uniform-coordinate facts; no private copies avoid dependencies. |
| G52-07 | Public prose now states substantive rational computation, acceptance-probability and seed-growth reasons; campaign labels are removed, required Dv tags retained. |
| G52-08 | One current-head account, delivered compact check authority, received reviews distinguished from executed checks, and every checkpoint's source/delivery identity. No obsolete integration directions or duplicate report appendix. |
| G52-09 | Nineteen facade placeholder descriptions name actual definitions/targets/headline results; imports/exports unchanged. |
| G52-06 / G52-10 | Compact size rule remains resolved with legacy files retained. The corrected extra-subagent breach remains disclosed below. |

## Current axiom rows and full-gate status

| Declaration (area prefix omitted) | Exact axioms |
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
| `Params.realizable_of_targets` | Classical.choice, Quot.sound, propext |
| `jlsSPRG` | Classical.choice, Quot.sound, propext |
| `theorem41_of_targets` | Classical.choice, Quot.sound, propext |
| `exists_sprg_of_targets` | Classical.choice, Quot.sound, propext |
| `exists_sprg_of_targets_subexp` | Classical.choice, Quot.sound, propext |


| Full final validation | Current actual status |
| --- | --- |
| Complete current stored-root dependency/axiom graph | Not performed at this local source milestone; no current full-gate pass is asserted. |
| Exact complete public theorem print comparison | Not performed at this local source milestone; no current full-gate pass is asserted. |
| All original full generated kernel types | Not performed at this local source milestone; no current full-gate pass is asserted. |
| Exact dynamic owner×four seal variants / conservative closures | Not performed at this local source milestone; no current full-gate pass is asserted. |
| All positive/negative reader controls and runtime masks/chunks/EOF | Not performed at this local source milestone; no current full-gate pass is asserted. |

Zero source holes and selected standard-only rows are separate from these full
gates. The earlier complete M0 census/Rule10 results retain their original source
scope; they are not current full-gate passes. Final canonical seals/controls, complete stored axiom census/public print comparison and full frozen kernel types remain outstanding. Source proof completion is saved; end-to-end proof-gate completion is not claimed.

## Delivery scope and process disclosures

Current compact update: 1354361 bytes (1.354361 MB), 1224 custom
inserted UTF-8 lines outside
src/patches, within 20,000,000B and 50,000 lines. The current top manifest covers the
retained exchange tree, while `evidence/compact/M6/SHA256SUMS` covers the new small
result set. The earlier evidence manifest remains its historical snapshot. Legacy
files are retained; no new bulk tools/inputs/scripts/transcripts/raw logs or bundle
are delivered. Only nine compact actual-result files are newly delivered. Source commit hashes and full patch metadata are supplied; worker replay is not run under the received Gate52 instruction. Earlier published payload files remain unchanged.

The full LOCAL raw snapshot is at `/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange/evidence-archives/M6-gate52-raw.tar.gz`, SHA-256
`41ee8902cd06416b21d13ec0e40b185d9ca6f98d0cfafee487380d93d3127aba`, 73945650 bytes. Its capture scope is
the entire persistent local folder `/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange/evidence`, captured after all current source/build/axiom/static/slot checks and before report/publication packaging; no raw archive is sent. This local raw path is the explicit compact-delivery archival
reference; the check authority cited above is delivered compact evidence.

Two corrected process breaches remain: an extra research descendant exceeded the
two-subagent limit and was interrupted; the no-mutation account is based on task
reports, not an independent process audit. Separately, wrappers93883/93983 overlapped
15:07:45–15:07:48UTC; the child was terminated and the prior wrapper released at
15:08:34UTC. Full tagged lines, REAP provenance and correction records are archived.
Whole-history seriality stays false/max2. A verified post-correction serial/closed
suffix is a qualified wrapper fact, not a global host process-cap or child-history
proof. The final checkpoint slot snapshot is closed. Host preflight:6.51GiB headroom and78.23GiB minimum free disk; shared host cap3, this job one Lean at a time since the recorded correction.

Paper SHA-256 is
`bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d`.
No PDF is copied, committed or delivered. Report/top manifest hashes and actual
publication records remain external to avoid circular hashes. No user question is
outstanding.
