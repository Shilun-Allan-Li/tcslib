# io-sprg Phase A — checkpoint 3 (M3), local gates pending

M3's ten original proof bodies and thirteen new theorem-only helpers are completed
in root-confirmed source `c767ee867e76c0b1248cee46d4af5296ffa078d5`.
All133 saved proof-step records are CHECKED_PASS. The final26-owner build and fresh
selected/headline axiom probes are still running/pending; **this report does not
claim all local gates or publication are complete**. M4–M6 and the full final proof
gates remain unfinished. T1–T6 remain the named Phase B efficiency hypotheses.

M0 was frozen at `d10a560b34d58919bc1a5206ce66a444613f94c7` and delivered at
exchange `15946b52d0615fda8afad9ed3c57cfaf5beaaa8d`. M1 source
`19dde91afc384656e7e47cb018057e088d4ded0a` was published at exchange
`10da7fdefd9a44023cc117a672f19e8a3617b81d`. M2 source
`4ecc40c04a001bc87349b7ec368ece309774c28a` was published at exchange
`c1d4f422f071f4a8e346d71a0f00ea3525941eee`. `evidence/delivery/M2.json`
records its successful non-force push, exact5,270-file payload path set and zero
committed SHA-256 mismatches. These remain historical M2 delivery results.

The source branch is `fill/io-sprg` on base
`5ed465f62e4ae0f93ded1a1ba49e807591b589eb`, without rebasing. Delivery writes
only `inbox/fills/io-sprg/` on `exchange/pass-shelat-ch5-8`.

## Source commits and confirmed proof scope

| M3 source checkpoint | Commit |
| --- | --- |
| First M3 source commit | `e966956e25caf9512050ddf5d480a5dec7f4d3de` |
| Second M3 source commit | `bc5d5227a52571ad5e1e9b86219cfcb4987b7771` |
| Proof-complete M3 source head | `c767ee867e76c0b1248cee46d4af5296ffa078d5` |

The final package's COMMITS.tsv must supply exact source-commit subjects and
metadata; no exchange delivery hash is inferred from these source hashes.

M3 fills all ten frozen original obligations (Load5 and Claim425) and adds thirteen
theorem-only helpers: six numerical bounds, six conditional probability bounds,
and one shared semantic joint-law reader. The reader avoids duplicating the same
sampler transport in the decomposition and Cond2 proof; Cond3 also reuses it.
It adds no algorithm or sampler. The decomposition consumer received a fresh root
check after this refactor. Cond2's repaired local index projection closes by rfl;
no projection equality or transport premise was added to a frozen statement.

| Confirmed source/proof quantity | Value | Evidence and limit |
| --- | --- | --- |
| Owned source modules, including both facades | 26 | Current M3 owner inventory; full build pending |
| Explicit source headers | 689 | Proof-complete global map; independent final static refresh pending |
| Frozen M0 headers and statement-prose prefixes | 670 unchanged | Global freeze PASS, no approved prose change |
| Cumulative new theorem-only helpers | 19 (M1 3 + M2 3 + M3 13) | Global map and source inventories; fresh axiom scope pending |
| Existing declarations relocated | 14 | Exact move ledger and retained per-file decls2 rows |
| Saved checked proof steps | 133 CHECKED_PASS | Read all evidence/steps/001–133/step.json records |
| Completed original bodies | 114 (M1 100 + M2 4 + M3 10) | Root-confirmed original/helper classification |
| Remaining original direct holes | 32 | Root-confirmed; no transitive sorryAx-dependent count inferred |
| Source size and width | 26 files;8,657 lines; largest801; width≤100 | Direct byte/line measurement, source hashes match freeze snapshot |

The proof-complete global freeze is a source-bound WORKTREE_CANDIDATE audit whose
capture preceded the final commit. This preparation checked every captured source
hash against the current files, and root confirmed their committed head as above.
It does not mislabel that guard as an independent Git HEAD or kernel-type audit.
The older progress.json still describes an earlier prefix and is not used as final
completion evidence. Source/build/static/axiom/slot gates remain separate.

## Claim 4.2 proof route

The finite load bound counts `(t+1)`-element witnesses inside the overloaded
intersection. For each fixed witness subset, `Equiv.piEquivPiSubtypeProd` separates
selected from unused placement coordinates. Public `uprob_comp_equiv`, `uprob_fst`,
`OneWay.uprob_pi_forall` and `OneWay.uprob_eq_one_div_card` give the exact reciprocal
bucket probability. Public `uprob_exists_le` and `Finset.card_powersetCard` then give
`choose(|S|,t+1)/B^(t+1)`. Union over all B labels and specialize `S=univ` for the
remaining load bounds. This counts all labels and preserves the strict threshold
at every finite parameter, including zero thresholds.

The binomial estimate composes public natural-choice/factorial bounds and the
existing exponential-series estimate. The checked-root API correction to the
staged body supplies the explicit real argument to
`Real.pow_div_factorial_le_exp (k : ℝ) ... k`; discarded/failed attempts remain
archived. The source proof and root's final check are the authority, not the
untested preparation packet.

The locality estimate bounds the expected BAD cardinality by summing per-output
coordinate failures. The existing finite probability/expectation and Markov APIs
supply Cond1's single-repetition bound. The complete index is fixed **before**
independence over noise repetitions is used. Only afterwards is the bound averaged
under the actual index sampler. No uniform distribution on Boolean generator
indices is assumed.

Cond2 fixes all nuisance data while leaving the genuine placement draw uniform.
The small-set condition is handled inside the event; a BAD set larger than Γ is
not assumed away by an extra global premise. Cond3 uses the full-load estimate.
`Params.jointLaw_prob_eq_uprob` transports events through the actual deterministic
index/seed cores from one uniform raw product draw, once, and is reused by the
specialized decomposition and Cond2 proof. This is semantic probability equality;
no equality of free-oracle programs is asserted for unused queries.

The decomposition reuses `Correctness.firstGood_none_iff`. Polynomial bucket-count
bounds and the shared public polynomial/exponential growth APIs yield one eventual
cutoff. The final frozen statement is
`∃ κ₀, ∀ κ ≥ κ₀, ∀ pp : PrimeParam κ, errProb κ pp ≤ 2⁻κ`:
the cutoff precedes the public prime. Internal positive/large-κ helper hypotheses
do not change that statement or impose a new positive-κ premise on the raw family.
The rational δ convention remains SP-W1; no new analytic assumption on δ or the
noise width is introduced for Claim 4.2.

## Original M3 declarations

These anchors and saved checked steps refer to the proof-complete M3 source.
Fresh all-owner build/axiom gates remain pending.

| Declaration (area prefix omitted) | M3 source anchor | Saved step |
| --- | --- | --- |
| `Params.errProb_nonneg` | `Claim42/Defs.lean:135` | 116: CHECKED_PASS |
| `Params.badSet_expect_le` | `Claim42/Defs.lean:146` | 117: CHECKED_PASS |
| `Params.cond1_prob_le` | `Claim42/Defs.lean:274` | 118: CHECKED_PASS |
| `Params.errProb_le_decomposition` | `Claim42/Conditions.lean:268` | 119: CHECKED_PASS |
| `Params.claim42` | `Claim42.lean:58` | 133: CHECKED_PASS |
| `Internal.binomial_bound` | `Claim42/Load.lean:54` | 111: CHECKED_PASS |
| `Internal.bucket_tail` | `Claim42/Load.lean:91` | 112: CHECKED_PASS |
| `Internal.some_bucket_tail` | `Claim42/Load.lean:177` | 113: CHECKED_PASS |
| `Internal.full_bucket_tail` | `Claim42/Load.lean:194` | 114: CHECKED_PASS |
| `Internal.some_full_bucket_tail` | `Claim42/Load.lean:206` | 115: CHECKED_PASS |

## New M3 theorem-only helpers

All thirteen helper bodies have saved CHECKED_PASS records. Fresh selected-owner
axiom checks and final overlap/admission evidence are distinct gates.

| Declaration (area prefix omitted) | M3 source anchor | Saved step |
| --- | --- | --- |
| `Internal.bucket_count_upper` | `Claim42/Bounds.lean:41` | 120: CHECKED_PASS |
| `Internal.bucket_count_lower` | `Claim42/Bounds.lean:57` | 121: CHECKED_PASS |
| `Internal.prefactor_eventually_le_two_pow` | `Claim42/Bounds.lean:81` | 122: CHECKED_PASS |
| `Internal.binomial_ratio_quarter` | `Claim42/Bounds.lean:131` | 123: CHECKED_PASS |
| `Internal.smallset_bucket_tail_quarter` | `Claim42/Bounds.lean:159` | 124: CHECKED_PASS |
| `Internal.capacity_bucket_tail_quarter` | `Claim42/Bounds.lean:195` | 125: CHECKED_PASS |
| `Internal.cond1_single_le_quarter` | `Claim42/Conditions.lean:48` | 126: CHECKED_PASS |
| `Internal.cond1_repetitions_fixed_index` | `Claim42/Conditions.lean:83` | 127: CHECKED_PASS |
| `Internal.cond1_all_fixed_index` | `Claim42/Conditions.lean:114` | 128: CHECKED_PASS |
| `Internal.cond1_all_joint` | `Claim42/Conditions.lean:141` | 129: CHECKED_PASS |
| `Internal.cond3_joint_le_quarter_pow` | `Claim42/Conditions.lean:161` | 131: CHECKED_PASS |
| `Internal.cond2_sparse_joint_le_quarter_pow` | `Claim42/Conditions.lean:193` | 132: CHECKED_PASS |
| `Params.jointLaw_prob_eq_uprob` | `Claim42/Defs.lean:96` | 130: CHECKED_PASS |

## Module organization and frozen interface preservation

The approved split moves fourteen existing declarations out of Claim42.lean,
preserving their FQNs, statement headers and pre-sketch prose. Claim42.lean keeps
the frozen `Params.claim42` statement as the public facade. The fifteen-row move
ledger includes that stationary claim as well as the fourteen actual moves.

| Module | Role and dependencies |
| --- | --- |
| Claim42/Load | Existing finite binomial and placement bounds |
| Claim42/Defs | Cond1/Cond2/Cond3, joint law/error definitions and readers; locality/Markov bounds; shared joint-law probability reader |
| Claim42/Bounds | Rounded bucket and numerical tail bounds; imports Defs and Load |
| Claim42/Conditions | Fixed-index/repetition/placement bounds and decomposition; imports Bounds and the precise existing Correctness module |
| Claim42 | Public claim42 body and facade imports |

Correctness depends on Samplers, so the additional owned import is acyclic.
The split introduces no new external Mathlib import root. This is a source
organization decision authorized by root's best judgment while preserving frozen
mathematical interfaces. The five Claim42 files measure102 facade,307 Defs,236 Bounds,368 Conditions and
212 Load lines, respectively; every line has width≤96. The full exact import
closure/static refresh remains pending. No file exceeds1,000 lines.

The former per-file decls2 output legitimately contains paired REMOVED/ADDED rows
for the fourteen moves. Those rows are retained, not discarded. The new global
freeze guard rejects duplicate FQNs, compares every frozen kind/normalized header
and statement-prose prefix before `**Proof sketch.**`, and reconciles each move
against the explicit ledger with unchanged headers. New entries are separately
reported theorem/lemma helpers. Full frozen kernel-expression types are a separate
required final check, including generated public fields/constructors.

Root's proof-complete global guard PASS is archived in
`evidence/checks/M3-proof-complete-global-freeze/`. All26 captured source hashes
match the current proof-complete files;670 frozen headers/prose prefixes are
preserved, fourteen moves are exact and nineteen added helpers are separately
reported. Kernel types/helper axioms remain separate gates.

## Current local checks and final-gate limits

| Required final M3 evidence | Status in this draft |
| --- | --- |
| Final source head and exact26-owner inventory | Root-confirmed c767ee867e76c0b1248cee46d4af5296ffa078d5; captured source hashes match proof-complete freeze |
| Full owner compilation, current source/log/object hashes, rc0 and both error forms zero | PENDING_ROOT_RECORDS |
| All133 saved proof-step records | Confirmed CHECKED_PASS by direct reading of all saved records |
| Ten original bodies and thirteen helpers | Bodies have saved CHECKED_PASS; fresh standard-only axiom gate PENDING_ROOT_RECORDS |
| Current completed-owner and headline print scopes/hashes | PENDING_ROOT_RECORDS; no print count guessed |
| Global670-header/prose freeze, exact fourteen moves, helper census | Proof-complete source-bound PASS;689 current headers,19 new helpers |
| Style, sk15, widths, max-file size, clash and baseline campaign comparison | PENDING_ROOT_RECORDS |
| Phase A/import/contract/realiser/PDF boundary | PENDING_ROOT_RECORDS |
| Exact helper name/shape and isolated exact?/apply? overlap probes | PENDING_ROOT_RECORDS; invalid harness attempts kept separate |
| Fresh tagged-wrapper audit after the last root check | PENDING_ROOT_RECORDS |
| M3 replay, bundle, exact manifests and successful publication | PENDING; no delivery hash or successful push claimed |

M0's full stored-constant census, typed dump, dependency graph and four-variant
Rule10 matrix remain **historical M0 evidence until the final fresh gates**.
At M0 there were22 owners,88 seals plus96 controls,1036 stored constants,
948 public kernel types and511 theorem prints. These are neither current M3
counts nor M3 proof passes. M1/M2 selected theorem prints likewise retain their
published limited scopes; no transitive sorryAx-dependent number is inferred by
subtracting filled source holes.

Root's final audit must discover all current owners, including Basic and the new
Claim42 modules (and any later LPN splits), before generating seals/census/controls.
The prepared V2 audit adapters derive exact owners from base→committed HEAD,
require owner×four complete seals and all paired reader controls, retain full
conservative closures/request/runtime/EOF guards, bind source/log/object/import
environments, and support an empty final obligations TSV. They are **untested
candidates**, not gate results. Only the unchanged-byte global freeze tool has a
root-reported execution result. Final source/helper overlap admission remains a
separate required record.

## Unchanged quantifiers, targets and earlier judgments

SP-W1 uses rational δ with real analytic coercions. SP-W2 asserts only the two
semantic acceptance equalities needed by the hybrid bridge, not equality of
free-oracle programs with an extra unused query. SP-W3 requires growing seed size
as well as the polynomial output bound; M2 proved both for the construction.
The public prime remains an input and all constructions accept every schedule.
Canonical LPN and Boolean assumption challenge encodings remain unchanged.

Rule15 primitive evaluator and exact-draw sampler efficiency fields remain
mandatory. Target witnesses are selected before every applicable size, schedule,
prime or input. In particular, T6 chooses one shared sampler witness before all
prime schedules; it is not a family of separately selected witnesses after π.
T1/T3/T5/T6 will fill the respective primitive fields only conditionally on the
unproved target propositions. No Phase B machine/sampler/efficiency construction
is introduced here. M4's advice-family-before-all-realisers/all-κ requirements and
M5's fixed shared subexponential exponent remain the frozen later obligations.

The four historical mathematical tables below retain the complete earlier
fidelity/deviation, Rule15 field, target-selection and nonvacuity detail. Their
historical line references are not altered to pretend they are current anchors.
The separate source-c767ee8 appendix follows declaration identity and handles moved
Claim42 declarations explicitly.

## Frozen fidelity, Rule15 and non-vacuity tables

All four mathematical tables below are byte-exact M0 snapshots. Their line numbers
are **historical M0 anchors**; current draft anchors are indexed separately.

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


## Current M3 source declaration anchors

These locations refer to root-confirmed source
`c767ee867e76c0b1248cee46d4af5296ffa078d5`. Every captured source hash matches
the root's proof-complete global freeze snapshot; the source-head file and owner
inventory identify the same commit. This preparation did not independently run Git.
The complete TSV retains explicit structure-field anchors from unchanged M2 files.
Generated constructors/recursors/inherited fields remain represented by their structure.
This lexical appendix is not a typed kernel census or proof-status table.

| Declaration (area prefix omitted) | Worktree source anchor |
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
| `Internal.binomial_ratio_quarter` | `Claim42/Bounds.lean:131` |
| `Internal.bucket_count_lower` | `Claim42/Bounds.lean:57` |
| `Internal.bucket_count_upper` | `Claim42/Bounds.lean:41` |
| `Internal.bucket_tail` | `Claim42/Load.lean:91` |
| `Internal.capacity_bucket_tail_quarter` | `Claim42/Bounds.lean:195` |
| `Internal.cond1_all_fixed_index` | `Claim42/Conditions.lean:114` |
| `Internal.cond1_all_joint` | `Claim42/Conditions.lean:141` |
| `Internal.cond1_repetitions_fixed_index` | `Claim42/Conditions.lean:83` |
| `Internal.cond1_single_le_quarter` | `Claim42/Conditions.lean:48` |
| `Internal.cond2_sparse_joint_le_quarter_pow` | `Claim42/Conditions.lean:193` |
| `Internal.cond3_joint_le_quarter_pow` | `Claim42/Conditions.lean:161` |
| `Internal.encodeList_injective_of_fixedWidth` | `Basic.lean:49` |
| `Internal.encodeList_length_of_fixedWidth` | `Basic.lean:82` |
| `Internal.eventually_seed_relative_gap` | `Stretch.lean:254` |
| `Internal.full_bucket_tail` | `Claim42/Load.lean:194` |
| `Internal.prefactor_eventually_le_two_pow` | `Claim42/Bounds.lean:81` |
| `Internal.smallset_bucket_tail_quarter` | `Claim42/Bounds.lean:159` |
| `Internal.some_bucket_tail` | `Claim42/Load.lean:177` |
| `Internal.some_full_bucket_tail` | `Claim42/Load.lean:206` |
| `Internal.stretch_gaps` | `Stretch.lean:223` |
| `Internal.w_lower` | `Stretch.lean:204` |
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
| `Params.Cond1` | `Claim42/Defs.lean:43` |
| `Params.Cond2` | `Claim42/Defs.lean:56` |
| `Params.Cond3` | `Claim42/Defs.lean:71` |
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
| `Params.badSet_expect_le` | `Claim42/Defs.lean:146` |
| `Params.bucketBound` | `Encoding.lean:350` |
| `Params.cap` | `Params.lean:132` |
| `Params.chainGame` | `Hybrids.lean:86` |
| `Params.chainPublic` | `Hybrids.lean:69` |
| `Params.claim42` | `Claim42.lean:58` |
| `Params.cond1_prob_le` | `Claim42/Defs.lean:274` |
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
| `Params.errProb` | `Claim42/Defs.lean:123` |
| `Params.errProb_le_decomposition` | `Claim42/Conditions.lean:268` |
| `Params.errProb_nonneg` | `Claim42/Defs.lean:135` |
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
| `Params.jointLaw_prob_eq_uprob` | `Claim42/Defs.lean:96` |
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
| `jls_hasPolyStretch` | `Stretch.lean:428` |
| `jls_secure` | `Security.lean:102` |
| `jls_seedBits_le` | `Stretch.lean:404` |
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

## Source and host disclosures

The paper was verified in place at SHA-256
`bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d`.
No PDF is copied, committed or delivered. The initial memory/disk observations
and the preflight retry remain historical measurements in the M0/M1/M2 reports;
this draft makes no new resource measurement claim.

Both historical instruction breaches remain disclosed. An extra research
descendant exceeded the whole-job two-subagent limit and root interrupted it.
No Lean/cache/push/source mutation was reported for that descendant, based on
task reports rather than an independent process audit; no further agents were
spawned. Separately, tagged wrappers93883 and93983 overlapped at
15:07:45–15:07:48UTC; the recorded search child was terminated and the prior
wrapper released at15:08:34UTC. The records are
`evidence/host/team-limit-correction.json` and
`evidence/host/search-process-correction.json`.

The exact-exception slot checker preserves every tagged line and REAP provenance,
rejects any other overlap, records whole-history seriality false and maximum two
tagged wrappers, and tests the post-correction suffix separately. Root must run
it again after M3's last check. No unqualified whole-job seriality, global host
process cap or complete child-process-history claim is made.

## Delivery and continuation

M3 proof bodies and source anchors are now confirmed. Local gates, packaging and
publication remain pending. After root supplies the final records, replace only
evidence-backed pending entries; keep the current committed-source/hash binding. Preserve
the four archived M0 mathematical tables byte-for-byte. Packaging must replay all
source patches at the pinned base with exact commit hashes (including M0's empty
marker), verify the bundle, scan every intermediate tree for PDFs, copy committed
source only and verify exact source/evidence manifest path sets and hashes.

Then continue M4–M6 and the full final source/kernel/canonical seal gates. No user
question is pending. This report preparation performed static reads and temporary
writes only; it did not run Lean, Lake, Git, cache tools, implementation edits or
agents. Its pure producer was executed only to generate this temporary draft and
anchor/provenance artifacts.
