# Gate 06: four external statement audits of ch. 5–8 (S4; round 1)

**Current status,2026-11-08 PST:** all four user-dispatched Codex statement audits are CLOSED:
06A0B/0M/2m,06B0B/0M/5m,06C0B/0M/4m,06D0B/0M/4m. Verbatim findings and
separate resolutions-06A/B/C/D-r1.md preserve their pins and evidence limits.
The combined unapplied comment proposal in review-r1-c/ covers15 minors/13 files,
jointly applies and preserves exact noncomment bytes. No proof is completed.
PR #232 remains draft at3f6db40e1688c4a0bb922c9575dd3bd2157a650b; accepted S2 is
absent from that head. A clean merge-tree preview is not a combined-source check.
Final comment application/current-source verification remain before landing.
Under the user's cautious full221-path cleanup screen, all39 direct crypto proof
targets are currently blocked; no new fill or proof branch is prepared. The issued
round1 account below is historical and unchanged in the pinned Git snapshot.

**Round 1: common preparation complete; ready for staging (2026-11-07).**
Audit source: `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`; checked comparison ancestor:
`eee107e92a7db11f1f8c98a5c2867304f57ddc54`; draft PR #232. Historical prong heads are provenance only.
This document records neither staging/user dispatch nor external gate closure. Auditor: **Codex**;
return findings Markdown in the audit chat, with no commit or push requested. The user dispatches
all four audits after reviewed bundles and external pins are staged.

The user's 2026-11-04 gating ruling supersedes the original single-gate proposal: S2a and S2b
have API gates, and **each prong has its own statement gate before that prong's fills**. Gate
06A–D use one reconciled integration source and may be audited in parallel after the common
preparation below. No A → B → C → D audit order was imposed.

- **What is audited:** definitions, statements, docstrings and proof sketches against [PS10]
  and the second sources cited per item. Proofs are out of scope except the short proofs that
  carry a definition's correctness (including the protocol phase/correctness lemmas).
- **The tree:** S2b/#195 and the repaired ch. 2–4 API are merged; all four prongs and the
  repaired PAC/main transfer are incorporated. The current source includes the integration
  repairs below, public reading interfaces, four topic facades and their root exports.
- **Every pack carries:** relevant S2a/S2b APIs as context; the inventory and errata; the decision
  log and applicable rulings; `policy.md`; the exact source bundle/manifest; and primary-source
  access information in `source-manifest.md`. Goldreich drafts are linked for personal retrieval
  rather than redistributed. The author-hosted PSV copies have distinct recorded hashes from
  the historical publisher uploads; no byte identity is asserted.
- **Delivery:** the recorded external-auditor choice is Codex, with findings Markdown returned
  in chat. The user dispatches the jobs; the maintainer intakes and records the findings.

## Packs

Paths below are under `TCSlib/Cryptography/` unless qualified. Historical prong heads are
provenance only; none is the source pin for these integrated audits.

| Pack | Content | Integrated files | Items |
|---|---|---|---|
| 06A | Authentication, ch. 5 | `Authentication/{Defs,PRFMAC,Lamport,DLHash,HashAndSign}` and facade | Defs 134.1, 134.2, 135.1, 136.2, 136.a, 140.1; Protocols 134.3, 137.1, 142.2, 144.2; Theorems 135.4, 137.2, 142.3, 144.1 |
| 06B | Secure computation, §6.2 | `SecureComputation/{Defs,ObliviousTransfer,SpecialEncryption,SpecialEncryptionSecurity,Garbling,GarblingSpecial,GarblingSecurity,Hybrid,Compose,ComposePhases,ComposeSecurity,Yao,YaoReal}` and facade | Def 155.1; Alg 157.2, Claim 157.a; Constr 158.a, Claim 159.a; Def 160.a, Prot 160.4, Prop 161.5; Prot 162.6, Thm 163.7; the hybrid composition statement |
| 06C | Composability, ch. 7 | `Composability/{Defs,PRFScheme,CCA2Scheme,PublicKey,NonMalleable,SimNonMalleable,SequentialZK,ThreeColoring}` and facade | Defs 168.1, 171.5, 172.6, 173.7; Thm 168.2, Claim 169.a, Alg 169.3, Thm 170.4, Claim 172.a, Thm 174.8, optional Thm 175.9, Thm 175.1; the explicit sequential 3COL corollary |
| 06D | Randomness, ch. 8 | `Randomness/{Extraction,Learning,BPPBridge,Derandomization}` and facade; `LearningTheory/PAC/{Defs,Prediction}`, `InformationTheory/Samples` and their dependencies as already-gated context | Def 179.a; Thms 179.1, 180.1, 183.6 |

## Source bundles and common records

Each pack identifies its primary paths and already-gated context. Its prepared source-only
bundle contains their complete TCSlib import closure at the frozen source, plus `TCSlib.lean`
for root-export context, with raw bytes, hashes and revision-qualified provenance. Shared owner-side
interfaces are context rather than fresh prerequisite statement audits. The seven separately
verified import/option-only files are `TCSlib.lean`, the four topic facades in the table above,
`TCSlib/InformationTheory.lean` and `TCSlib/LearningTheory/PAC.lean`; they are outside theorem
sealing, not foreign-definition/name exemptions. Root-export elaboration is not claimed.

Common record paths are root `policy.md` and `PassShelatChapter5-8Plan.md`;
`briefs/pass-shelat-ch5-8/{inventory-ch5-8.md,duplication-ledger.md}`; this directory's
`PLAN.md`, `source-manifest.md` and the relevant `06A-pack.md`–`06D-pack.md`; and the final
preparation evidence index with every cited acceptance artifact. Gate 06D also carries
`gates/05-pac/{findings/gate05-pac-r3-findings.md,resolutions-r3.md}` under the campaign.
The four source-only bundles and source manifests are prepared and verified; records bundles
and exchange staging follow the reviewed D0 records commit. The exchange READMEs and dispatch
prompts pin that records commit, records/common archive hashes and the final index hash
externally. No such self-referential pin is embedded in these records. Third-party source
delivery follows `source-manifest.md`, including official-link Goldreich/PSV access.

## Statement-phase findings retained for the auditor

- Algorithm 99.1's `Dec` refuses malformed ciphertexts (#193); its omission made the CCA1 claim
  false. The repaired guard remains in the shared base.
- `π′`'s tag covers `(r,c₁)`, not only `c₁` (the inventory erratum).
- Public-key games use canonical ciphertext padding and refuse non-canonical strings.
- Non-malleability follows [PSV06] and [PSV07]: CPA equivalence, and SIM ⇒ IND for every attack.
  The two maintainer sketches remain audit subjects; [PSV07] defers their proofs.
- `CRH` carries domain/range membership tests; Thm 144.1 retains its full-domain hypothesis.
- Thm 175.1 retains `Protocol.ProverBounded`; D8 alone does not bound honest prover messages.
- OT has five messages under D8. `SamplerCanonical` is now a theorem from the collection
  contract, not a security hypothesis. The canonical-encoding equation `henc`, polynomial-time
  evaluator hypothesis `hH`, and `EnhancedHardCore` remain explicit.
- Yao is audited first as an OT-hybrid protocol, with its real form a corollary of the separate
  honest-but-curious composition statement ([Gol04, §7.3], Q-5).

## Integration changes present in the frozen source

1. **Canonical OT.** `SamplerCanonical` is derived by `Collection.sample_eq_encD`. The local
   decoding specification used by correctness follows from the retained canonical-only `henc`
   through `Collection.apply_of_decD`; callers no longer supply the old decoder-wide `hspec`.
   `hH : PolyTimeComputable H` and `EnhancedHardCore` are retained in OT and the real Yao theorem.
   Enhanced security still exposes the receiver's sampler coins to the predictor; it was not
   replaced by ordinary hard-core security. Def 155.1 includes efficient parties and bounded
   honest messages.
2. **Sequential ZK and 3COL.** The duplicate `ProverBounded` is deleted; the canonical definition
   is in `ZeroKnowledge/Interaction.lean`. `PerfectZK.seqRep` follows from `StatZK.seqRep` at zero
   error through `perfectZK_iff`. `PerfectZKAbort.seqRep` uses `PerfectZKAbort.statZK` and has
   statistical error `Q(n)·2^{-n}`; it does not claim exact perfect ZK. References use `[Gol01]`.
   `Composability/ThreeColoring.lean` adds `negligible_colSeqSound` and
   `colSeq_efficientProverProof_zk` at `Q(N)=2(N+1)^2`, with the explicit scheduling/count
   deviations. The corollary depends on the still-admitted generic repetition statements.
3. **PAC/main transfer.** Gate 05 closed, #194 reached `main`, and the repaired PAC layer is in
   the integration source. `PACLearnable` stays removed. `FinDist.probTrue` is now in
   `InformationTheory/FinDist.lean`, with its reading equation; Samples and PAC depend on that
   upstream home. The weak-learning confidence/amplification qualifications remain in force.
4. **Interfaces and exports.** Ordinary/predicate readers and explicit structure-field equations
   were added beside the prong definitions; machines are read through run/coin contracts.
   Public owner-side readers needed by the integration were added to base modules. The four
   topic facades and `TCSlib.lean` expose the new modules. T1/T2 sketches cite the extended
   public efficiency interfaces rather than claiming that the older statements suffice.
5. **DL-6/DL-7.** One `TCSlib.Cryptography.coinBlock`, its equation and length lemma live in
   `Asymptotic/Adversary.lean`; BlockEncryptor, Lamport, sequential ZK and both GI layers use it.
   Lamport's duplicate padding theorem is deleted. Lamport and CCA2 use
   `Collection.ofFn_padFin_of_le` from `Asymptotic/CollectionsHelpers.lean`, simplifying the
   zero-length padding suffix in the equal-length case. These repairs are present in the frozen source and covered by the completed common
   verification; landing remains subject to the external gates; cleanup retains its post-S2 order.

## Exact preparation and audit order

1. **Closed prerequisite interfaces are context.** S2a/S2b and the repaired ch. 2–4 interfaces
   are present. For 06D, Gate 05's closed findings/resolutions and repaired PAC transfer are
   context. The old holds for #195, Q-5, honest-party efficiency and #194 are resolved.
2. **Common verification is complete at the frozen pin.** The scope, native reconciliation,
   seals, controls, axioms, source scans, style/API and source-only bundles are reconciled below
   and in `briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/FINAL-EVIDENCE.md`. Retained inherited failures are failed evidence, not exclusions or
   a whole-source pass. The separate S2 candidate-host fill is not incorporated.
3. **Finish round-1 staging.** Review these six records and the four source-only manifests,
   make the D0 records commit, build the matching records/common bundles, and stage all four
   exchange packs. Pin the records commit, records/common archive and final-index hashes in
   each exchange README and dispatch prompt, outside the pack/PLAN/manifest bytes. The source
   bundle hashes and source-only manifests are stable because they contain only source data.
   This document does not attest that staging or dispatch has happened.
4. **The user dispatches all four Codex audits.** They may run **in parallel** after the common
   preparation and reviewed staging. Each auditor returns its named findings Markdown in the
   audit chat; no commit/push is requested. Receiving auditors verify access and report exact
   unavailable source comparisons. Repair findings and repeat the affected audit until its
   0-blocker/0-major closure; no external gate is closed by the common checks.
5. **Each prong's fills follow its own statement-gate closure.** There is no A→B→C→D audit
   dependency. S2 candidate-host acceptance/landing remains separately pinned, and cleanup
   part 2/efficiency retain their standing post-S2 order. Bundle only the Gate06 source at the
   declared head. Any later source or target advance needs source/root-export equivalence or
   refreshed comparison and source-matched affected/downstream verification.

## Completed common preparation

The common evidence is reconciled at the source/base above. The final index is
`briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/FINAL-EVIDENCE.md` and its machine summary is
`briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-final-r1/FINAL-SUMMARY.json`.
The final index/common archive hashes and the records commit/bundle hashes are pinned externally
in the exchange README and dispatch prompt, outside these pack bytes.

| Common check | Completed outcome and limit |
|---|---|
| Scope/native | 61 changed Lean paths: **54 math modules + 7 import/option-only facades**. All 1,108 library sources match the snapshot; 467 native source/object/prerequisite records are reconciled after 182 affected checks. `TCSlib.lean` was **not elaborated**. |
| Full-source seals | All 54 harnesses valid: **37 source passes, 17 source failures, 138 diagnostics in 110 unchanged full header/proof blocks**. No new/touched failing block or home-induced read was identified. All failures remain failed observations. |
| Failure/debt disposition | Exact historical-key normalization gives **62 historical / 48 additional observation keys**. Additional observations are retained inherited debt, not new source violations or failure exclusions. |
| Sensitivity controls | All **11** verified: 5 unsealed negative passes, 5 sealed sole-proof failures, 1 sealed published-reader pass. |
| Axioms/admissions | **2,881 actual identities**: 2,835 standard-only, **46 admitted-dependent** (33 direct statements + 13 derived dependencies), 0 unexpected axioms. The same 46 names/dependencies remain; substantive proof completion is not claimed. |
| Source scans/C3 | **C1: 142 raw hits + 10 selected-open supplement observations; C2: 10 rows; C3: 3 retained legacy pairs**, not zero. The exhaustive TCS record has 134 inherited candidates: 131 debt + 3 exact recorded notation items. All 18 non-TCS raw hits are unchanged too. Composite new/touched review identifies **0 foreign-body violations / 0 unresolved items**. |
| Style/API | 10 inherited style findings, 0 new; each complete prong's plain/check8b runs returned 0. This is not an all-library lint or Rule10-clean claim. |

The completed C3 R2 census covers all owned types/values, including opaque/private/generated
constants; its exact per-module root sets match all 2,881 identities. Both metadata controls
pass. The private BlockEncryptor pair is an older eqn-term observation outside the 110 failed
blocks; counts are not blindly added. Invalid R1 C3 and earlier harness attempts remain labelled
invalid. No failure, notation reference or inherited read is filtered or waived.

S2's separate candidate-host fill (PR #231) is **not incorporated or attested** by this Gate06
source. Earlier closed S2a/S2b APIs remain context. Further source repairs require renewed
source-matched affected/downstream checks and audit pins.

## Final verification detail and limits

- Native reconciliation uses earlier successful same-chat objects plus **182 affected checks**;
  it is not a second cold 467-module build. The root export and all seven facades are verified
  as import/option-only context; `TCSlib.lean` was not elaborated.
- The fresh collector has 1,039 term pairs within 55,373 complete-closure pairs. The 46
  admitted-dependent names/axiom sets equal the initial e9 census. Lexical `sorry` is 511→544;
  zero `admit`/`axiom` commands on both sides. Public-header parser rows are 816 added / 7
  removed / 13 changed, not actual elaborated declaration counts or proof completion.
- C1's 142 raw hits are 124 TCSlib + 18 non-TCS. Ten named-open uses selected by
  `open PrivateKeyScheme (encodeList)` are separately retained, giving all 134 inherited TCSlib
  candidates (131 debt + exactly 3 recorded `PolyExpr.eval` notation items). The scanner's
  named-open limitation is disclosed; it does not produce a zero claim. All ten C2 rows are
  retained unchanged failures. The three legacy C3 pairs include the private BlockEncryptor
  proof at historical eqn-term row 713 outside the 110 failed blocks; all pairs/homes remain
  recorded. Neither counts nor the 764-row historical inventory are blindly added together.
- Exact normalization of historical `_root_.Complexity.NUPPT.computes_iff_uprob` yields
  62 historical / 48 additional observation keys. The earlier conservative 61/49 proposal
  remains immutable. Both Encoding keys are historical. No failing complete block or
  home-induced read was newly introduced; no full native base environment/base seal rerun
  is claimed. Every raw failure/observation is retained.
- The first C3 final attempt is an invalid parser/synthetic-sorry refusal, not a census. R2
  changes only Cache field layout; it completes and its exact 54-module/2,881-name extraction
  retains three legacy pairs and zero new/touched pairs. Its two metadata controls supplement
  the eleven seal controls. Earlier invalid BPPBridge attempts and the e9 51-file survey remain
  historical, not substitute final coverage.
- The final style comparison covers all 61 paths (10 inherited/0 new, style rc1); prong plain
  and check8b runs each return 0. This is not an all-library campaign-lint pass. Existing exact
  notation/style exceptions remain precise; no blanket abbreviation/body-reading waiver is
  introduced. The checked base's documented source/root-export equivalence is retained in
  `evidence-static-final-r1/comparison-base-equivalence.json`; a later target advance requires
  a fresh documented equivalence check or actual-base comparison.

## Round 1 source identities and external records pins

| Pack | Exchange source bundle | SHA-256 | Source sections | Source-only manifest SHA-256 |
|---|---|---|---:|---|
| 06A | `outbox/gates/06A-r1-gate/gate06A-source-bundle.md` | `fdad5c0bdd23d421f6351c3e8d37587fc09fc8a0662ba84db31e47cea26be8a2` | 125 | `fca279c40d91758168efc9d7a729a49f2641ba84d2cb0609afcbb567c68aae7c` |
| 06B | `outbox/gates/06B-r1-gate/gate06B-source-bundle.md` | `66f3ac9e11a1100a276f3336f54ee4a6f5b3a109e5c647523575b95e828ef9ff` | 129 | `e33f8aa437668a506a31a5f7c1c2e3d2632ff999023be5d2847e324cbcd83990` |
| 06C | `outbox/gates/06C-r1-gate/gate06C-source-bundle.md` | `15dfbca8d2d255b5b31bd71393a8c87bd7b88946cd46c9a3a2ff32a65a34654b` | 171 | `f649a5fa5ff1dee8395586345f0dc1a22efab783e850f46185e7230fbfb1406b` |
| 06D | `outbox/gates/06D-r1-gate/gate06D-source-bundle.md` | `3a167712e1748f7a121aa01455e060977a225bb98f5ea144071c087c568a64cd` | 185 | `8947c1090298d80034c616b1492792707f91016528759d0b8047478a4ef97f90` |

The four `06A-source-manifest.json`–`06D-source-manifest.json` files in this gate directory
contain source data only: head/base, primary modules, import-edge closures, raw revision/path/
byte/hash rows and source-bundle filename/hash. Each pack embeds its own manifest hash. Records
commits and records/common archive hashes are intentionally pinned only by exchange READMEs
and user dispatch prompts. The final evidence index is cited by path above; its hash is an
external staging pin, so later prose polish cannot create a self-reference.

Primary sources are the common provided exact tracked PS10 course PDF and official author
links/version limits in `source-manifest.md`. Receiving auditors must verify access and name
unavailable comparisons in their Markdown findings. Goldreich/PSV PDFs, extracted full text and
rendered pages are not redistributed. Draft-to-publisher equivalence and deferred proofs remain
explicit audit subjects. S2 PR #231 is not part of this source or this attestation.

**Not yet clear to merge — all statement gates close; comment application and combined-source verification remain.**
