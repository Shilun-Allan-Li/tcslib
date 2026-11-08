# Gate 06D (Pass–shelat ch. 8, randomness): external statement audit pack

**Round 1: common preparation complete; ready for staging (2026-11-07).**
Audit source: `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`; checked comparison ancestor:
`eee107e92a7db11f1f8c98a5c2867304f57ddc54`; draft PR #232. Historical prong heads are provenance only.
This document records neither staging/user dispatch nor external gate closure. Auditor: **Codex**;
return findings Markdown in the audit chat, with no commit or push requested. The user dispatches
all four audits after reviewed bundles and external pins are staged.

**What is audited:** [PS10] ch. 8 as formalized in `TCSlib/Cryptography/Randomness/`, with the PAC layer of gate 05 as context: definitions, statements, docstrings and proof sketches, against the
sources. Proofs are out of scope, except the short ones that carry a definition's correctness
(`correct` fields, length lemmas). The deliverable is **`gate06D-findings.md`**.

**Sources for round 1 (receiving-auditor access must be verified):** [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed.,
January 2010 (book page = PDF page − 12), §8.1–8.3, book pp. 179–184.

## Scope

| Item | Where | State |
|---|---|---|
| Def 179.a (the learning game) | the PAC layer (`TCSlib/LearningTheory/PAC/`, gate 05), with `Randomness/Learning.lean` | defined |
| Thm 179.1 (PRFs give an unlearnable class) | `Randomness/Learning.lean` | (a), (c) proved; (b) stated |
| Thm 180.1 (PRGs give `BPP ⊆ DTIME(2^{n^ε})`) | `Randomness/Derandomization.lean`, with `BPPBridge.lean` | stated; the bridge proved |
| Thm 183.6 (no efficient one-bit extractor for efficient sources) | `Randomness/Extraction.lean` | stated |

## Prior findings (verify the repairs)

1. **Thm 183.6 needs a polynomial-time `Ext`** (source gap: "`X` is computable since `Ext` is").
   It is stated at every `n`, which is stronger than the source's existential.
2. **Thm 179.1** uses the repaired information-theoretic PAC layer (#194, Gate 05 closed
   before its merge into `main`), now incorporated with `PACLearnable` removed. The bridge
   concerns a specified learner at fixed parameters under the uniform distribution. Starting
   from [KV94, §4.1]'s success probability `1/q`, confidence below the prediction gap may
   require amplification and a different learner, with its sample count, runtime and edge
   accounted for.

## PAC/main and API integration context

Repaired `LearningTheory/PAC/{Defs,Prediction}` and `InformationTheory/Samples` are present;
Gate 05's closing findings/resolutions are context. `FinDist.probTrue` and its reader moved
from `Extractors.lean` to upstream `FinDist.lean`; PAC does not gain a crypto-framework
import. Gate 05's checked [KV94]/[SSBD14] comparisons are context, not claims that those
PDFs are attached here. Public readers, the topic facade and root export are present.
Native source/object/prerequisite reconciliation covers all 467 union modules at the frozen
head; the root export was not elaborated. Common collection, seals, controls and axiom
reconciliation are complete with the retained failures detailed below. Further source repairs
require affected rechecks. #194's transfer is complete.

## Source bundle and context

Primary paths below use braces as set notation; each name has the `.lean` suffix:

- `TCSlib/Cryptography/Randomness.lean`.
- `TCSlib/Cryptography/Randomness/{Extraction,Learning,BPPBridge,Derandomization}.lean`.
- Already-gated context: `TCSlib/LearningTheory/PAC.lean`,
  `TCSlib/LearningTheory/PAC/{Defs,Prediction}.lean`, `TCSlib/InformationTheory/Samples.lean`.

The prepared source-only bundle contains these paths' complete final-head TCSlib import closure,
plus `TCSlib.lean` for root-export context, with raw-byte hashes and revision-qualified provenance.
Shared Games/Interaction/Machines/Collections/FinDist/complexity owners are context, not new
prerequisite audits. Include the common record/evidence set specified in `PLAN.md` and retain
source-version/access limits. Do not substitute historical prong or e9 dependency copies.

Gate 05 context records also include
`gates/05-pac/{findings/gate05-pac-r3-findings.md,resolutions-r3.md}` under the campaign.

## Brief for the auditor

You are auditing the **trusted surface**. Hunt for:
1. **Infidelity:** a definition or statement that differs from the source's other than by a
   declared deviation; check that each declared deviation is benign or that its cost is stated.
2. **Wrong semantics:** a definition that does not compute what its docstring says.
3. **Trivialization:** vacuous hypotheses; games won or lost for degenerate reasons (`n = 0`,
   empty domains, a budget of 0).
4. **Wrong strength:** a theorem weaker or stronger than its docstring claims.
5. **Attribution:** `policy.md` §2.

For **every definition**, restate it in your own words before reading its docstring. For
**every theorem**, say in 1–3 sentences whether the statement is what its docstring claims. Attempt
at least **three adversarial instantiations**. Do not give a blanket approval.

## Specific questions

1. **Thm 179.1.** Is `prfConcept` (the first output bit) the source's class? Is `learnerOf` a
   faithful non-adaptive learner? Does (c) follow from (b) with the stated confidence gap?
   When comparing with [KV94]'s notion, are amplification and the resulting learner/sample/
   runtime/edge changes accounted for rather than attributed to the original learner?
2. **Thm 180.1.** Does the S3c bridge (`verifier_toNUPPT`, `randProb_eq_uprob`) make `main`'s
   BPP and the NUPPT model meet without changing either? Is `subexpBound` the source's
   `2^{n^ε}`?
3. **Thm 183.6.** Are `samplerLaw` and `effSources` the source's "efficiently computable
   `(n − 2)`-sources"? Is `extBit` the right one-bit function of `Ext`?

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

## Round 1 source and delivery identities

| Attachment identity | Exact value |
|---|---|
| Source bundle exchange path | `outbox/gates/06D-r1-gate/gate06D-source-bundle.md` |
| Source bundle SHA-256 | `3a167712e1748f7a121aa01455e060977a225bb98f5ea144071c087c568a64cd` |
| Source sections | 185 raw files: the 184-module primary TCSlib closure plus root-export context |
| Source-only manifest in records | `briefs/pass-shelat-ch5-8/gates/06-ch5-8-statements/06D-source-manifest.json` |
| Manifest exchange filename | `gate06D-source-manifest.json` |
| Source-only manifest SHA-256 | `8947c1090298d80034c616b1492792707f91016528759d0b8047478a4ef97f90` |

The manifest contains raw source path/revision/byte/hash rows, primary modules/import closure,
source-bundle filename/hash and source/base pins only. It contains no records commit or self-hash.
`TCSlib.lean` is context, not a closure root or an elaborated export check. The exact source-only
bundle is prepared and verified; staging is an external action. A later records snapshot and its
records/common bundles are identified only by the exchange README and user dispatch prompt,
which also pin the common archive and final index. This avoids a records/hash self-reference.

Receiving auditor: verify access to the common provided exact tracked PS10 course PDF and the
required official Goldreich/PSV URLs/version notes in `source-manifest.md`; list exact unavailable
comparisons in the findings. Draft/publisher equivalence and deferred proof limits remain audit
subjects. Do not redistribute third-party PDFs, extracted full text or rendered pages.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide:
- **blocker:** a downstream phase would build on a wrong statement;
- **major:** a statement is fixable but materially misleading as it stands, or accumulated debt
  that the gate may not close over without explicit human acknowledgment;
- **minor:** an edge case, or a naming or attribution defect;
- **note:** an observation; no change required.

The gate closes at **0 blockers and 0 majors**.

**Not yet clear to merge — external statement audits and their resolutions remain.**
