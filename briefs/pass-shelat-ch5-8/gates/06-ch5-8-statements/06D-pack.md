# Gate 06D (Pass–shelat ch. 8, randomness): external statement audit pack

**Status: unissued DRAFT (2026-11-07); not staged or dispatched.** Frozen integration source:
`3f6db40e1688c4a0bb922c9575dd3bd2157a650b`; checked comparison ancestor:
`eee107e92a7db11f1f8c98a5c2867304f57ddc54`; draft PR #232. This is not an issued audit pin.
The 467-module native union is source/object/prerequisite reconciled with zero stale records
after 180 + 2 affected checks; `TCSlib.lean` was not elaborated. The fresh collector is active;
fresh whole-file seals, controls and final axiom outcomes are not yet available. Historical
prong heads are provenance only. Auditor: Codex; findings Markdown in the audit chat; the user
dispatches the job. No readiness or final seal-pass attestation is made here.

**What is audited:** [PS10] ch. 8 as formalized in `TCSlib/Cryptography/Randomness/`, with the PAC layer of gate 05 as context: definitions, statements, docstrings and proof sketches, against the
sources. Proofs are out of scope, except the short ones that carry a definition's correctness
(`correct` fields, length lemmas). The deliverable is **`gate06D-findings.md`**.

**Sources required at issue (receiving-auditor access is not yet attested):** [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed.,
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
head; the root export was not elaborated. The fresh collector is active and fresh seal/control
outcomes remain pending. Further source repairs require affected rechecks. #194's transfer is complete.

## Source bundle and context (draft; not assembled)

Primary paths below use braces as set notation; each name has the `.lean` suffix:

- `TCSlib/Cryptography/Randomness.lean`.
- `TCSlib/Cryptography/Randomness/{Extraction,Learning,BPPBridge,Derandomization}.lean`.
- Already-gated context: `TCSlib/LearningTheory/PAC.lean`,
  `TCSlib/LearningTheory/PAC/{Defs,Prediction}.lean`, `TCSlib/InformationTheory/Samples.lean`.

The bundle must contain these paths' complete final-head TCSlib import closure, plus
`TCSlib.lean` for root-export context, with raw-byte hashes and revision-qualified provenance.
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

## Pending issue-time attestations

These are explicit issue-time fields, not completed attestations. Common evidence and the
current native/static/style limits are in `PLAN.md`.

- Issued source: `[ISSUE_SOURCE_COMMIT]` (must match the frozen head above, or receive a new
  source-matched verification); actual comparison/target disposition: `[ISSUE_BASE_DISPOSITION]`;
  records: `[ISSUE_RECORDS_COMMIT]`.
- Exact source bundle: `[ISSUE_06D_BUNDLE_PATH]`, `[ISSUE_06D_BUNDLE_SHA256]`;
  matching manifest: `[ISSUE_06D_MANIFEST_PATH]`, `[ISSUE_06D_MANIFEST_SHA256]`.
- Final source/native evidence: `[ISSUE_FINAL_EVIDENCE_INDEX_PATH]`,
  `[ISSUE_FINAL_EVIDENCE_INDEX_SHA256]`; retain the root-export non-elaboration limit and all
  affected/downstream rechecks required by any later repair.
- Fresh collector, actual axiom identities and dispositions: `[ISSUE_COLLECTOR_AXIOM_EVIDENCE]`,
  `[ISSUE_COLLECTOR_AXIOM_OUTCOMES]`. Current prepared scope is 54 mathematical modules and seven
  separately verified import/option-only facade/export files; derive scope from pinned metadata.
- Fresh full seals/controls: `[ISSUE_SEAL_CONTROL_EVIDENCE]`, `[ISSUE_SEAL_CONTROL_OUTCOMES]`.
  Cover stored types/values/private/generated declarations and anonymous commands through the
  full import-closure supplement, without name exclusions beyond approved notation. Classify
  every source failure against the actual base; inherited failures remain failed observations,
  not seal passes, exclusions or automatic waivers. Invalid harnesses remain separately labelled.
- Final explicit-unfold/source/API scans and precise existing style exceptions:
  `[ISSUE_SCAN_API_STYLE_EVIDENCE]`, `[ISSUE_SCAN_API_STYLE_DISPOSITIONS]`. Lexical census and
  parser rows do not replace elaborated axiom/declaration identities.
- Receiving auditor's source access and exact version/comparison limits:
  `[ISSUE_SOURCE_ACCESS_DISCLOSURE]`; preserve `source-manifest.md`'s linked-source arrangement.

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

**Not yet clear to merge — fresh verification outcomes, source-access disclosures, issue-time pins/bundles and user dispatch remain.**
