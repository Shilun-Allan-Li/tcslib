# Gate 06D (Pass–shelat ch. 8, randomness): external statement audit pack

**Status: internal reconciliation draft (2026-11-07); not issued or staged.** Reviewed source
reference: `e9d64158461bfe24ddc88ab885bc4017899b4c16` on the pushed integration branch. This is
not an issued audit pin: Rule-10 seals remain pending. The current 467-module source/object
manifest has zero stale records; any subsequent source repair requires an affected replay.
Historical prong heads are provenance only. The recorded auditor choice is Codex (findings
Markdown in chat); the user dispatches the job. No readiness attestation is made here.

**What is audited:** [PS10] ch. 8 as formalized in `TCSlib/Cryptography/Randomness/`, with the PAC layer of gate 05 as context: definitions, statements, docstrings and proof sketches, against the
sources. Proofs are out of scope, except the short ones that carry a definition's correctness
(`correct` fields, length lemmas). The deliverable is **`gate06D-findings.md`**.

**Sources required at issue (availability is not yet attested):** [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed.,
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
Rule-10 closure remains pending; the current native manifest reconciles all 467 source/object
records. Further source repairs require affected rechecks. #194's transfer is complete.

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

- Exact final source/records commits and matching source bundle/manifest, after the common
  preparation in `PLAN.md`; the internal source reference above is not an issued pin.
- Final source-matched affected replay/downstream checks, `sorry` census and axiom records.
- Rule-10 elaborated-term/anonymous-command coverage, installed seals, sensitivity controls and
  explicit-unfold scan; inherited failures classified against the actual PR base.
- Style/API lint comparison and precise existing exceptions; source attachments with hashes.
  Earlier union/API replay summaries concern staged sources. The later
  `evidence-run/seal-ready-pinned.json` reconciles all 467 current source/object/prerequisite
  records; seal-driven repairs must be checked again in their affected closure.


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

**Not yet clear to merge — common verification, source attachments and user dispatch remain.**
