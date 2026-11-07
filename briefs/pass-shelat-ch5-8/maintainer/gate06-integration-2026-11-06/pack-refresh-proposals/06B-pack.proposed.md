# Gate 06B (Pass–shelat §6.2, secure computation): external statement audit pack

**Status: unissued DRAFT (2026-11-07); not staged or dispatched.** Frozen integration source:
`3f6db40e1688c4a0bb922c9575dd3bd2157a650b`; checked comparison ancestor:
`eee107e92a7db11f1f8c98a5c2867304f57ddc54`; draft PR #232. This is not an issued audit pin.
The 467-module native union is source/object/prerequisite reconciled with zero stale records
after 180 + 2 affected checks; `TCSlib.lean` was not elaborated. The fresh collector is active;
fresh whole-file seals, controls and final axiom outcomes are not yet available. Historical
prong heads are provenance only. Auditor: Codex; findings Markdown in the audit chat; the user
dispatches the job. No readiness or final seal-pass attestation is made here.

**What is audited:** [PS10] §6.2 as formalized in `TCSlib/Cryptography/SecureComputation/`:
definitions, statements, docstrings and proof sketches, against the sources. Proofs are out of
scope, except the short ones that carry a definition's correctness (correctness of OT, of the
special encryption, of garbling and of Yao; the composition's phase lemmas). The deliverable is
**`gate06B-findings.md`**.

**Sources required at issue (receiving-auditor access is not yet attested):** [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed.,
January 2010 (book page = PDF page − 12), §6.2, book pp. 154–164. [Gol04] O. Goldreich,
*Foundations of Cryptography, Volume 2*, §7.3 (including Theorem 7.3.3) and Appendix C.1.
Official author drafts are located and locally verified in `source-manifest.md`. Supply
their official URLs/access notes, not redistributed Goldreich PDF copies or book excerpts.
The author versions and published-edition comparison limits must be disclosed.

## Scope

| Item | Where | State |
|---|---|---|
| Def 155.1 (honest-but-curious security; polynomial-time parties, ruled) | `SecureComputation/Defs.lean` | defined |
| Def 160.a, Prot 160.4, Prop 161.5 (OT) | `ObliviousTransfer.lean` | correctness proved; Prop 161.5 stated |
| Alg 157.2, Claim 157.a (special encryption) | `SpecialEncryption.lean`, `SpecialEncryptionSecurity.lean` | correctness proved; claim stated |
| Constr 158.a, Claim 159.a (garbling) | `Garbling.lean`, `GarblingSpecial.lean`, `GarblingSecurity.lean` | deterministic part proved; probabilistic part stated |
| The hybrid model and [Gol04, Thm 7.3.3] | `Hybrid.lean`, `Compose.lean`, `ComposePhases.lean`, `ComposeSecurity.lean` | phase lemmas proved; theorem stated |
| Prot 162.6, Thm 163.7 (Yao) | `Yao.lean` (OT-hybrid), `YaoReal.lean` (real protocol) | correctness proved; Thm 163.7 stated, the real form by composition |

## Prior findings (verify the repairs)

1. **OT has five messages:** D8 reads a party's output as its next-message function on its
   complete history.
2. **Prop 161.5 no longer assumes sampler canonicity.** `SamplerCanonical` is a theorem from
   `Collection.sample_eq_encD`. Canonical decoding derives the local decoder-wide `hspec`
   through `Collection.apply_of_decD` from the retained canonical-only equation
   `henc : ∀ i x, H (pairEncode i (T.encD i x)) = [h i x]`. The explicit polynomial-time
   evaluator hypothesis `hH : PolyTimeComputable H` and **`EnhancedHardCore` remain**.
   Bob's sampler coins remain visible in his view, so ordinary hard-core security does not
   replace the enhanced hypothesis. Real Yao retains these OT hypotheses.
3. **Garbling: `Good`** means correct opening under every assignment's keys.
4. **Efficiency is in Def 155.1** (ruled): `Efficient` strategies and bounded honest messages.
5. **Yao in the OT-hybrid model, then composition** (ruled, Q-5).

## Integrated API and construction context

All thirteen secure-computation modules and the topic facade are included. Public interfaces
cover real/ideal sampler equations, predicate characterizations, functionality/strategy/protocol
fields, and simulator run/coin contracts. Composition and Yao read the shared interaction
layer through public lemmas. Correctness/phase lemmas remain distinct from admitted security
and efficiency statements. Native source/object/prerequisite reconciliation is complete at
the frozen head, with the root export not elaborated; the fresh collector is active and fresh
seal/control outcomes remain pending. Any source repair requires affected rechecks.

## Source bundle and context (draft; not assembled)

Primary paths below use braces as set notation; each name has the `.lean` suffix:

- `TCSlib/Cryptography/SecureComputation.lean`.
- `TCSlib/Cryptography/SecureComputation/{Defs,ObliviousTransfer,SpecialEncryption,SpecialEncryptionSecurity,Garbling,GarblingSpecial,GarblingSecurity,Hybrid,Compose,ComposePhases,ComposeSecurity,Yao,YaoReal}.lean`.

The bundle must contain these paths' complete final-head TCSlib import closure, plus
`TCSlib.lean` for root-export context, with raw-byte hashes and revision-qualified provenance.
Shared Games/Interaction/Machines/Collections/FinDist/complexity owners are context, not new
prerequisite audits. Include the common record/evidence set specified in `PLAN.md` and retain
source-version/access limits. Do not substitute historical prong or e9 dependency copies.

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

1. **Def 155.1** (`HBCSecure`, `Functionality.PolyTime`). Is the reading (private outputs,
   polynomial lengths, one negligible bound for all inputs of a length) faithful? Is the
   efficiency requirement (`Efficient` strategies and polynomially bounded honest messages; ruled)
   the source's p.p.t. protocol in this model? Does the output clause still force correctness?
2. **OT (Prot 160.4, Prop 161.5).** Are the five messages (D8's output convention) harmless? Are
   collection-derived canonicity and the canonical-only `henc` interface correct? Does
   `Collection.apply_of_decD` supply the specification correctness uses? Are the retained
   `hH` and **enhanced** hard-core hypothesis (`EnhancedHardCore`, with sampler coins visible)
   correctly propagated to `yaoProtocol_hbcSecure`? Appendix C.1.1 defines enhanced inversion;
   compare the predicate motivation with §7.3.2's OT argument (draft pp. 639–641), rather than
   treating the formal Boolean predicate as a literal definition from Appendix C.1.
3. **Garbling (Alg 157.2, Constr 158.a, Claims 157.a, 159.a).** Is `nestedSpecial` Alg 157.2
   applied in layers? Is `Good` the right notion? Is the bound of `garbling_good_whp` stated over
   the right distribution?
4. **The hybrid model and composition** (`Hybrid.lean`, `Compose*.lean`). Is "ideal calls first"
   a faithful special case of [Gol04, §7.3.1]'s oracle-aided protocols for Yao? Is the composed
   protocol's layout (pairs with fillers, a lead filler, no trailing filler) the sequential
   composition? Check the phase lemmas' statements. Is `hbcSecure_compose`'s added hypothesis
   (`main` has at least one move) necessary (the worker's counterexample) and sufficient?
5. **Yao (Prot 162.6, Thm 163.7).** Compare `yaoHybrid` with the source's protocol. Check each
   declared deviation: the XOR-shift row order, the output decoding pairs, sink output vertices
   (`outs_sink`: without it the decoding pairs leak), `n` bit OTs per input wire, the joint PRF
   hypothesis `hG₁₂`, the uniform circuit family. Is `yaoProtocol_hbcSecure` (real protocol, by
   composition) the source's Thm 163.7?

## Pending issue-time attestations

These are explicit issue-time fields, not completed attestations. Common evidence and the
current native/static/style limits are in `PLAN.md`.

- Issued source: `[ISSUE_SOURCE_COMMIT]` (must match the frozen head above, or receive a new
  source-matched verification); actual comparison/target disposition: `[ISSUE_BASE_DISPOSITION]`;
  records: `[ISSUE_RECORDS_COMMIT]`.
- Exact source bundle: `[ISSUE_06B_BUNDLE_PATH]`, `[ISSUE_06B_BUNDLE_SHA256]`;
  matching manifest: `[ISSUE_06B_MANIFEST_PATH]`, `[ISSUE_06B_MANIFEST_SHA256]`.
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
