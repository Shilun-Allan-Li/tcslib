# Gate 06B (Pass–shelat §6.2, secure computation): external statement audit pack

**Round 1: common preparation complete; ready for staging (2026-11-07).**
Audit source: `3f6db40e1688c4a0bb922c9575dd3bd2157a650b`; checked comparison ancestor:
`eee107e92a7db11f1f8c98a5c2867304f57ddc54`; draft PR #232. Historical prong heads are provenance only.
This document records neither staging/user dispatch nor external gate closure. Auditor: **Codex**;
return findings Markdown in the audit chat, with no commit or push requested. The user dispatches
all four audits after reviewed bundles and external pins are staged.

**What is audited:** [PS10] §6.2 as formalized in `TCSlib/Cryptography/SecureComputation/`:
definitions, statements, docstrings and proof sketches, against the sources. Proofs are out of
scope, except the short ones that carry a definition's correctness (correctness of OT, of the
special encryption, of garbling and of Yao; the composition's phase lemmas). The deliverable is
**`gate06B-findings.md`**.

**Sources for round 1 (receiving-auditor access must be verified):** [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed.,
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
the frozen head, with the root export not elaborated. Common collection, seals, controls and
axiom reconciliation are complete with the retained failures detailed below. Any source repair requires affected rechecks.

## Source bundle and context

Primary paths below use braces as set notation; each name has the `.lean` suffix:

- `TCSlib/Cryptography/SecureComputation.lean`.
- `TCSlib/Cryptography/SecureComputation/{Defs,ObliviousTransfer,SpecialEncryption,SpecialEncryptionSecurity,Garbling,GarblingSpecial,GarblingSecurity,Hybrid,Compose,ComposePhases,ComposeSecurity,Yao,YaoReal}.lean`.

The prepared source-only bundle contains these paths' complete final-head TCSlib import closure,
plus `TCSlib.lean` for root-export context, with raw-byte hashes and revision-qualified provenance.
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
| Source bundle exchange path | `outbox/gates/06B-r1-gate/gate06B-source-bundle.md` |
| Source bundle SHA-256 | `66f3ac9e11a1100a276f3336f54ee4a6f5b3a109e5c647523575b95e828ef9ff` |
| Source sections | 129 raw files: the 128-module primary TCSlib closure plus root-export context |
| Source-only manifest in records | `briefs/pass-shelat-ch5-8/gates/06-ch5-8-statements/06B-source-manifest.json` |
| Manifest exchange filename | `gate06B-source-manifest.json` |
| Source-only manifest SHA-256 | `e33f8aa437668a506a31a5f7c1c2e3d2632ff999023be5d2847e324cbcd83990` |

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
