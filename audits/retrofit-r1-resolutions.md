# Retrofit epoch R1 — gate resolutions (CLOSED, round 8)

**Gate: CLOSED on round 8 (2026-10-10): PASS, 0 blockers, 0 majors, 1 minor.**
Findings verbatim in `audits/retrofit-r1-r8-findings.md`. **Epoch R1 is retired,
and the 12.2c refactor is armed.** RB4 is unaffected: its window had already
opened under the A-S1 fill gate, and its delivery is under review as PR #13.

## What the epoch delivered

Three retrofit batches over the chapter-1/2 machine files, all merged by the
user (PR #9: RB2 with the E1 commit; PR #10: RB1 and RB3):

- RB1: Loop, −198 lines.
- RB2: Primitives, −1,262 lines.
- RB3: Hardness, −179 lines.

Net: **−1,639 lines and −83 private declarations** (76 dead, 7 replaced). Public
surfaces stayed byte-identical apart from the one human-approved E1 rewrite.

## What the gate certified

The cumulative duplication ledger, `audits/duplication-ledger.md`. Its census
is now **generated** by `audits/evidence/retrofit/r1-public-proof-screen.py`
(pass 4). The round-8 auditor reproduced it independently: 537 like-kind member
pairs; Catalog 318/423, Primitives 173/272, Loop 117/212, Wrappers 19/29,
Composition 6/19, TimeConstructible 20/21. It found **no omission within the
stated rule and population, and no generator bug**. All of this is
acknowledged debt (D-R2, D-R3, RB4, CH7-D1, CH34-D2), with its cleanup
scheduled on the 12.2c tasklist (`AroraBarakChapters3-4Plan.md` §4d).

## Round history (why eight rounds)

| Round | Verdict | The finding that held the gate | Root cause |
|---|---|---|---|
| 1 | 0/2 | Sources unattached; no cumulative ledger existed | Evidence gap |
| 2 | 0/2 | Ledger arithmetic inconsistent; the relocation family misclassified as independent work; 13 H3 copies omitted | Hand-assembled ledger |
| 3 | 0/1 | The 20-declaration counter block and the Composition copies missed | Hand-assembled ledger |
| 4 | 0/1 | Two public proof correspondences missed | Hand-assembled ledger |
| 5 | 0/2 | The screen's description did not match the run; one adaptation missed | Method stated, not executed |
| 6 | 0/1 | Public-only residual scope missed a private source | Scope limit fixed one instance at a time |
| 7 | 0/1 | Source side taken from best matches only | Hand-transcribed source side |
| 8 | **PASS** 0/0/1 | — | — (the census is generated) |

Lessons recorded: generate the census rather than assembling it; when a finding
exposes a scope gap, close the whole class; state methods exactly as they were
executed, and publish the script. **Process amendment (user, 2026-10-10;
`audits/TEMPLATE.md` failure mode 5, merged to main as PR #12):** accounting
corrections inside an already-acknowledged debt family are minors.

## Disposition of round 8

| Finding | Disposition |
|---|---|
| R8-1 (minor: stale prose in three passages) | **Swept at close.** The pass-3 population now reads 553 declarations (542 extracted). Pass 3b reads 109 raw pairs, 107 like-kind over 62 targets, 12 at 90% or more, plus 2 restatements. The note that in-file near-matches add no member now names the independent cross-file path for `emLoopHost_init`/`_anchor_return`. The final near-duplicate note no longer lists the H3 `_init` pair as uncounted. |
| R8-2 — R8-6 (notes) | Carried. R7-1 and R7-2 are closed; pass 4 is retained as the census generator. |
