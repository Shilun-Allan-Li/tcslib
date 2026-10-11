# R8.0b fill gate (§12.8 stream D): resolutions, round 1

Round 1 (`audits/s12-8-fill-D-findings.md`, verbatim) returned **FAIL: 0 blockers, 1 major,
2 minors, 11 notes**. The auditor independently confirmed the fill:
- the freeze replays exactly (F4);
- the meanings and `Bool` instances are preserved (F5);
- there is one host induction, with the `Bool` contracts derived through Z5 (F6);
- the decrement route (F7) and the public-surface agreement (F8) are as bound;
- guards, anchor priority and the cost range hold (F9);
- R8.6 follows its route, with the degenerate cases (F10);
- the screen delta (F11), the axiom boundary (F12) and the logs (F13) agree;
- the docstrings and the size exception hold (F14).

The repairs are on the PR #38 branch at `d2c9e16c` and after. The round-2 pack is
`audits/s12-8-fill-D-r2-pack.md`.

| # | Disposition |
|---|---|
| **F1** (major) | **Accepted by the user (2026-10-11): a one-off exception for exactly this definition pair**, `counterLoopTMVia`/`counterLoopTM` at 91%/84%. The brief mandated both texts, and there is no duplicated proof. It is recorded in `audits/duplication-ledger.md` (acknowledgment table) and in `backlog.md` §1, **R80B-E1**. That 12.2c follow-up redefines `counterLoopTM` as the identity-embedding instance of `counterLoopTMVia`, with the generic host first and consumers re-checked, under its own gate. The fill's freeze is untouched. |
| **F2** (minor) | **Accepted.** The round-2 bundle attaches what round 1 lacked: <ul><li>`Build/Catalog.lean` and `Build/Seam.lean`, so the six-file screen can be re-run;</li><li>the delivery's `SHA256SUMS` (`r80b-fill/delivery-SHA256SUMS.txt`);</li><li>the agent's full 74-module sweep (`r80b-fill/agent-final-sweep.log`);</li><li>the axiom and admission-walk probe sources (`S128FillDAxioms`, `S128FillDAdmissionWalk`, and round 2's `S128FillDR2Axioms`);</li><li>the false-control output (`audits/logs/s12-8-fill-D-r2-instances.log`).</li></ul> Archive integrity, the C shim's non-execution and the Python helpers' non-execution are maintainer attestations, and are stated as such. |
| **F3** (minor) | **Accepted; erratum.** The round-1 pack's and the integration record's "nine rewritten over a generic alphabet" should read: **eight alphabet generalizations** (`counterSpan`, `counter_span_append`, `counterPatch`, `counter_patch_twice`, `counter_patch_frame`, `counter_debit`, `counter_body`, `counter_rounds`), **plus the authorized `counter_buffer_complement` proof replacement**. The shipped round-1 pack and record are kept unchanged, under the archival rule. |
| F12 | The agent's and the maintainer's axiom logs agree entry by entry. They are not identical files: the agent prints the derived `instDecidableEqCounterLoopState` as well. |
| F14 | **Done.** The combined tree was checked first. The branch merged the campaign tip `fc999a8b`, where streams A–C have landed, and the user's replay of `CounterLoop`'s downstream closure (8 modules) gave 0 errors, with **`CounterLoop` at 0 sorry warnings**. All 31 `CounterLoop` publics, `expandTM_run_ofCfg` included, print only the standard triple, and the admission walk is empty (`audits/logs/s12-8-fill-D-r2-{replay,axioms}.log`). Then came the doc-only status refresh (`d2c9e16c`): the status line no longer calls `writeAdvTM_run_ofCfg` sorried. Comment-stripped code is identical. |

The other notes record verified properties and need no action.
