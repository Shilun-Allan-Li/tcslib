# Gate 40 · round 2 · CLEAR → CLOSED

Codex's round-2 verdict is **CLEAR**: 0 blockers, 0 majors, 0 minors, 0 notes.
- **Findings:** `findings/gate40-pairings-statements-r2-findings.md`, SHA-256
  `e008f3a4494e5d563802b35b9f8aa5bab91401151813577287c6810e6a78f341`.
- **Audited:** #331 at `9e7a96481785d6cac4dea3b2e990c49ac278b060`, records `b356e50b`, exchange `56eff06a`, supplement
  `98a06806`, PR base `673a2715`.

All six round-1 findings are closed:
- **G40-01:** closed under the ruling. The three injectivity fields rule out the round-1 countermodel, and the BB1
  proofs are sound with standard axioms only.
- **G40-02:** closed. Both LE-gate40 and the merged-tree supplement give 40/40 seals, ALL_OK controls and 0 foreign
  unfolds; the supplement answers the merged-tree question, and no seal rerun is outstanding.
- **G40-03 to G40-06:** closed.

Codex also confirmed:
- the merge `39d42e23` (single-sided changes from their owners, the facade union, exactly #331's 13 files against the
  tip);
- LE-doc-abs against the DW-7 BB04 transcription;
- the round-1 confirmations, with T1–T4 and `bb1_sidSecure` unchanged;
- the build, admissions (237 → 241), axioms and lint evidence.

Nothing new is undisclosed, and nothing needs fixing. **Gate 40 is closed.**

## Remaining merge condition (maintainer)
- An integration build of #331 on the current tip, which now has #327 and #324 (`201bf57a`). It is queued for the
  next free olean tree, combined with Gate 43's #339 × #338 build. Once it passes, #331 is marked ready.
- After #331 merges, #340 (T1) and the T4 PR are retargeted to `cryptography/pass-shelat-ch2-4`.
