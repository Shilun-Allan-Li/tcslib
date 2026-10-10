# §12.6 framed catalog contracts — statement-gate resolutions (CLOSED, round 1)

**Gate: CLOSED on round 1 (2026-10-10): PASS, 0 blockers, 0 majors, 0 minors;
eight notes.** Findings verbatim in `audits/s12-framed-findings.md`. The five
statements in `Build/Catalog.lean` (`transferTM_run_ofCfg`, `copyTM_run_ofCfg`,
`clearTM_run_ofCfg`, `incrementTM_run_succ_ofCfg`,
`incrementTM_run_overflow_ofCfg`) are audited true as stated and sufficient for
the zone consumer. This commissions the fill batch (`briefs/s12-framed-fill.md`).

## The auditor's evidence

- Blind restatements of all five.
- Trace inductions on the transition tables, with an every-time trajectory
  table.
- 15 adversarial instantiations plus 1,524 configurations in an independent
  semantic model; all 63 of the maintainer's fixtures were reproduced.
- Mutation tests showing each delimiter premise is needed where it is claimed.
- The canonical-specialization table.
- A consumer-fitness analysis, including the counter's geometric cost:
  `Σ_{r=1}^{2^i}(2v₂(r)+2) = 2^{i+2} − 2`.

## Notes carried into the fill brief (binding guidance)

| Note | Carried as |
|---|---|
| F1–F5: no findings; prove the generalized trace once, in Catalog | The fill's central rule: one generalized trace per routine family; no parallel private traces |
| F6: hypotheses are sufficient, not minimal (the right delimiter is unread on success; clear tests only nonblankness) | Statements frozen as audited; no strengthening edits |
| F7: consumer obligations (uniform control, window location, boundary save/restore, left-side orientation, identity branch, unary-scratch restoration, first-return transport, explicit halt) | Carried to the ZF-A3 brief, not this fill |
| Canonical specialization holds for all five; "the proof dependency order may need rearrangement because the framed rows currently appear later in the file" | The fill **re-derives each canonical row from its framed form**. Moving the framed section above the canonical rows is sanctioned, statements unchanged and the move flagged |
| F8: compilation and history attestations were not replayed by the auditor | Retained as maintainer evidence: Catalog elaborates with exactly the five sorries, and the downstream replay is clean |
| Suggested kernel sanity checks (the 15 concrete cases, width preservation, the `incFixed` characterizations) | Optional permanent regressions in the fill brief |
