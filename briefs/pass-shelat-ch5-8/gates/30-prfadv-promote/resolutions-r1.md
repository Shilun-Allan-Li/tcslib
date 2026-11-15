# Gate 30 · resolutions, round 1 · IN PROGRESS

Codex's verdict is **CLEAR**: 0 blockers, 0 majors, 1 minor, 0 notes.
- **Findings:** `findings/gate30-prfadv-promote-findings.md`.
- **Audited head:** `5757bc0604527602d790a1a57e9703374ce02c7b`.

Codex confirmed the following:
- the placement beside `prfAdv`;
- the import, which is acyclic and justified (closure 6 → 9 modules, 42 downstream modules gain it);
- the ETT API, which is unchanged;
- that no other unrecorded copy exists. The private `prfAdv_prfReduction` stays deferred.

| # | Severity | Disposition |
|---|---|---|
| G30-01 | minor | **Being fixed by LE-gate30, docstring only.** `ETTGame.prfAdv_eq_expect`'s docstring still says it is "re-derived here" and keeps the old sketch. Both will be replaced by a direct-specialization note. Rebuilt. |

**Follow-up from Codex.** DL-44 is not fully discharged until prf-mac re-points its `hadv`. The merged #313/#314 tree
needs an integration build before the second of the two merges.
