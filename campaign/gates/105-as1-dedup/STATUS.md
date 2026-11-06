# Gate 105 (#214, the dedup window's AS-1)

- 2026-11-06: the change `73629daf` (a sub-agent; the one member outside `CircuitComplexity`),
  #214 opened. `replay-las1` passed (7 modules, 0 failed, 0 `sorry`); freeze and lint in
  `evidence/`. Pack complete.
- 2026-11-06: staged (`outbox/gates/105-as1-dedup-gate/`, exchange commit `cb3039b2`): bundle
  `105-as1-dedup-bundle.md`, 17 sections, SHA-256
  `c80ff456bad64c7bd5776e930479a2e5c1b192d4d14bf205cd80267e144a456a`; Lean from `0bc71211`.
  Findings file `as1-dedup-findings.md`. **Ready to dispatch.**
- 2026-11-06: **dispatched** (the user).
- 2026-11-06: after dispatch, the user allowed colleague-owned edits; `1fd7d4ce` re-proves the five
  `BoolCircuit` members through the general equations (pushed to #214). Round 1 audits
  `0bc71211` as dispatched; the five go into round 2 with a new replay.
- 2026-11-06: round 2: #214 complete (`92e53e6e`); freeze, lint, replay-las2 (109/0); pack-r2 written; staged.
- 2026-11-06: round 2 **dispatched** by the user (140 sections, bundle `e935f140…`).
- 2026-11-06: round 2 findings: **HOLD 0/2/2** (implicit astep reductions; cross-file instruction-table reads). Awaiting the user's ruling.
