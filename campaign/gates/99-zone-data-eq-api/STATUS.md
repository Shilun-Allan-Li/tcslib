# Gate 99 (#207, the zone data maps as whole values)

- 2026-11-06: G5's brief review found the blocker B1 (the pointwise data-map fields cannot be
  used under the seal). The user ruled: publish by a new API PR. Branch `lean/zone-data-eq`:
  `zoneRebalanceData_eq`, `zoneExtendData_eq`. #207 opened; `replay-lzde` passed (5 modules,
  0 failed); the consumer probe, controls, axioms, freeze, names, screen (by construction) and lint
  in `evidence/`. The pack is complete.
- 2026-11-06: staged on the exchange (`outbox/gates/99-zone-data-eq-api-gate/`, exchange commit
  `e62c2e5a`): bundle `99-zone-data-eq-api-bundle.md`, 36 sections, SHA-256
  `44c0b904bfec182e69c504f5a4ba5e3ecf75a63182e4c12c41e8064a189aa2a2`; Lean from `f866f314`, records
  from `66f40de528bc43fbd92cefad2042459293cd8520`. The auditor pushes
  `zone-data-eq-api-findings.md` to the exchange inbox (the new protocol).
- 2026-11-06: **dispatched** (the user).
- 2026-11-06: #202 merged; the campaign merged into the branch (`d01332e4a924576bb4ec405b44822c954b233294`, no change to
  the PR's file). `replay-lzde2` passed (5 modules, 0 failed; `TwoTapes`' one `sorry`), chained from
  `oleans-lsi2` (`evidence/merged-tree-after-202/`): the replay of record for the merge.
