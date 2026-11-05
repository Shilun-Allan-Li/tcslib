# Gate 96 (the deepening API, #196): resolutions

**Staged (2026-11-05)** on the exchange at `arora-barak-ch3-4/outbox/gates/96-deepen-api-gate/`
(exchange commit `f755a879`): bundle `96-deepen-api-bundle.md`, 209 sections, SHA-256
`1954b449d5347f77c72e6f294b608876d53145ff52a28f035e5d279c26e5c797`. Lean files from the PR head
`89f4ebbc6b0d007c981f907e3353d72fa84fa787`, everything else from the records commit
`683e2adf571e8b6a5c62280d4a3739ec89687546`. Findings file `deepen-api-findings.md`.

**Replay (2026-11-05): `replay-ldwa` passed**, 73 modules, 0 failed; the static check 0
mismatches, the campaign's existing 30 `sorry`s (`evidence/merged-tree/`).

#196 is clear to merge once gate 96 closes with zero blockers and zero majors.

**Dispatched (2026-11-05, the user).**

**Maintainer's supplementary check (after staging):** the pack cites four files outside the
18-file screen population (`Simulation`, `ARMLoops`, `ARMProof`, `Codec/Langs`). A screen widened
to 29 files and restricted to pairs touching the PR's files finds no pair beyond the pack's
`NoEdge`/`Rel` idiom (`evidence/screen/supplementary-29files/`).

## Round 1 findings (received 2026-11-05)

`findings.md`, verbatim from the exchange inbox (`arora-barak-ch3-4/inbox/deepen-api-findings.md`,
exchange commit `ad00d747c47c5cdbe3c1453fc49e07e553d084e2`), SHA-256
`5654d6d08d041ef16ada0c76b5360dd64bf7349d39a371debed8754c1e5da982`.

**Verdict: does not close.** 0 blockers, 2 majors (F1, `NoEdge` without its `_iff`; F2,
`Cfg.InWindow.apply_of_lt` re-derives `CfgRecord`'s private `recordStep_window`), 4 minors
(F3–F6), 6 notes (F7–F12). Dispositions follow below as the repairs land.

**Not yet clear to merge: #196** (gate 96 has two majors open).
