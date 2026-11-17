# RAM work: handoff

## 0. Current state (2026-11-17)

- **Branch** `complexity/ram-simulation`, cut from `main` `5cb25d52` with `seyoon-devtools`
  (`189af085`) merged in.
- **Snapshot:** `oleans-cc91f4` (898 objects) is `main`'s build at `5cb25d52`. The chapters 3–4
  campaign adopted it after #363. #364 changed only Ladner's header comment, whose object is
  byte-identical.
- **Plan:** `items/ram-tm/PLAN.md` §0. The 14 admissions come in three tiers: WordSize 3,
  Simulation 2, Classes 9.
- **Recheck done** (`items/ram-tm/recheck/README.md`): no statement change is needed; tier 3
  needed eight readers (PR #370).
- **Fills route through the exchange** (`exchange/pass-shelat-ch5-8`, `arora-barak-ch3-4/`;
  Seyoon, 2026-11-17).

| PR / gate | State |
|---|---|
| `fill-ram-wordsize` | **Tier 1 staged** (2026-11-17), base `81557aad`, bundle `d41aa4c2` (17 sections), exchange `9a1e74a2`; dispatch pending. |
| #370 / 160 | **Gate 160 staged** (2026-11-17), not yet dispatched: bundle `db6e8ccd` (23 sections), exchange `48647728`, PR head `e75d2907` (draft, `ram/readers`): the eight tier 3 readers. Replay 265/265 on `oleans-cc91f4` (output `oleans-cl160-cc91f4`), seals 8/8, controls 20/40, sweeps clean. |
| `fill-ram-classes` | **Tier 3 brief ready** (`items/ram-tm/briefs/fill-ram-classes.md`); staged after #370 merges. |
