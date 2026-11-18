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
| #371 / 161 | **Gate 161 staged** (2026-11-18), draft, branch `ram/fills-0-1` at `24aa4050`, **stacked on #370**: tiers 0 (18, `Extended`) and 1 (3, `WordSize`) as delivered, plus a maintainer repair (`cfg_map_comp` → public `Cfg.mapState_mapState`). Replay 7/7 on `oleans-cl160-cc91f4`, seals 34, controls 43/86, 9 copy pairs dispositioned. RAM admissions 32 → 11. `ConfigCount` import: confirm with Seyoon. |
| `fill-ram-wordsize` | **Delivered** (2026-11-17, `d48bc959`); in #371. |
| `fill-ram-steps` | **Delivered** (2026-11-18, `cbc46b92`, after checkpoint 1); in #371. |
| #370 / 160 | **Round 1 HOLD** (2026-11-17; 0/1/1): G160-01 tier 3 brief missed the admitted `HaltsWithin` helpers (tier 0 added, briefs corrected), G160-02 three docstrings (repaired). Head now `25040f43`, which also adds four vendored readers to `Programs/WordRAM/Steps` (Seyoon). **Round 2 CLEAR** (2026-11-18; 0/0/0, 9 notes; `findings-r2.md`): clear to merge at `25040f43`. Round 2 was dispatched (Seyoon, 2026-11-17): replay 280/280 (42 inherited admissions: RAM 14, Extended 18, BooleanAnalysis 10), seals 12/12, controls 20/40, sweeps clean (`gates/160-ram-readers/pack-r2.md`). Round 1 was dispatched (Seyoon, 2026-11-17): bundle `db6e8ccd` (23 sections), exchange `48647728`, PR head `e75d2907` (draft, `ram/readers`): the eight tier 3 readers. Replay 265/265 on `oleans-cc91f4` (output `oleans-cl160-cc91f4`), seals 8/8, controls 20/40, sweeps clean. |
| `fill-ram-classes` | **Tier 3 brief ready** (corrected after G160-01); staged after #370 merges and tier 0 lands. |
