# RAM work: handoff

## 0. Current state (2026-11-18)

- **Branch** `complexity/ram-simulation`, cut from `main` `5cb25d52` with `seyoon-devtools`
  (`189af085`) merged in.
- **Snapshot:** `oleans-cl161-cl160` (898 objects), the build of the branch after #371 (2026-11-18; gate 161's replay output, manifest `manifests/oleans-cl161-cl160.output.json` verified against all 898 objects). Before it, `oleans-cl160-cc91f4`, the build after #370; and before that, `oleans-cc91f4`, `main`'s build at `5cb25d52`. The chapters 3–4
  campaign adopted it after #363. #364 changed only Ladner's header comment, whose object is
  byte-identical.
- **Plan:** `items/ram-tm/PLAN.md` §0. The 32 admissions come in four tiers: Extended 18,
  WordSize 3, Simulation 2, Classes 9. After #371, 11 remain (Simulation 2, Classes 9).
- **Recheck done** (`items/ram-tm/recheck/README.md`): no statement change is needed; tier 3
  needed eight readers (PR #370).
- **Fills route through the exchange** (`exchange/pass-shelat-ch5-8`, `arora-barak-ch3-4/`;
  Seyoon, 2026-11-17).

| PR / gate | State |
|---|---|
| #371 / 161 | **Merged** (`adb694d2`, 2026-11-18); the merge's Lean equals the audited head `24aa4050`, so `oleans-cl161-cl160` is the branch's build. RAM admissions: 11 (Simulation 2, Classes 9). Earlier: **Gate 161 CLEAR** (2026-11-18; 0/0/3, 4 notes; `findings.md`, `resolutions.md`): **clear to merge at `24aa4050`**. The three minors are records-only: the bundle's citation homes, five more copy-screen pairs (dispositioned) and the sweep wording; two kit follow-ups. After the merge, adopt `oleans-cl161-cl160`. Earlier: gate 161 dispatched (Seyoon, 2026-11-18), draft, branch `ram/fills-0-1` at `24aa4050`, **stacked on #370**: tiers 0 (18, `Extended`) and 1 (3, `WordSize`) as delivered, plus a maintainer repair (`cfg_map_comp` → public `Cfg.mapState_mapState`). Replay 7/7 on `oleans-cl160-cc91f4`, seals 34, controls 43/86, 9 copy pairs dispositioned. RAM admissions 32 → 11. `ConfigCount` import confirmed (Seyoon, 2026-11-18). |
| `fill-ram-wordsize` | **Delivered** (2026-11-17, `d48bc959`); in #371. |
| `fill-ram-steps` | **Delivered** (2026-11-18, `cbc46b92`, after checkpoint 1); in #371. |
| #370 / 160 | **Merged** (`ccbf930c`, 2026-11-18). Snapshot `oleans-cl160-cc91f4` (gate 160's replay output, 898 objects) is the branch's build: the merge's Lean equals the replayed head `25040f43`. Earlier:  **Round 1 HOLD** (2026-11-17; 0/1/1): G160-01 tier 3 brief missed the admitted `HaltsWithin` helpers (tier 0 added, briefs corrected), G160-02 three docstrings (repaired). Head now `25040f43`, which also adds four vendored readers to `Programs/WordRAM/Steps` (Seyoon). **Round 2 CLEAR** (2026-11-18; 0/0/0, 9 notes; `findings-r2.md`): clear to merge at `25040f43`. Round 2 was dispatched (Seyoon, 2026-11-17): replay 280/280 (42 inherited admissions: RAM 14, Extended 18, BooleanAnalysis 10), seals 12/12, controls 20/40, sweeps clean (`gates/160-ram-readers/pack-r2.md`). Round 1 was dispatched (Seyoon, 2026-11-17): bundle `db6e8ccd` (23 sections), exchange `48647728`, PR head `e75d2907` (draft, `ram/readers`): the eight tier 3 readers. Replay 265/265 on `oleans-cc91f4` (output `oleans-cl160-cc91f4`), seals 8/8, controls 20/40, sweeps clean. |
| #373 / 163 | **Gate 163 staged** (2026-11-18), draft, branch `ram/fill-classes` at `1ababb82`: tier 3 as delivered (`fill-ram-classes.zip` `8f7d8c12…`). Replay 2/2 on `oleans-cl161-cl160`, seals 13 proofs, controls 37/74, 0 read candidates, 3 copy pairs dispositioned. The maintainer's dependency walk: each target reaches only `exists_simulation` or `exists_ndSimulation`. After the merge the RAM work's admissions are the two tier 2 targets only. |
| `fill-ram-classes` | **Delivered** (2026-11-18, `8f7d8c12`); in #373. |
| #372 / 162 | **Tier 2 statements PR** (draft, `ram/tier2-statements` at `e1325c96`): the public statements of the word rows, the keyed table, the input bit, and the simulation's interfaces (`Sim/Encoding`, `Sim/Startup`, `Sim/Phases`); readers in `Extended`. Gate 162 (a Codex statement audit, D5) in preparation. |
| Tier 2 | **Design note drafted** (2026-11-18; `items/ram-tm/TIER2-DESIGN.md`): four new library pieces (lockstep arithmetic row, multiplication, keyed table host, input contracts), simulation split into `RAMSimulation/Sim/`, one induction for both forms, about 6.2k–11.1k lines in about ten fills after a statements PR. **D1–D5 ruled** (Seyoon, 2026-11-18): new public homes, reuse `RecordTable`'s layout, one induction, five larger Codex jobs A–E in parallel, and a Codex statement audit. Next: the maintainer's statements PR. |
