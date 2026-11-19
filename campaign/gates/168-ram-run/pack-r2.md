# Gate 168, round 2 · RAM simulation, tier 2 job E: the two stage-2 targets proved (PR #383)

**Round 2 of the Codex audit.** Round 1 (`findings.md`) was **HOLD**: 0 blockers, 1 major,
2 minors. It found the simulation argument sound (G168-04) and the evidence consistent (G168-05).
This round answers the three findings. PR #383 is a draft into `complexity/ram-simulation`.
Seyoon dispatches and merges.

- **Lean head:** `230c39f53b31396fc8392132033839b6f64075fc` (branch `ram/fill-run`). Since round
  1's head `a6199066`:
  1. `f399426a`, the maintainer's repair of G168-01 in `Sim/RunStep.lean`: `host_local` and
     `words_headD`;
  2. `80cc59a6`, a merge of the RAM branch: #385 (`WordArith`), #382 (`exists_tmProc`), #388
     (`InputBit`, `Startup`) and #389 (`KeyTable`). It merges cleanly and changes none of this
     PR's 22 files;
  3. `230c39f5`, the rest of G168-01: `host_envelope`. `Sim/RunStep.lean` goes from 398 to 430
     lines.
- **#391 merged after this run** (`b9b521fd`). It changes only `Build/Convention`,
  `StateRenaming` and `CodeSimulator`, none of which this PR touches, and the PR still merges
  cleanly. The replay below is of the PR merged into the branch before #391; the next snapshot
  replay of the merged branch covers both.
- **Rulings that bind:** as in round 1 (tier 2 design D1 and D3, the approved edit of
  `Simulation.lean`'s imports, the reader rule).

## Resolutions

| # | Severity | Resolution |
|---|---|---|
| G168-01 | major | **Factored.** Three helpers in `Sim/RunStep.lean` now carry the shared work. `RunSetup.host_local` builds the local entry configuration, transports the encoding, and gives the reconstruction and head equations. `RunSetup.words_headD` is the word/head obligation. `RunSetup.host_envelope` is the selected/frame split that bounds every prefix head. `host_ordinary` and `host_verdict` each open with one `obtain … := A.host_local …`, cite `words_headD` and `host_envelope`, and then diverge into dispatch and halt. The screen still pairs them (72% in round 1, 63% now): what remains shared is their local `let` bindings and one-line citations of these helpers and of `phase_correct` (class `citation-shape`). All three helpers are public in `WordRAM.Sim.RunSetup` under D1. |
| G168-02 | minor | **Described and checked.** The metadata check is an **axiom allowance**: a nonempty `inherited_admissions` admits `sorryAx`, without naming sites. The check of named dependencies is a new kit step, the **admission walk** (`checks/admission-walk.py`), run on the final replay's snapshot. For each root it walks every constant reachable through types and values, theorem proofs included. It lists the constants whose own type or value uses `sorryAx`, and fails unless every root's sites lie in the allowlist. Result (`ADMISSION-WALK.json`): all 13 roots reach **exactly** `WordRAM.Sim.exists_phase` and `WordRAM.Sim.exists_verdictPhase`. The roots are the two targets and the eleven `Classes` corollaries, including #379's two `PolyTimeComputable` results. `exists_startup` is no longer reached because #388 proved it; the allowlist still names it, a superset only. |
| G168-03 | minor | **Homes bundled, screen extended.** All 19 citation homes of `CITATION-HOMES.json` are now in the bundle, including the 14 that round 1 lacked. They also join the copy screen's population through the new `population_extra` key. With them the population is 22 owners plus 19 homes. The screen finds 24 new pairs and 0 gone (253 → 277), all classified in `PAIR-DISPOSITIONS.json`. The new pairs with the cited homes are field-by-field `Cfg` equalities through the `Cfg.mapState_*` readers. Three of them restate the mapped-initial-configuration equation: `host_initCfg`, and `NDHost`'s two inline `hinit`. The other is the re-tag-and-restore identity, `startupErase_attach` against `runEntry_reconstruct`. PR #391 publishes `Cfg.mapState_init`, and its approved follow-up retires `host_initCfg` (with C's private copies) to citations after #391 and this PR merge. It also lists `NDHost`'s two copies and `startupErase_attach` as further candidates. |
| G168-04, -05 | note | No change needed. |

## Brief for the auditor

1. **G168-01:** `host_local`, `words_headD` and `host_envelope` state the shared work
   faithfully, and `host_ordinary` and `host_verdict` no longer repeat it.
2. **G168-02:** the walk does what it says (`kit/checks/admission-walk.py`, in the data carrier),
   and `ADMISSION-WALK.json` matches its log.
3. **G168-03:** the 19 homes are present at the audited head; the 24 new pairs' dispositions
   hold.
4. **The merge** of the RAM branch changes no file of this PR and no frozen statement
   (`SOURCE.json`).

## Evidence (`evidence/`)

- **`REPLAY.json`:** the merged-tree replay on `oleans-cl175-cl169`, the RAM branch's build after
  #382, #388 and #389. 286 modules: 286 passed, 0 failed. The replayed sources contain 16
  admissions: the two targets' remaining interfaces and tier 2's open statements, none in this
  PR's files.
- **Seals:** 111 proofs and 76 heads, all passing (108 in round 1, plus the three helpers).
- **Controls:** 79 definitions and 158 identities in two parts, native-PASS and sealed-FAIL.
- **Sweeps:** the proof-syntax sweep finds 0 read candidates in 111 roots. Citation homes are in
  `CITATION-HOMES.json`.
- **Admission walk:** `ADMISSION-WALK.json` (13 roots), with its Lean file and log in the data
  carrier.
- **Copy screen:** 253 → 277 pairs, 24 new and 0 gone, all classified (`PAIR-DISPOSITIONS.json`,
  `pair-notes.json`).
- **The fill's report** (`REPORT-run.md`), as in round 1. Round 1's pack is `pack.md`.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate168-ram-run-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
