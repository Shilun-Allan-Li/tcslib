# The ND inventory API (branch `lean/nd-api`): notes

**Why.** C1's fill briefs come next on the NTIME-hierarchy chain (`audits/evidence/c1/C1-fill-plan.md`).
Under the user's "Everything" rule (2026-10-16, `policy.md` §1), every definition a brief's route reads
gets a published equation before the brief is dispatched. #118 did this for the deterministic model.
C1's routes read the nondeterministic model, and its counterparts were missing.

**The inventory** (`inventory/`): the seed-inclusive elaborator (`maintainer-tools/DefInventorySeeds`)
over 47 seeds: the five C1 host contracts, the three headline statements and the names their proof
sketches cite. It elaborates against `oleans-lbapi4` (the tip plus #118's round 3) with 0 errors and
prints 152 rows. Each flagged definition is judged:

| Judgement | Definitions |
|---|---|
| **Gap, fixed here** | `NDTM.stepWith` (no live case), `NDTM.fixChoice`, `NDTM.initCfg`, `NDTM.HaltsWithin`, `FinNDTM.AcceptsWithin`, `FinNDTM.DecidesInTime`, `NTIME`, `MultiTapeTM.toNDTM`, `FinTM.toFinNDTM`, `NDTM.relabelState`, `NDTM.replayTM`, `NDTM.withChoiceTape`, `CodeNDTM.toFinNDTM`, `guessRunCfg`, `streamStartCfg`, `clockCfg`, `Cfg.Stopped` |
| A machine read through its run lemmas | `expandTM`, `skipBackTM`, `NDTM.phaseHostND`, `guessRunTM` with `guessRunPhases`, `guessRunRed` and `GuessRunPhase.State` |
| A model primitive, read through its run algebra | `MultiTapeTM.runFrom`, `NDTM.runWith` |
| The worker's own file | `ndWriterTM` (the writer's brief) |
| Covered | `serializeK` (`serializeK_eq`), `tableBitsK`, `CodeNDTM.serialize` (`serialize_eq_tableBitsK`), `pairEncode`, `FinTM.bufferTape`, `ComputesInTime`, `ComputesFunInTime`, `counterOverhead`, `unaryFin`, `wordPatch`, `TimeConstructible`, the renamings |

Each brief's own inventory (its route's definitions crossed with their unfolding sites, as MIG-12's)
is still run when the brief is drafted.

**What.** One commit, `4abca360`, on #118's round-3 head `531b98a2`. It adds 41 equations, declarations
and `simps` attributes only (`isSimp := false`, no `@[simp]`):
- **7 hand-written:**
  - `NDTM.stepWith_of_some`, the live ND step, beside `stepWith_of_halt`; the counterpart of
    `MultiTapeTM.step_of_some`;
  - `NDTM.initCfg_eq`, the counterpart of `MultiTapeTM.initCfg_eq`;
  - `NDTM.haltsWithin_iff`, `FinNDTM.acceptsWithin_iff`, `FinNDTM.decidesInTime_iff`,
    `Complexity.mem_NTIME_iff`, `Cfg.stopped_iff`: the definitions unfolded, by `Iff.rfl`.
- **34 generated:** the fields of
  - `fixChoice`, `MultiTapeTM.toNDTM`, `relabelState` and `replayTM` (2 each);
  - `FinTM.toFinNDTM` and `CodeNDTM.toFinNDTM` (`k`, `State`, `tm`);
  - `withChoiceTape`, `guessRunCfg`, `streamStartCfg` and `clockCfg` (5 each).

  Each file's Main-results list names the additions.

**Checks** (maintainer, against `oleans-lbapi4`):
- **Elaboration:** the six files, each with a probe appended, give 0 errors. Their warnings equal the
  bases' run in `wt-bapi`: NTIME has 1 (a Mathlib deprecation), NDHost 1 (the writer's sorry), the
  others 0 (`logs/`).
- **New names:** the 41 resolve. Their statements are the docstrings' formulas. Their axioms are
  standard: 10 use none, and the other 31 use only `propext`, `Quot.sound` and `Classical.choice`
  (the 3 that use `Classical.choice` are the three `CodeNDTM.toFinNDTM` fields).
- **Freeze:** publics added only (`freeze/`). No statement or body changes, and no private changes.
- **Lint** (`lint/`): 0 FAIL in both subtrees. `TuringMachine/` goes from 67 to 64 WARN and
  `ClassNP/` from 16 to 15. Check 8 is now satisfied for the ten definitions it flagged in these files.
- **Copy-text screen** (11 files, `screen/`): 136 declarations and 22 pairs at the base, 140 and 27 at
  the head. The 5 new pairs are boilerplate among the four configuration-valued definitions: each now
  carries the same `attribute [simps … state inputPos workTapes workTapePos output]` line and tag
  phrase, which the screen attaches to the declaration above it. No proof text is copied.
- **Replay closure:** 102 modules (`replay-order.txt`, from `graph2.py`; the root is excluded). Two
  in-flight brief files are downstream, `SpaceComplexity/WindowClock` (F3) and
  `TuringMachine/UniversalK` (U2-S). The additions are declarations only, so those fills are unaffected
  whichever merges first.

**Status:** local only. Push, PR, replay and gate wait for the user.
