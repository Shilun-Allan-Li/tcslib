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

**Status:** pushed as PR #119 (user, 2026-10-17: its own PR and gate).

## The second commit (`85f2c916`): C1 wave 1's route inventory

The first inventory's seeds were the stubs' statements and the names their sketches cite. Wave 1's
route inventory (`inventory/C1Wave1Inv.*`) seeds what the routes of WC, E, R and UN read: the
counter loop, the embeddings, the replay lemma, the step clock, the catalog's rows, the phase host
and seams, H2's hosted loop, Z1, the input call and the guess-run lemmas. It runs against
`oleans-lbapi4`, which predates #119, so the first commit's fixes are discounted by hand.

| Judgement | Definitions |
|---|---|
| **Gap, fixed in the second commit** | `StepBlock.Rep`, `exit`, `summaryTape`, `tableTape`, `outputSummary` (no empty case), `summaryCells` (the definitions `hostedLoopTM_run` and `hostedLoop_read` read); `vhostCfg`, `vhostSilentCfg`, `vhostCap` |
| Covered | `counterLoopCfg` at Bool (`counter_cfg_eq`), `counterLoopOrbit` (an `abbrev`, with #118's N3 pitfall), `embedEmitCfg` and `embedSilentCfg` (their selected and unselected lemmas), `MultiTapeTM.initCfg` (`initCfg_eq` and `Cfg.init`'s fields), `vhostBank` (`vhostBank_eq`) |
| Machines read through their run lemmas | `counterLoopTM`, `StepBlock.loopTM`, `hostedLoopTM`, `embedEmitTM`, `embedSilentTM`, `clearTM`, `incrementTM`, `skipTM`, `skipBackTM`, `expandTM`, `phaseHostTM`, `seamCompTM`, `vhostEmitTM`, `vhostSilentTM`, `guessRunTM`, `phaseHostND` |
| **Deferred, then fixed in the third commit** | `Cfg.ofWords`: four of its five fields had no equation. The second commit's note took it for the diagonalizer fill's route only, and for a `Simulation` definition. It is in `Build/Convention`, and R's startup reads it through `exists_installCallTM` (below). |

**The commit:** 14 equations in two files, `StepBlock` (7 hand-written) and `VirtualInput`
(`vhostCfg`'s five fields by `simps`, and 2 hand-written).

**Checks**, against `oleans-lbapi4`:
- **Elaboration** with probes appended: 0 errors and 0 warnings, as at the base (`logs/`).
- **New names:** the 14 resolve with their formulas. Over all 55 names the axioms are standard: 12
  use none; the rest use only `propext`, `Quot.sound` and `Classical.choice`.
- **Freeze:** publics added only.
- **Lint:** `TuringMachine/` goes from 64 to 63 WARN. `VirtualInput`'s warning goes, and
  `StepBlock`'s list shrinks from 12 to 8; those 8 are the step block's internals, read through its
  run lemmas.
- **Screen** over 13 files (`screen2/`, the first population plus `StepBlock` and `VirtualInput`):
  240 declarations and 33 pairs at the base, 244 and 38 at the head. The new pairs are the first
  commit's 5 boilerplate pairs; the second commit adds none.
- **Replay closure:** 111 modules (`replay-order.txt`), from 102.

The stacked #120 and #121 merged the new head (`e18a7bfa`, `250dad4e`). Their Lean diffs from their
bases are unchanged, and their replay scripts chain from 111.

## The third commit (`1e45f50a`): the seam configuration's fields

Wave 1's route inventory, round 3 (`inventory/C1Wave1Inv2.*`), seeds the header-parsing and
installation pieces of R's and UN's routes: the prefix parser and canonizer (`UniversalStartup`),
the buffered composition, `FinTM.exists_installCallTM`, `pairExtractTM`, `counterValue_bits` and the
hosted loop.
- **Covered:**
  - `prefixCanonTM` through `prefixCanonTM_eq` and `bufferedCompTM`'s fields (#118);
  - `universalPrefixTM`, read through `prefixCanon_start`, `_run` and `_complete`;
  - `pairExtractTM`, through `pairExtractTM_computes`, `_fst` and `_snd`.
- **The gap:** `Cfg.ofWords`. `exists_installCallTM`'s contract is stated through `Cfg.ofWords`
  seams, so R's startup reads them, and only `Cfg.ofWords_workTapes` was published. It lives in
  `Build/Convention`, not in `Simulation` as the second commit's note assumed, and it is on wave
  1's route, not only E-D's.

**The commit:** `Cfg.ofWords_state`, `_inputPos`, `_workTapePos`, `_output` (`rfl`), beside
`Cfg.ofWords_workTapes`.

**Checks:**
- **Elaboration** with a probe appended: 0 errors and 0 warnings, as at the base.
- **New names:** the 4 use `[propext]` only.
- **Freeze:** publics added only.
- **Lint:** 63 WARN, unchanged.
- **Replay closure:** 189 modules, from 111; `Convention` is upstream of the seams.

**In all:** 59 equations (20 hand-written, 39 generated) in nine files. #120 and #121 merged the
new head (`6d18902f`, `13f52659`), and their replay scripts chain from 189.
