# The core specification API (PR #116): notes

## Why

The user ruled on 2026-10-16, in two steps:
1. **An API PR first**, not unfolding (G4's and B6 F3's escalations E1). That is PR #112, for the
   machine library's contracts and layouts.
2. **The rule covers everything.** Every definition a brief's route reads, wherever it lives,
   gets a published equation lemma before dispatch, found by a pre-ship inventory per brief.

**The primitives boundary (user, 2026-10-16).** Workers read the machine model's primitives
(`MultiTapeTM.step`, `runFrom`, `Action.apply`, `Cfg.mapState`) through the existing lemmas, and
unfold `step` and `Action.apply` only for a leaf defined in their own file.

This PR covers the inventories of the next two briefs, and the zone layer (below):
- **U2-S** (`exists_selfStartupTMK`) reads the serialization's shape, the two encodings, the
  initial configurations, the buffered composite's configurations and the silent transport's
  frame.
- **B6 F5** (the ruler device) reads the visited sets, the transports' scalar fields and the
  heads' readings at the input blanks.
- **The zone layer** (user ruling, 2026-10-16, option (a): "add a zone API to #116 before its
  gate"). G4's continuation reads `Build/Zone` and `Build/ZoneTape`, whose pure definitions G4's
  original brief let it unfold. The maintainer's inventory of the two files' 35 definitions:
  - **already covered** by published lemmas that determine the value on every input:
    `zoneCapacity` (`zoneCapacity_eq`, in this PR), `zoneStart` (`zoneStart_eq`, the closed
    form), `zoneOwner` (`zoneOwner_of_mem`/`_of_not_mem`; an equation is added anyway),
    `zoneIndex` (`zoneIndex_eq_iff`; likewise), `zoneShiftIndex` (`zoneShiftIndex_eq`,
    `_eq_length_iff`; likewise);
  - **lacking an equation for some input before this PR**: the other 27 (`zonedTape` and
    `zoneRebalance` had case lemmas for part of their inputs). Each now has equations covering
    every input ("What", below).
  - `ZoneCell`, `ZoneSym` are `abbrev`s of `Fin k → Option (Option Bool)` and `Bool ⊕ ZoneCell k`,
    and `ZoneContents` is a structure read through its projections; none needs a lemma.

## What

The patch is `core-api.patch`: five commits, ten files.
- **Configuration:**
  - `Cfg.init`'s five fields (`simps`, `isSimp := false`);
  - `Cfg.inputSymbol_of_zero`, `Cfg.inputSymbol_of_end` (with the existing `inputSymbolInner`,
    every input reading);
  - `Cfg.workTapeSymbols_eq`.
- **Deterministic:**
  - `initCfg_eq`, `mem_visitedByTapeHead_iff`;
  - `visitedByTapeHead_add_subset` and `visitedByTapeHead_step_subset`, **moved from
    `Build/StepBlock`** with identical statements and proofs. Their docstring there named this
    file as their eventual home (design note O9). Their full names are unchanged, so every citation
    (StepBlock's own, H2-F's) resolves.
- **Encoding:** `pairEncode_eq`, `unaryFin_eq`.
- **Simulation:** `FinTM.bufferedFirstCfg`'s and `bufferedSecondCfg`'s five fields (`simps`,
  `isSimp := false`).
- **Build/Embed:** `embedSilentCfg_unselected`, the frame companion of `embedSilentCfg_cap`; the
  state, input position and output of both transports (`simps`, `isSimp := false`).
- **CodeSimulator:** `serializeK_eq`. Its hunk (line ~102) is apart from #113's, so the two merge
  cleanly.
- **Build/StepClock:** `wordPatch_of_mem`, `wordPatch_of_not_mem`. F3's continuation reads F2's
  runner endpoint, whose clock tape is a `wordPatch`, to clear the clock.
- **Build/Zone:** `zoneCapacity_eq` (G4's partial unfolded `zoneCapacity`); and the zone layer
  (fifth commit, `scripts/mkzone.py`; two further asserted edits rewrapped long lines and wrote
  the headers, so the patch is authoritative):
  - equations: `zoneBase_eq`, `zoneIndex_eq`, `zoneSlot_of_lt`/`_of_le`, `zoneSide_eq`,
    `zoneShiftInW_eq`, `zoneShiftOutW_eq`, `zoneMove_true`/`_false`, `zoneStepPair_eq`,
    `zoneCascadeRight_eq`, `zoneCascadeLeft_eq`, `zoneCascade_true`/`_false`,
    `ZoneContents.words_true`/`_false`, `zoneShiftIndex_eq_findIdx`, `zoneRebalance_of_lt` (the
    cascade case, beside the existing identity case `zoneRebalance_of_le`),
    `zoneTrackTape_zero`/`_of_pos`/`_of_neg`;
  - field equations `_home`, `_left`, `_right` (`simps`, `isSimp := false`; 24 names) of
    `ZoneContents.empty`, `zoneShiftIn`, `zoneShiftOut`, `zoneHomeWrite`, `zoneMoveRight`,
    `zoneMoveLeft`, `ZoneContents.swap`, `ZoneContents.extend`.
- **Build/ZoneTape:** `zoneSlotOf_inl`/`_inr`, `zoneCellOfCell_inr`/`_inl`/`_none`,
  `zoneSlotSet_eq`, `zoneOwner_eq`, `zoneCells_eq`, `zoneCellAt_eq`, `zonedTape_of_pos`/`_of_neg`
  (with the existing `zonedTape_zero`, every cell).
- **Docstrings that state their formulas** (policy.md §2; the #112 gate's finding 4 flagged the
  same bare-label style there): `zoneCapacity_eq`, `wordPatch_of_mem`/`_of_not_mem`,
  `Cfg.inputSymbol_of_zero`/`_of_end`, `Cfg.workTapeSymbols_eq`, `initCfg_eq`. Text only.

## Checks (maintainer; against `oleans-lf3p`; head `d5255232`)

- **Elaboration** (`logs/elab-*-{base,head}.out`): each changed file except StepBlock has 0 errors,
  with warning counts equal to the base (Configuration 3, Deterministic 0, Encoding 1,
  Simulation 1, Embed 2, CodeSimulator 3, StepClock 0, Zone 0, ZoneTape 0). StepBlock cites the
  moved lemmas and needs the new Deterministic olean, so the replay checks it. ZoneTape's new
  lemmas cite no new Zone lemma, so it elaborates against the base Zone olean.
- **Generated names** (`logs/generated-*.txt`, Zone's 24 in `generated-Zone.txt`): all resolve
  in-module, with their statements as Lean prints them. `simps` states function-valued fields
  applied (`(zoneShiftIn side i z).left a = (if side = true then … else …) a`).
- **Axioms** (`logs/axioms.log`): the hand-written lemmas are within
  `[propext, Classical.choice, Quot.sound]`.
- **Freeze** (`logs/freeze.log`): publics added only, apart from StepBlock's two moved lemmas.
  The `initCfg` flag is the tool's chunking heuristic (annotated in the log). The zone round's
  BODY CHANGE flags are the docstring rewrites (annotated: no statement or proof line changed).
- **Lint** (`logs/lint-{base,head}.txt`): 0 FAIL, 23 WARN over 78 files, the same warning set
  as at the base. No added line over 100 characters.
- **Screen** (`logs/screen-{base,head}.txt`, `logs/screen-delta.log`; ten files, ZoneTape
  added): 462 → 468 declarations, 103 pairs before and after, 21,874 → 22,142 reproduced
  characters. No new copy:
  - the one renamed pair is relocated by the move;
  - four pre-existing Zone pairs (the mirrored `zoneShiftIn`/`zoneShiftOut` and
    `zoneMoveRight`/`zoneMoveLeft` definitions) grow by the shared `attribute [simps …]` line,
    which the screen attaches to each definition.
- **Replay:** the closure of `Configuration` (about 320 modules) contains the files of #112, #114
  and #115. The branch is brought up to date after those merge, and the user runs the replay.
  #112's gate returned FAIL (2 majors, in #112's own files); its round 2 is separate from this PR.
