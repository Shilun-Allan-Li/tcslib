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

This PR covers the inventories of the next two briefs:
- **U2-S** (`exists_selfStartupTMK`) reads the serialization's shape, the two encodings, the
  initial configurations, the buffered composite's configurations and the silent transport's
  frame.
- **B6 F5** (the ruler device) reads the visited sets, the transports' scalar fields and the
  heads' readings at the input blanks.

## What

The patch is `core-api.patch`: three commits, seven files.
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

## Checks (maintainer; against `oleans-lf3p`)

- **Elaboration** (`logs/elab-*-{base,head}.out`): each changed file except StepBlock has 0 errors,
  with warning counts equal to the base (Configuration 3, Deterministic 0, Encoding 1,
  Simulation 1, Embed 2, CodeSimulator 3). StepBlock cites the moved lemmas and needs the new
  Deterministic olean, so the replay checks it.
- **Generated names** (`logs/generated-*.txt`): all resolve in-module, with their statements as
  Lean prints them.
- **Axioms** (`logs/axioms.log`): the hand-written lemmas are within
  `[propext, Classical.choice, Quot.sound]`.
- **Freeze** (`logs/freeze.log`): publics added only, apart from StepBlock's two moved lemmas.
  The `initCfg` flag is the tool's chunking heuristic (annotated in the log).
- **Lint** (`logs/lint-{base,head}.txt`): 0 FAIL, 23 WARN over 78 files, as at the base. No added
  line over 100 characters.
- **Screen** (`logs/screen-{base,head}.txt`, `logs/screen-delta.log`): 355 → 358 declarations,
  80 pairs before and after. The one changed pair is relocated by the move; no new copy.
- **Replay:** the closure of `Configuration` (about 320 modules) contains the files of #112, #114
  and #115. The branch is brought up to date after those merge, and the user runs the replay.
