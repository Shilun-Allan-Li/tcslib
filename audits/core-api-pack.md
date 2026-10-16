# External audit pack — the core specification API (PR #116)

Campaign: the Arora-Barak chapters 3-4 plan; the machine library (`machine-library-design.md`
§12–§16).
- **User (2026-10-16):** every definition a brief's route reads gets a published equation lemma
  before dispatch ("Everything").
- The machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`, `Cfg.mapState`)
  are read through existing lemmas. A worker unfolds `step` and `Action.apply` only for its own
  leaf.
- PR #112 (gated separately, `audits/spec-api-pack.md`) publishes the machine library's contract
  and layout facts.
- **This PR publishes the core definitions** that the U2-S startup and the B6 F5 ruler device read,
  the gap the F3 continuation inventory found beyond #112 (`wordPatch`'s cells), and **the zone
  layer** (`Build/Zone`, `Build/ZoneTape`) that G4's continuation reads. The user ruled the zone
  layer into this PR on 2026-10-16 ("add a zone API to #116 before its gate"). It gets its own
  gate before it merges.
- #112's gate (round 1) returned FAIL with two majors in #112's own files (the release adapters'
  and `Contract.ofSegment`'s fields; `sweepMapWrite`). Those are repaired in #112's round 2, not
  here.

| File | Additions |
|---|---|
| `Configuration.lean` | `Cfg.init_{state,inputPos,workTapes,workTapePos,output}`; `Cfg.inputSymbol_of_zero`, `Cfg.inputSymbol_of_end`; `Cfg.workTapeSymbols_eq` |
| `Deterministic.lean` | `MultiTapeTM.initCfg_eq`, `mem_visitedByTapeHead_iff`; `visitedByTapeHead_add_subset`, `visitedByTapeHead_step_subset` (moved from `Build/StepBlock`) |
| `Encoding.lean` | `pairEncode_eq`, `unaryFin_eq` |
| `Simulation.lean` | `FinTM.bufferedFirstCfg_*`, `FinTM.bufferedSecondCfg_*` |
| `Build/Embed.lean` | `embedSilentCfg_unselected`; `embedSilentCfg_{state,inputPos,output}`, `embedEmitCfg_{state,inputPos,output}` |
| `Build/StepBlock.lean` | the two moved lemmas removed; docstrings updated |
| `Build/StepClock.lean` | `wordPatch_of_mem`, `wordPatch_of_not_mem` (F3's continuation reads F2's endpoint through `wordPatch`) |
| `Build/Zone.lean` | `zoneCapacity_eq`, `zoneBase_eq`, `zoneIndex_eq`, `zoneSlot_of_lt`/`_of_le`, `zoneSide_eq`, `zoneShiftInW_eq`, `zoneShiftOutW_eq`, `zoneMove_true`/`_false`, `zoneStepPair_eq`, `zoneCascadeRight_eq`, `zoneCascadeLeft_eq`, `zoneCascade_true`/`_false`, `ZoneContents.words_true`/`_false`, `zoneShiftIndex_eq_findIdx`, `zoneRebalance_of_lt`, `zoneTrackTape_zero`/`_of_pos`/`_of_neg`; the `_home`/`_left`/`_right` field equations (`simps`) of `ZoneContents.empty`, `zoneShiftIn`, `zoneShiftOut`, `zoneHomeWrite`, `zoneMoveRight`, `zoneMoveLeft`, `ZoneContents.swap`, `ZoneContents.extend` |
| `Build/ZoneTape.lean` | `zoneSlotOf_inl`/`_inr`, `zoneCellOfCell_inr`/`_inl`/`_none`, `zoneSlotSet_eq`, `zoneOwner_eq`, `zoneCells_eq`, `zoneCellAt_eq`, `zonedTape_of_pos`/`_of_neg` |
| `CodeSimulator.lean` | `serializeK_eq` |

The docstrings of `zoneCapacity_eq`, `wordPatch_of_mem`/`_of_not_mem`, `Cfg.inputSymbol_of_zero`/
`_of_end`, `Cfg.workTapeSymbols_eq` and `initCfg_eq` now state their formulas (policy.md §2).

- **Evidence:** `audits/evidence/core-api/`, with the patch, the logs and `NOTES.md`.
- **The bundle** contains the nine files at the PR head, the two drafted briefs
  (`audits/evidence/core-api/drafts/`, not dispatched; placeholders unfilled), and the drafted
  inventories' consumers:
  `UniversalK.lean` (U2-S's target), `Build/InputDevice.lean` (F5's targets),
  `UniversalStartup.lean` (the prefix canonizer U2-S runs), and `Build/StepBlockForward.lean` (a
  citer of the moved lemmas).
- For the zone layer: G4's brief `briefs/s13d-fill-g4.md` (its route), its delivery review
  `audits/evidence/s13d-g4-fill/delivery-review.md` (escalation E1 and the API it asked for),
  and `Build/ZoneRebalance.lean` (the two rows and the landed partial's helpers).

## Brief for the auditor

1. **Faithfulness.** Each lemma states exactly its definition, with no strengthening and no lost
   case.
   - For the generated field equations (`logs/generated-*.txt`), check the right sides against the
     definitions.
   - For `Cfg.inputSymbol_of_zero`/`_of_end`, check that together with `inputSymbolInner` they
     cover every input position.
   - **The zone layer.** The case lemmas must cover every input together:
     - `zoneSlot_of_lt`/`_of_le`;
     - `zoneMove_true`/`_false`;
     - `zoneRebalance_of_lt` with the existing `zoneRebalance_of_le`;
     - `zoneTrackTape_zero`/`_of_pos`/`_of_neg`;
     - `zoneSlotOf_inl`/`_inr`;
     - `zoneCellOfCell_inr`/`_inl`/`_none`;
     - `zonedTape_of_pos`/`_of_neg` with the existing `zonedTape_zero`.

     The `rfl` equations restate each body exactly (`zoneShiftInW_eq`, `zoneShiftOutW_eq`,
     `zoneCascadeRight_eq`, …). Zone's 24 generated field equations are in
     `logs/generated-Zone.txt`.
2. **The move.** `visitedByTapeHead_add_subset` and `visitedByTapeHead_step_subset` move from
   `Build/StepBlock` to `Deterministic`. Confirm that:
   - statements and proofs are identical (compare the patch);
   - the full names are unchanged;
   - nothing else in StepBlock changed apart from the two docstring sentences;
   - every citer resolves: StepBlock itself, and `Build/StepBlockForward` in #114.
3. **No behaviour change.** No `@[simp]` is added (`isSimp := false`; the hand-written lemmas carry
   no attribute), and no existing statement or definition changed.
4. **Coverage.** This is the main question: is anything still missing for the two briefs' routes?
   - **U2-S's route:**
     - the prefix canonizer (`prefixCanonTM`, landed in #110), around Hydroxyi's cleaned machine
       `Complexity.LogProg.cleanTM` (cited as is);
     - capture and placement by `embedSilentRetTM`;
     - redistribution of the captured `serializeK` by catalog rows;
     - an input rewind by `FinTM.timed_rewind`.
   - **F5's route:**
     - a lockstep boundary-test leaf, the call rows by seams, and the ruler host as a
       `Turing.Lockstep`;
     - visited sets in Z1's style.
   - **G4's continuation** (the route in `briefs/s13d-fill-g4.md`; continuation brief not yet
     drafted):
     - the extension row's endpoint `zonedTape_extend`;
     - the scan of the feeding side for `zoneShiftIndex`;
     - the cascade by `zoneStepPair` stages and the guarded `zoneMove`;
     - per-track column moves by the mapped sweeps, with `extract := zoneSlotOf t` and
       `merge := zoneSlotSet t`;
     - the rows' specifications through `zoneRebalance` and `ZoneContents.extend`.

     The mapped sweeps' own endpoint helper `sweepMapWrite` is #112's finding 2, repaired there.

   Name any definition outside the worker's file that these routes would still have to unfold
   (other than the primitives above), and say where its lemma belongs.
5. **Placement.** Each lemma should sit beside its definition, which is why the replay is the
   closure of `Configuration`. Should any move (for example, the generic visited-set lemmas
   generalized beyond `Bool`)? A note is enough; the generalization is not in scope.
6. **Duplication** (failure mode 5): the screen of the nine files, before and after
   (`logs/screen-*.txt`).
7. **Records.** Check `NOTES.md` and this pack against the evidence.

## Repository-side attestations (verify or challenge)

- Built on the tip `62fa2330` (Lean content `c2897d7f`), against `oleans-lf3p`. Head `d5255232`
  (five commits; the fifth is the zone layer and the docstring rewrites).
- **Elaboration:** each changed file except StepBlock has 0 errors, with warning counts equal to
  the base. StepBlock is checked by the replay.
- **Generated names:** all resolve in-module.
- **Axioms:** the hand-written lemmas use standard axioms only.
- **Freeze:** publics added only, apart from the move. The `initCfg` flag is a chunking artifact.
- **Lint:** unchanged.
- **Screen:** the ten files (ZoneTape added), before and after: 462 → 468 declarations,
  103 → 103 pairs, 21,874 → 22,142 characters (`logs/screen-delta.log`, head against base).
  - The one renamed pair is pre-existing and relocated by the move: `roundTM_iterate` reproduces
    `visitedByTapeHead_step_subset` at 76% in the base and at 71% from its new home (the text
    lacks the `_root_` prefix). The gate may comment on the now cross-file pair.
  - Four pre-existing Zone pairs (the mirrored `zoneShiftIn`/`zoneShiftOut` and
    `zoneMoveRight`/`zoneMoveLeft`) grow by the shared `attribute [simps …]` line that the screen
    attaches to each definition.
  - **No new copy.**
- **Replay:** about 320 modules, after #112, #114 and #115 merge (run by the user).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into `audits/core-api-findings.md`.
The gate closes when it has zero blockers and zero majors.
