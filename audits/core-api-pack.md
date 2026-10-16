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
- **This PR publishes the core definitions** that the U2-S startup and the B6 F5 ruler device read.
  It gets its own gate before it merges.

| File | Additions |
|---|---|
| `Configuration.lean` | `Cfg.init_{state,inputPos,workTapes,workTapePos,output}`; `Cfg.inputSymbol_of_zero`, `Cfg.inputSymbol_of_end`; `Cfg.workTapeSymbols_eq` |
| `Deterministic.lean` | `MultiTapeTM.initCfg_eq`, `mem_visitedByTapeHead_iff`; `visitedByTapeHead_add_subset`, `visitedByTapeHead_step_subset` (moved from `Build/StepBlock`) |
| `Encoding.lean` | `pairEncode_eq`, `unaryFin_eq` |
| `Simulation.lean` | `FinTM.bufferedFirstCfg_*`, `FinTM.bufferedSecondCfg_*` |
| `Build/Embed.lean` | `embedSilentCfg_unselected`; `embedSilentCfg_{state,inputPos,output}`, `embedEmitCfg_{state,inputPos,output}` |
| `Build/StepBlock.lean` | the two moved lemmas removed; docstrings updated |
| `CodeSimulator.lean` | `serializeK_eq` |

- **Evidence:** `audits/evidence/core-api/`, with the patch, the logs and `NOTES.md`.
- **The bundle** contains the seven files at the PR head, the two drafted briefs
  (`audits/evidence/core-api/drafts/`, not dispatched; placeholders unfilled), and the drafted
  inventories' consumers:
  `UniversalK.lean` (U2-S's target), `Build/InputDevice.lean` (F5's targets),
  `UniversalStartup.lean` (the prefix canonizer U2-S runs), and `Build/StepBlockForward.lean` (a
  citer of the moved lemmas).

## Brief for the auditor

1. **Faithfulness.** Each lemma states exactly its definition, with no strengthening and no lost
   case.
   - For the generated field equations (`logs/generated-*.txt`), check the right sides against the
     definitions.
   - For `Cfg.inputSymbol_of_zero`/`_of_end`, check that together with `inputSymbolInner` they
     cover every input position.
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

   Name any definition outside the worker's file that these routes would still have to unfold
   (other than the primitives above), and say where its lemma belongs.
5. **Placement.** Each lemma should sit beside its definition, which is why the replay is the
   closure of `Configuration`. Should any move (for example, the generic visited-set lemmas
   generalized beyond `Bool`)? A note is enough; the generalization is not in scope.
6. **Duplication** (failure mode 5): the screen of the seven files, before and after
   (`logs/screen-*.txt`).
7. **Records.** Check `NOTES.md` and this pack against the evidence.

## Repository-side attestations (verify or challenge)

- Built on the tip `62fa2330` (Lean content `c2897d7f`), against `oleans-lf3p`.
- **Elaboration:** each changed file except StepBlock has 0 errors, with warning counts equal to
  the base. StepBlock is checked by the replay.
- **Generated names:** all resolve in-module.
- **Axioms:** the hand-written lemmas use standard axioms only.
- **Freeze:** publics added only, apart from the move. The `initCfg` flag is a chunking artifact.
- **Lint:** unchanged.
- **Screen:** the seven files, before and after: 355 → 358 declarations, 80 → 80 pairs, 17,590 characters (`logs/screen-delta.log`, head against base). The one changed pair is pre-existing and relocated by the move: `roundTM_iterate` reproduces `visitedByTapeHead_step_subset` at 76% in the base and at 71% from its new home (the text lacks the `_root_` prefix). **No new copy**; the gate may comment on the now cross-file pair.
- **Replay:** about 320 modules, after #112, #114 and #115 merge (run by the user).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into `audits/core-api-findings.md`.
The gate closes when it has zero blockers and zero majors.
