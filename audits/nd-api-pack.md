# External audit pack — the ND inventory API (PR #119)

Campaign: the Arora-Barak chapters 3-4 plan, C1 (the nondeterministic time hierarchy, [AB09, Theorem
3.2]). The user's "Everything" rule (2026-10-16, `policy.md` §1): every definition a brief's route
reads gets a published equation before the brief is dispatched.
- **Why now:** C1's fill briefs are next (`audits/evidence/c1/C1-fill-plan.md`; the user's rulings of
  2026-10-17: this PR with its own gate; wave 1 of five briefs; the normal form in its own module; C1-E's
  statement phase now). Their routes read the nondeterministic machine model. #118 (gate closed,
  `audits/brief-api-r3-findings.md`) published the deterministic counterparts.
- **The head:** `lean/nd-api` at `1e45f50a`, three commits on #118's round-3 head `531b98a2` (the
  tip's Lean since #118 merged): `4abca360` (the stubs' inventory), `85f2c916` and `1e45f50a`
  (wave 1's route inventory).

| File | Additions |
|---|---|
| `TuringMachine/Nondeterministic` | `NDTM.stepWith_of_some`, `NDTM.initCfg_eq`, `NDTM.haltsWithin_iff` (hand-written); the fields of `NDTM.fixChoice`, `MultiTapeTM.toNDTM`, `FinTM.toFinNDTM`, `NDTM.relabelState` (`simps`) |
| `ClassNP/NTIME` | `FinNDTM.acceptsWithin_iff`, `FinNDTM.decidesInTime_iff`, `Complexity.mem_NTIME_iff` (`Iff.rfl`) |
| `TuringMachine/ChoiceReplay` | the fields of `NDTM.replayTM` and `NDTM.withChoiceTape` (`simps`) |
| `TuringMachine/NDCodes` | `CodeNDTM.toFinNDTM`'s `k`, `State`, `tm` (`simps`) |
| `TuringMachine/Build/NDHost` | the fields of `guessRunCfg` and `streamStartCfg` (`simps`) |
| `TuringMachine/Build/StepClock` | the fields of `clockCfg` (`simps`); `Cfg.stopped_iff` (`Iff.rfl`) |
| `TuringMachine/Build/StepBlock` (second commit) | `tableTape_eq`, `summaryTape_eq`, `exit_true`, `exit_false`, `Rep_iff`, `outputSummary_nil`, `summaryCells_eq` |
| `TuringMachine/Build/Convention` (third commit) | `Cfg.ofWords_state`, `_inputPos`, `_workTapePos`, `_output` |
| `TuringMachine/Build/VirtualInput` (second commit) | `vhostCfg`'s five fields (`simps`); `vhostCap_eq`, `vhostSilentCfg_eq` |

In all: 59 names, 20 hand-written and 39 generated, every `simps` with `isSimp := false`, and no
`@[simp]`. Each file's Main-results list names its additions.

- **Evidence:** `audits/evidence/nd-api/`. It holds:
  - `NOTES.md`, with the inventory's judgement table;
  - the inventory probe and output (`inventory/`);
  - the per-file elaborations with probes appended, and their bases (`logs/`);
  - the freeze, the lint, the screen, the replay closure, the patch, and the edit scripts.
- **The bundle** also contains:
  - the eight touched files at the head;
  - the C1 consumers `Diagonalization/NTimeHierarchy`, `ClassNP/ExhaustiveReplay`,
    `TuringMachine/NDCodeSimulator`, `TuringMachine/Build/InputWindow`, and the hosted loop
    `TuringMachine/Build/StepBlockLoop` (the second commit's consumer);
  - the deterministic precedents `TuringMachine/Deterministic` (`step_of_some`, `initCfg_eq`) and
    `TuringMachine/Configuration` (`Cfg.init`'s fields);
  - the C1 design and the fill plan.

## Brief for the auditor

1. **Faithfulness.** Does each equation state exactly its definition's behaviour?
   - `stepWith_of_some` is the live case of `NDTM.stepWith`, beside the existing `stepWith_of_halt`.
   - The five iffs (`haltsWithin_iff`, `acceptsWithin_iff`, `decidesInTime_iff`, `mem_NTIME_iff`,
     `Cfg.stopped_iff`) are the definitions' bodies.
   - The generated field equations are the definitions' fields: check the probe outputs against the
     definitions.
2. **Completeness for C1's routes.** Is any definition left unpublished that a route reads?
   - The routes are wave 1's five briefs (W the writer, WC the window copy, E the exhaustive decider,
     R the interpreter core, UN with BF, H′ and S), RC the replay canonizer and NF the normal form; see
     the fill plan's table and each stub's proof sketch.
   - Challenge the judgement table in `NOTES.md`: machines read through their run lemmas, model
     primitives read through their run algebra, the writer's own file, and "covered".
   - Note the method's limit: the seeds are the stubs' statements and the names their sketches cite.
     Each brief's own route inventory, with its unfolding sites, still runs when it is drafted.
3. **No behaviour change.** The diff adds declarations, docstrings and `simps` attributes only; it
   deletes nothing. No existing statement or definition changes (the freeze).
4. **Duplication.**
   - The screen's 5 new pairs: is the boilerplate explanation right (the shared `simps` attribute line
     of the four configuration-valued definitions)?
   - Are the parallel deterministic and nondeterministic lemmas (`step_of_some` and
     `stepWith_of_some`, the two `initCfg_eq`) acceptable as the model's two layers, or should one
     derive from the other?
5. **Records.** Do `NOTES.md`, this pack and the PR body agree with the evidence?

## Repository-side attestations (verify or challenge)

- **Elaboration** of the nine files with probes appended, against `oleans-lbapi4` (the tip plus
  #118's round 3): 0 errors. The warnings equal the bases': NTIME has 1 (a Mathlib deprecation),
  NDHost 1 (the writer's `sorry`), the others 0.
- **New names:** the 59 resolve. 12 depend on no axioms; the rest use only `propext`, `Quot.sound` and
  `Classical.choice`.
- **Freeze:** publics added only.
- **Lint:** 0 FAIL. `TuringMachine/` goes from 67 to 63 WARN, and `ClassNP/` from 16 to 15.
- **Screen** (13 files, `screen2/`): 240 declarations and 33 pairs at the base, 244 and 38 at the
  head (5 new, boilerplate, all from the first commit).
- **Replay:** `replay-lndapi.sh`, the nine files' downstream closure (189 modules), from
  `oleans-lbapi4`. ⟨REPLAY RESULT⟩

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into `audits/nd-api-findings.md`. The
gate closes when it has zero blockers and zero majors.
