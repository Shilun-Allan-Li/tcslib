**The input rewind as a machine** (`Build/InputRewind`, new): the API that UN continuation 1's
landing needs, by the user's ruling (2026-10-22, "New small module"). It provides:

- `Turing.InputRewindPhase` and `Turing.inputRewindTM k`: one step left, the scan left over the
  input, one step right at the left blank into a stationary park;
- `Turing.inputRewindTM_run`: from a configuration in `start` with the input head at `p ≥ 1`, the
  machine is in `done` at exactly time `p + 1` and not earlier, with the head at `1` and everything
  else as it was; at every time up to then its work tapes, work heads and output are the start's;
- `Turing.inputRewindTM_step_done`: the park stays put;
- `Turing.Cfg.mapState_mapState`: relabeling twice is relabeling by the composite.

**`Build/NDHost`:** its private `guessRun_mapState_mapState` had exactly the new lemma's statement
(at `Type`, over `Bool`), and its proof unfolded `Cfg.mapState`, which is `StateRenaming`'s
definition. **The user ruled (2026-10-22): re-point it in this PR.** The private is removed, and
its three uses (in `guessRunTM_runWith_handoff`) rewrite with `Cfg.mapState_mapState`. NDHost
imports the new module.

**Commit:** `ac5ce7bc`, on the campaign branch at `86523ba5`.

| Check | Result |
|---|---|
| Elaboration (against `oleans-lu2sc1`) | `Build/InputRewind`: no output. NDHost has no olean for the new import in any snapshot, so it was checked as one file holding the new module's text and then NDHost's, with their imports merged: no output |
| Axioms | the three theorems on `[propext, Quot.sound]` |
| Rule 10 | a seal (`MultiTapeTM.step`, `MultiTapeTM.runFrom`, `FinTM.controlAction`, `moveInputPos`, `Cfg.inputSymbol`, `Cfg.mapState`, `Action.apply` irreducible) over primed copies of the module's text: the proofs elaborate; 7 controls fail sealed and close unsealed |
| Freeze | NDHost 25 → 25 public, 8 → 7 private (`guessRun_mapState_mapState` removed); one body changed, `guessRunTM_runWith_handoff` (the three `rw` sites); the facade's only change is the new import and its `## Contents` entry |
| v3 screen | the two modules, the files they cite (`Configuration`, `Deterministic`, `StateRenaming`, `Simulation`), and `Build/Rewind`, `ClassNP/ExhaustiveReplay`, `Diagonalization/NTimeHierarchy`: 253 → 257 declarations, 164 → 167 pairs; no pair gone; 3 new, all with `ExhaustiveReplay`'s members of the input-rewind family IR-1 (`xr_inRewindTM` 82% / 73%, `xr_E_initCfg` 54%), which the duplication ledger already assigns to the user's dedup window |
| Lint | `TuringMachine/Build` 0 FAIL, 33 WARN over 40 files (none on the new module); no line over 100 characters |

**Known debt, not changed here:** NDHost's other 11 simp-argument unfoldings of `Cfg.mapState`
(rule 10) predate this PR; they are in the backlog.

**Follow-ups this enables:** UN continuation 1's landing re-points `un_inRewTM` and
`un_mapState_comp` to this API. R continuation 2's `ic_rewind_scan` (#151) re-points when this
lands (the user's ruling). The `ExhaustiveReplay` and U2-S copies are in the dedup window.

**Order and replay.** No olean snapshot has this PR's base tree: `oleans-lspapi` and
`oleans-lu2sc1` each carry an unmerged PR's files. So after #149 merges, the campaign branch is
merged in, and the downstream closure is replayed from #149's merged-tree snapshot. That closure
has 5 modules: `Build/InputRewind`, `Build/NDHost`, `Diagonalization/NTimeHierarchy`, and the
`Diagonalization` and `TuringMachine` facades. **Pending.**

**Gate:** an API gate (gate 65). **Pending**, after the replay.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
