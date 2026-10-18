# PR #119's body, as retrieved 2026-10-17 (head `1e45f50a`)

**The ND inventory API.** Under the user's "Everything" rule (2026-10-16), every definition a brief's route reads gets a published equation before dispatch. C1's pre-ship inventory (the NTIME hierarchy's fill briefs; plan `audits/evidence/c1/C1-fill-plan.md`) found the nondeterministic counterparts of #118's deterministic API missing, and this PR adds them. It has 59 equations in three commits, all declarations and `simps` attributes (`isSimp := false`, no `@[simp]`): 41 in the first (7 hand-written, 34 generated), 14 in the second and 4 in the third, both from C1 wave 1's route inventory. **It gets a short gate before it merges.**

**#118 is merged** (`f7546373`); #119 now sits on the tip, whose Lean is #118's `531b98a2`. **#120 and #121 are stacked on it.**

| File | Additions | For |
|---|---|---|
| `Nondeterministic` | `NDTM.stepWith_of_some` (the live ND step, beside `stepWith_of_halt`); `NDTM.initCfg_eq`; `NDTM.haltsWithin_iff`; the fields of `fixChoice`, `MultiTapeTM.toNDTM`, `FinTM.toFinNDTM`, `relabelState` (`simps`) | W (the writer's ND step); E and NF (an arbitrary NDTM's step and relabelling); R and UN (initial configurations, all-branch halting) |
| `ClassNP/NTIME` | `FinNDTM.acceptsWithin_iff`, `FinNDTM.decidesInTime_iff`, `Complexity.mem_NTIME_iff` (each `Iff.rfl`) | E, UN, the hierarchy's membership arguments |
| `ChoiceReplay` | the fields of `replayTM` and `withChoiceTape` (`simps`) | RC (the replay machine's table); R and E (the replay lemma's configurations) |
| `NDCodes` | `CodeNDTM.toFinNDTM`'s `k`, `State`, `tm` (`simps`) | R, UN, NF |
| `Build/NDHost` | the fields of `guessRunCfg` and `streamStartCfg` (`simps`) | UN (the handoff, the core's start) |
| `Build/StepClock` | the fields of `clockCfg` (`simps`); `Cfg.stopped_iff` | E (the step clock's configurations and its stop condition) |
| `Build/StepBlock` (second commit) | `tableTape_eq`, `summaryTape_eq`, `exit_true`, `exit_false`, `Rep_iff`, `outputSummary_nil`, `summaryCells_eq` | R (the definitions `hostedLoopTM_run` and `hostedLoop_read` read: H2's step block in H1's hosted loop) |
| `Build/Convention` (third commit) | `Cfg.ofWords_state`, `_inputPos`, `_workTapePos`, `_output`, beside `Cfg.ofWords_workTapes` | R's startup (`FinTM.exists_installCallTM` is stated through `Cfg.ofWords` seams); the diagonalizer's input call |
| `Build/VirtualInput` (second commit) | `vhostCfg`'s five fields (`simps`); `vhostCap_eq`, `vhostSilentCfg_eq` | R (the hosted loop runs under Z1); the diagonalizer's top rung (Z1's suppressing host) |

**Checks (maintainer, against `oleans-lbapi4`, the tip plus #118's round 3):**

| Check | Result |
|---|---|
| Elaboration | all nine files with probes appended: 0 errors; warnings equal to the base (NTIME 1, a Mathlib deprecation; NDHost 1, the writer's `sorry`; the rest 0) |
| New names | the 59 resolve, with their docstrings' formulas; axioms standard (12 none; the rest within `propext`, `Quot.sound`, `Classical.choice`) |
| Freeze | publics added only; no statement, body or private changed |
| Lint | 0 FAIL; `TuringMachine/` 67 → 63 WARN, `ClassNP/` 16 → 15; check 8 drops the ten definitions it flagged in the first commit's files, `VirtualInput`'s two, and four of `StepBlock`'s twelve (the other eight are the step block's internals, read through its run lemmas) |
| Screen (13 files, with `StepBlock` and `VirtualInput`) | 240 → 244 declarations, 33 → 38 pairs. The 5 new pairs are boilerplate: the four configuration-valued definitions each carry the same `attribute [simps … state inputPos workTapes workTapePos output]` line, which the screen attaches to the declaration above it. No proof text is shared |

**Replay (user):** `replay-lndapi.sh`, the nine files' downstream closure (189 modules), from `oleans-lbapi4` (since #118 merged, the tip's Lean). `WindowClock` (F3) and `UniversalK` (U2-S), both briefed after #118, are downstream. The additions are declarations only, so it doesn't matter which merges first.

Records: `audits/evidence/nd-api/` (NOTES with the inventory's judgement table, the probes, freeze, lint, screen, patch).

🤖 Generated with [Claude Code](https://claude.com/claude-code)

