**The phase host's last phase** (`Build/Seam`, two public lemmas): the API the seam layout's review
asked for (its F1; the user's ruling of 2026-10-22: a small API PR with its own gate).

- `Turing.phaseHostTM_tr_of_red_none`: at a state of phase `i` that the redirect table leaves
  alone, the host takes phase `i`'s action, with the successor tagged by `i`;
- `Turing.phaseHostTM_run_le`: with no redirect strictly before `T`, the host runs the tagged
  phase up to and including `T`, with nothing assumed of the state at `T`. So a host's last phase
  can end at a live exit that is not redirected, without the self-redirect the seam layout used.

Both sit beside `phaseHostTM` (whose own file may unfold it); the module header names them.

**Commits:** `0b671a28` (on the campaign branch at `9f8bba86`); `eed76e8e`, the campaign branch
after #154 merged in (clean; `Seam` was unchanged there); `9f82de74`, `phaseHostTM_run` through
the new lemmas: its window up to `T` was the same proof as `phaseHostTM_run_le`, inline (the
screen's 77% pair), and its dispatch step had unfolded `MultiTapeTM.step` and `Cfg.mapState`; its
statement is unchanged; `a4d9b024`, the campaign branch after #155 merged in (clean);
`0e5f210b`, the gate's round-1 fix (below).

| Check | Result |
|---|---|
| Elaboration (against `oleans-lun2`) | the module's five unused-variable warnings, all in older code and the same as at the base |
| Axioms | `phaseHostTM_tr_of_red_none` on `[propext]`; `phaseHostTM_run_le` on `[propext, Classical.choice, Quot.sound]` |
| Rule 10 | a seal (`MultiTapeTM.runFrom`, `MultiTapeTM.step`, `Cfg.mapState`, `Action.mapState`, `Action.apply`, `Cfg.workTapeSymbols`, `moveInputPos`, `Cfg.inputSymbol` irreducible; `Action.apply` erased from simp) over primed copies of the three lemmas: the proofs elaborate; the 8 controls fail sealed and close unsealed. The table equation unfolds only this file's `phaseHostTM` |
| Consumer probe | with `phaseHostTM` also sealed, as for another file: the agreement transfer with the table equation as its hypothesis, and a last phase's live endpoint from `phaseHostTM_run_le` |
| Freeze | 22 → 24 public (the two added), 8 → 8 private; one body changed, `phaseHostTM_run`'s (statement unchanged) |
| Lint | `TuringMachine/Build` 0 FAIL, 33 WARN over 40 files; no new line over 100 characters |
| Copies | no private restatement of either lemma on the campaign branch or the open PRs' branches |
| v3 screen | `Seam` and the seven files using both `phaseHostTM` and the agreement transfer: 548 → 549 declarations, 125 → 125 pairs, none new or gone (before the rewrite, one new in-file 77% pair, which it removes) |

**Replay:** `replay-lphl.sh`, `Seam`'s downstream closure (88 modules) at `a4d9b024`, chained from
`oleans-lslsk` (#155's snapshot, the campaign's tree). **Passed (user, 2026-10-23): 88 of 88**, 0
failed, static-equal (53).

**Gate 69, round 1: FAIL** (1 major, 1 minor). The major: six older proofs in four files
re-derived the new prefix lemma (the agreement transfer with the host's table read by unfolding
`phaseHostTM`). **Fixed here (the user's ruling, 2026-10-23), `0e5f210b`:** `WindowRun`'s
`wr_prefix`, `StepBlock`'s `recordSkipTM_tail`, three `have`s in `Inclusions` (`b2b_trial_run`,
`b2b_round_run`, `b2b_finish_answer`) and `CodeSimulator`'s `canonEmitVerdict` are applications of
`phaseHostTM_run_le`; `OracleSim`'s `oracleHost_offQuery`, found by a wider search, is
`phaseHostTM_tr_of_red_none`. Statements unchanged; the five files' diagnostics and axioms are the
base's; a seal over the re-points (`phaseHostTM` and the run, step and renaming definitions
irreducible) with seven controls per file; screen 549 declarations, 125 pairs, none new or gone.
The minor: this description's file count (now seven) and the lint record (re-run at the head).

A seal sweep of every file that uses the host finds 12 older one-field or one-step reads of
`phaseHostTM` (its start state, its redirect branch's dispatch, single table reads). They need
equations this PR does not publish; **by the user's ruling (2026-10-24) a follow-up API PR**
publishes a start-state and a redirect-branch equation and re-points them.

**Replay (round 2):** `replay-lphl2.sh`, the five files' downstream closure (23 modules) at
`0e5f210b`, chained from `oleans-lphl`. **Pending.** **Gate 69, round 2: pending.**

🤖 Generated with [Claude Code](https://claude.com/claude-code)

