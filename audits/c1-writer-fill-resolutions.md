# C1-W fill gate (PR #123): resolutions (round 1; gate CLOSED)

**Gate:** the fill gate of PR #123, C1-W: the bounded choice writer's contract
`Turing.ndWriterTM_run_block` (`TuringMachine/Build/NDHost.lean`), proved (`lean/c1-writer` at
`c567568f`, stacked on #122). Pack `audits/c1-writer-fill-pack.md`; bundle SHA-256
`132a9861ae2599f0226cb830e2f7ce335260b3e9ee85ea69db4721acfd27c6ca` (38 sections; folder
`42-c1-writer-fill-gate/`). Replay passed (user, 2026-10-17): 2 of 2, static-equal (0).

**Round 1** (`audits/c1-writer-fill-findings.md`, verbatim): **PASS, 0 blockers, 0 majors,
2 minors, 11 notes.** The auditor could not run Lean and treated the elaboration, axiom and replay
logs as supplied evidence. The maintainer's review sub-agent verified every finding at
`c567568f`: all true, at the auditor's severities. **The gate is closed.**

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | `NDHost.lean:68–69`, Main results: `guessRunTM_silent_spec` is still "proved modulo the writer". | **True.** It is the only such text left in the module and the facade. **The fix** (`.lean`, docstring only, line count kept; blob `034ef7d9` → `6f57dcf8`): "`Turing.guessRunCfg_clean` (proved), `Turing.guessRunTM_silent_spec` (proved) — the" / "interpreter core's interface: precondition, emission capture, live verdicts." Elaborated against `oleans-lc1w`: exit 0, no warnings, standard axioms. **It rides on the next PR that edits `Build/NDHost`**, the controller-contract statement PR (`ndWriterTM_run_controller`; `C1-fill-plan.md`, last section), whose gate pack names it. A commit on #123 would force #124–#126 to be restacked and re-replayed. |
| 2 | minor | `land/freeze.txt:4` reports "UNAUTHORIZED BODY CHANGE: guessRunTM_runWith_handoff"; `land/replay-lc1w.sh:19`'s failure message names `0a5878ed`, while the check is against `6a48b93e`. | **True; records.** With comments stripped, `guessRunTM_runWith_handoff`'s code is unchanged; only `ndWriterTM_run_block`'s proof changed (`land/freeze-commentaware.txt`, added; `freeze.txt` kept as run). The script is kept as run; its message should name `6a48b93e`. The same copied message is in `replay-lseam.sh`, `replay-lg4c1.sh` and `replay-lx2.sh` (from `replay-lndapi2.sh`, where it is right), and is corrected wherever a script is next derived. |
| 3–13 | notes | Integrity and freeze; the definitions; the single-induction route; the second clause's uniformity; the boundary cases (`m = 0`, `m = 2`, negative heads, `hblock` essential); the screen's two pairs; credit and history; the logs, lint and replay. | No action. Note 9: the two statement-shaped pairs `wr_cfg`/`guessRunCfg` (56%, 50%) are accepted, with no refactor. |

**Carried:**
- To the controller-contract statement PR: minor 1's line, named in its pack.
- To W's continuation (the controller flavor's fill): the step lemma's pattern (`wr_cfg_stepWith`,
  one lemma branching on the scanned cell, not a step/finish pair) and the boundary probe at
  `m = 0` (the stop on the first step, nothing written; gate 37's resolution, finding 2).

**#123 is clear to merge** at `c567568f`, after #122 (its base): once #122 merges, retarget #123
to the campaign branch.
