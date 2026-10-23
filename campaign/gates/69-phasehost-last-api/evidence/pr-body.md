**The phase host's last phase** (`Build/Seam`, two public lemmas): the API the seam layout's review
asked for (its F1; the user's ruling of 2026-10-22: a small API PR with its own gate).

- `Turing.phaseHostTM_tr_of_red_none`: at a state of phase `i` that the redirect table leaves
  alone, the host takes phase `i`'s action, with the successor tagged by `i`;
- `Turing.phaseHostTM_run_le`: with no redirect strictly before `T`, the host runs the tagged
  phase up to and including `T`, with nothing assumed of the state at `T`. So a host's last phase
  can end at a live exit that is not redirected, without the self-redirect the seam layout used.

Both sit beside `phaseHostTM` (whose own file may unfold it); the module header names them.

**Commits:** `0b671a28` (on the campaign branch at `9f8bba86`), and `eed76e8e`, the campaign branch
after #154 merged in (clean; `Seam` was unchanged there).

| Check | Result |
|---|---|
| Elaboration (against `oleans-lun2`) | the module's five unused-variable warnings, all in older code and the same as at the base |
| Axioms | `phaseHostTM_tr_of_red_none` on `[propext]`; `phaseHostTM_run_le` on `[propext, Classical.choice, Quot.sound]` |
| Rule 10 | a seal (`MultiTapeTM.runFrom`, `MultiTapeTM.step`, `Cfg.mapState`, `Action.mapState` irreducible) over primed copies: the proofs elaborate; the 4 controls fail sealed and close unsealed. The table equation unfolds only this file's `phaseHostTM` |
| Consumer probe | with `phaseHostTM` also sealed, as for another file: the agreement transfer with the table equation as its hypothesis, and a last phase's live endpoint from `phaseHostTM_run_le` |
| Freeze | 22 → 24 public (the two added), 8 → 8 private; nothing else changed |
| Lint | `TuringMachine/Build` 0 FAIL, 33 WARN over 40 files; no new line over 100 characters |
| Copies | no private restatement of either lemma on the campaign branch or the open PRs' branches |
| v3 screen | ⟨SCREEN⟩ |

**Replay:** `Seam`'s downstream closure (88 modules), from the latest merged-tree snapshot. #155
(the seam layout's sketches) has a closure inside this one, so it merges first and this PR replays
from its snapshot. **Pending.**

**Gate:** an API gate (gate 69). **Pending.**

🤖 Generated with [Claude Code](https://claude.com/claude-code)
