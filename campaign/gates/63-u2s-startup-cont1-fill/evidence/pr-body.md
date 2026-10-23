U2-S continuation 1 (`UniversalK.lean`): **`Turing.exists_selfStartupTMK`, the `k`-generic
startup, is proved**, modulo exactly `Turing.exists_seamLayoutTM`, which #145 proves; after #145 it
is admission-free (and so is `SelfUniversal`'s `exists_selfStartupTM`, its `k = 1` case).
Delivered as item 1 of megafill B (`fill-u2s-startup-cont1.zip`, SHA-256 `95a0e169…1dbdd4`),
complete. **Merge after #145.**

**Commits** (on the campaign branch):
- `89332143`, `14b1ac5c`, `90bf1840`, `7e9aff5b`: the worker's four commits (`51a8c643..8e1aee0f`,
  on `6cfee544`), cherry-picked from its verified bundle; they touch only the owned file (the first
  adds the authorized `Build/SeamLayout` import), unchanged at the tip;
- `c6733db3`, the maintainer's, docstrings only: the module's status and main results, and the
  `TuringMachine` facade's line;
- `28150fc1`: the campaign branch merged in after #145, #146 and #148 (the facade auto-merged;
  `UniversalK` unchanged).

**What it adds:** 24 private `ss_` declarations: the capture over the buffered composite (through
the cast pair of #132), its normalization, the redistribution by the seam layout, the code buffer's
cleanup and the rewinds, at a time `T` and a bound `B = n·(T + 1)` chosen from the code alone.

**The user's ruling (2026-10-22): the cleanup's refinement is accepted** (the review's F1). On the
empty code the buffer is all blank, and no machine can tell its head at `−1` from `0`, so the
cleanup uses a second private one-step leaf (moving only on a blank cell) and the canonizer's fixed
final position on the empty code, a constant of the code scheme `E`.

**Review** (sub-agent; `campaign/fills/u2s/reviews/startup-cont1/REVIEW.md`; "complete; land after
#145"):

| Check | Result |
|---|---|
| Integrity | `SHA256SUMS` 122/122; the bundle (sole prerequisite the base), four commits and the patch series agree with the delivered file |
| Scope and freeze | regions (a)–(c) only; the statement and its docstring byte-identical; one import |
| Elaboration | 0 errors at the base and at the tip; only the other two stubs' sorry warnings |
| Axioms | `sorryAx` only through `exists_seamLayoutTM`; the standard three against #145's tree |
| Rule 10 | 32 definitions sealed and three simp sets erased; 36 controls fail sealed and pass unsealed |
| Probes | 111/111 and 121 checks of 118 names |
| v3 screen | 674 → 696 declarations, 514 → 525 pairs; 11 new pairs, all in-file, maximum 84% |
| Lint | 0 FAIL; the one new WARN is the file's size |
| Sweep | 95 modules, 0 errors; sorry warnings 33 → 32 |

The maintainer re-elaborated the landed head against `oleans-lg4c2` (the two other stubs' warnings
only) and re-linted (`TuringMachine` 0 FAIL).

**Order.** #145, #146 and #148 have merged (2026-10-22) and are in this head. #149 (the space API)
also replays a closure containing this one's: **merge #149 first**; this PR then re-replays its six
modules on the merged tree. (If this PR merges first, #149's 324-module replay repeats.)

**Replay:** `replay-lu2sc1.sh`, the merged tree `28150fc1`: the downstream closure of every file
changed since #144's merge (6 modules: `Build/InputDevice`, `Build/SeamLayout`,
`Build/ZoneRebalance`, `UniversalK`, `SelfUniversal`, the facade last), chained from `oleans-lsk2`.
**Pending.**

**Gate:** a fill gate (gate 63). **Pending.**

🤖 Generated with [Claude Code](https://claude.com/claude-code)

