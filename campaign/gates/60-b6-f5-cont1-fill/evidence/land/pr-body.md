B6, F5 continuation 1 (`Build/InputDevice.lean`): **the ruler device's call rows
`Turing.exists_rulerDeviceTM` and the ruler host `Turing.exists_rulerHostTM` are proved**, with no
admitted dependency. With the boundary test (#133), everything in the module is proved. It unblocks
F6 (`Complexity.space_universal`) and U2-E. Delivered as item 2 of megafill B
(`fill-b6-rulerdevice-cont1.zip`, SHA-256 `76f45501…f38cf28`), complete (2/2).

**Commits** (on the campaign branch):
- `b6c9e0c5`, `b26d53c9`: the worker's two commits (`8fa8598e`, `0f57ba49`, on `6cfee544`),
  cherry-picked from its verified bundle; they touch only the owned file, unchanged at the tip;
- `8114e482`, the maintainer's, docstrings only: the module's status and main results, the
  `TuringMachine` facade's line, and an `**Implementation.**` paragraph after each target's frozen
  sketch (as #133 did for the test), since the proofs take routes the sketches do not name.

**What it adds:** 32 private `rd_` declarations. The call rows: one phase host runs the boundary
test, a one-step input-move leaf and a dispatch, in exactly `2ℓ + 5` steps (`C = 4`). The host: a
`Turing.Lockstep` over `Turing.rulerHostCfg`; a block costs one step, or `2ℓ + 3` after a live left
move from a cleared tag (`C = 3`); the endpoint, cut and frames from the lockstep lemmas.

**Review** (sub-agent; `campaign/fills/b6/reviews/rulerdevice-cont1/REVIEW.md`; "complete; land"):

| Check | Result |
|---|---|
| Integrity | `SHA256SUMS` 92/92; the bundle (sole prerequisite the base), the two commits and the patch series agree with the delivered file |
| Scope and freeze | the two homes and the two bodies only; the three statements and their docstrings byte-identical; imports unchanged |
| Elaboration | 0 errors, 0 warnings at the base and at the tip |
| Axioms | all three targets on `[propext, Classical.choice, Quot.sound]`, no `sorryAx` |
| Rule 10 | 17 definitions sealed and two simp sets erased; 38 controls fail sealed and pass unsealed; no other-file definition among 376 rewrite arguments |
| Probes | 62/62 and 148/148 |
| Gate instances | the delivered machines run on 24, the statement gate's adversarial cases included |
| v3 screen | 720 → 741 declarations, 488 → 489 pairs; the one new pair in-file at 79% |
| Lint | 0 FAIL; the one new WARN is the file's size |
| Sweep | 95 modules, 0 errors; sorry warnings 33 → 31, exactly the two targets |

The maintainer re-elaborated the landed head against `oleans-lg4c2` (0 diagnostics) and re-linted
(`TuringMachine/Build` 0 FAIL, 32 WARN over 39 files).

**Order.** U2-S's continuation (its own landing, `UniversalK`) shares `UniversalK`, `SelfUniversal`
and the facade with this PR's closure: whichever merges second replays again on the merged tree.

**Replay:** `replay-lf5c1.sh`, the merged tree (every file changed since #132's merge, 16 modules),
chained from `oleans-l132b`. **Pending.**

**Gate:** a fill gate. **Pending.**

🤖 Generated with [Claude Code](https://claude.com/claude-code)
