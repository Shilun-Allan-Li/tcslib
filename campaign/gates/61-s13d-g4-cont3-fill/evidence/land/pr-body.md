§13d G4, continuation 3 (`Build/ZoneRebalance.lean`): **checkpoint 1.1b, the positive right
pass characterized.** Both rows (`Turing.exists_zoneExtendTM`, `Turing.exists_zoneRebalanceTM`)
keep their original `sorry` bodies: this is a partial (0/2). Delivered as item 3 of megafill B
(`fill-s13d-g4-cont3-cp1.zip`, SHA-256 `fe1398e5…c71315e9`), the checkpoint archive recovered
after the session lost its workspace while on checkpoint 1.2.

**Commit:** `13e17589`, the worker's commit `01bcc6e0`, cherry-picked from its verified bundle.
The bundle's first two commits are #143's (the brief applied them by `git am`; same patch-ids),
merged already, so only the worker's own commit lands. It touches only the owned file.

**What it adds:** 8 private `zr_` declarations, and 4 inherited ones re-pointed:
- `zr_rightPass_post` and `zr_rightPass_envelope`, exactly the two statements the brief supplied:
  the right pass's endpoint (the new right zone written, the nonpositive half-line preserved, the
  scratch head restored) and its tape-0 envelope; the scratch envelope; the bridge to the frozen
  extension specification;
- the singleton-exit re-wrap of the pass, ready to sequence;
- one composite adapter (`Contract.seq` then `Contract.ofSegment`), replacing the four copies of
  that pattern from continuation 2.

The extension's status paragraph says what is now proved.

**Review** (sub-agent; `campaign/fills/s13d/reviews/g4-cont3/REVIEW.md`; "land checkpoint 1 as a
partial"):

| Check | Result |
|---|---|
| Integrity | the zip and 70/70 internal sums; the recovery record's claims hold; bundle, patches and file agree |
| Scope and freeze | owned regions only; both statements frozen; no import change; no new admission |
| Elaboration | 0 errors at the head and at the tip; only the two targets' sorry warnings |
| Axioms | the 12 new or changed privates on the standard three; `sorryAx` reaches each target only through its own body |
| 1.1b | the statements proved as supplied; the level-one values (cells 5–8, heads 7 and −7, time 48) checked in Lean |
| Rule 10 | 57 other-file definitions sealed over the private section; the controls fail inside and pass outside |
| Probes | the brief's 439 checks, standalone and in-module; the worker's 445 |
| v3 screen | 5 new pairs, all in-file, under 90%; the old 81% adapter pair is now 63% |
| Lint | 0 FAIL, 31 WARN over 39 files |

The maintainer re-elaborated the landed head against `oleans-lg4c2` (the two targets' warnings only)
and re-linted.

**Replay:** `replay-lg4c3.sh`, the merged tree (every file changed since #132's merge, 16 modules),
chained from `oleans-l132b`. **Pending.**

**Gate:** a fill gate for this partial. **Pending.**

🤖 Generated with [Claude Code](https://claude.com/claude-code)
