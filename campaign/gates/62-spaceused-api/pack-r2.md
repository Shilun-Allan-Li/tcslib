# External audit pack — the space API (PR #149, an API gate), round 2

**Round 1** (`findings.md`; resolutions `resolutions.md`): FAIL, 0 blockers, 1 major, 1 minor, 8
notes. The major: `Build/WindowRun`'s private `wr_space` had exactly the statement of the new
public `Turing.MultiTapeTM.spaceUsed_le_of_abs_le` (at `Γ P : Type`) with its own copy of the
proof. **The user ruled (2026-10-22) to fix it in this PR.** The minor (F3 continuation 2's draft
probe count) is a records fix, done.

**The head:** `lean/spaceused-api` at `3d0f80b5`, one commit after round 1's head `097f3e04`; its
merge-base with the campaign branch is `144201de`. This bundle's records are from a later records
commit (stated in the bundle's README).

| File | Change since round 1 |
|---|---|
| `TuringMachine/Build/WindowRun` | `wr_space`'s body is `MultiTapeTM.spaceUsed_le_of_abs_le R d t radius henv`; its docstring says so; its statement and its two uses (in the runner's proof) are unchanged (`evidence/round1-fix/wr_space-repoint.patch`) |

## Brief for the auditor

1. **The fix.** Is the duplicate gone: does `wr_space` now carry no proof of its own, and does
   the public lemma apply at its arguments exactly (the universe, the envelope hypothesis's form)?
   Is anything else in `WindowRun` changed?
2. **No regression.** `WindowRun` elaborates and its two public rows keep their axioms; the
   module's consumers (`SpaceComplexity/WindowClock`, the facades) re-elaborate (the replay).
3. **Round 1's other points.** Is the minor's records fix adequate (F3 continuation 2's draft:
   both new lemmas in its import probe, 102 checks)? Is anything in round 1's resolutions
   unaddressed?
4. **Duplication.** The five-file screen at the new head: `wr_space` is now below the screen's
   eligibility threshold, and no pair is new or gone (`evidence/round1-fix/screen-r2.txt`).

## Repository-side attestations (verify or challenge)

- **Elaboration and axioms** (against `oleans-lspapi`, round 1's replay snapshot):
  `Build/WindowRun` at the head with `#print axioms` appended: no diagnostic;
  `exists_windowRunnerTM` and `exists_windowLoopTM` on `[propext, Classical.choice, Quot.sound]`
  (`evidence/round1-fix/elab-WindowRun-repoint.out`).
- **Freeze:** 10 → 10 public, 25 → 25 private; only `wr_space` changed
  (`evidence/round1-fix/freeze-WindowRun.txt`).
- **Lint:** `TuringMachine/Build` 0 FAIL, 33 WARN over 39 files; no line over 100 characters
  (`evidence/round1-fix/lint-build.txt`).
- **Screen (v3), the five files at the head:** 135 declarations, 30 pairs; against round 1's, no
  pair new or gone (`evidence/round1-fix/screen-r2.*`).
- **Replay:** `replay-lspapi2.sh`: `WindowRun`'s downstream closure (4 modules: `Build/WindowRun`,
  `SpaceComplexity/WindowClock`, the `SpaceComplexity` facade, the `TuringMachine` facade) at
  `3d0f80b5`, chained from `oleans-lspapi` (the tree of `097f3e04`).
  **Passed (user, 2026-10-23): 4 of 4**, 0 failed, static-equal (1: `WindowClock`'s stub)
  (`evidence/round1-fix/replay-lspapi2.*`, `evidence/round1-fix/down-lspapi2.txt`).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/62-spaceused-api/findings-r2.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `spaceused-api-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
