# Gate 45 review: PR #126, X2: BF as a hypothesis of `exists_diagonalizer` (PASS 0/0/2/10)

Reviewer: read-only review sub-agent, 2026-10-17. `$S` is the scratchpad; `$Z = $S/review/gate45`.
Every claim cites a saved output under `$Z/out/`.

**The PASS stands: 0 blockers, 0 majors.** All 12 findings are true at the auditor's severities.
- **Minor 1** is a `.lean` docstring on the top of the stack. I recommend committing it on #126,
  with time-invariant wording, and re-replaying.
- **Minor 2** is records only.

**#126 (`lean/ntime-diag-bf` at `5333b29b`): not yet clear to merge.** Its gate is closed (once
the records are committed) and its replay passed (2 of 2, static-equal 2). But it is stacked on
#125, which waits on #124 (gate 43 **failed**). If minor 1's commit lands, `replay-lx2b.sh` runs
first.

## Inputs

| Input | Value | Evidence |
|---|---|---|
| Findings | `audits/ntime-diag-bf-statements-findings.md` at `a5128d97` (verbatim; SHA-256 `35ec3db0…1a47`), read as data. Row 3 quotes the bundle's SHA-256 | `out/bundle-check.txt` |
| Bundle | `45-ntime-diag-bf-statements-gate/ntime-diag-bf-statements-bundle.md`, SHA-256 `296b21e2…824a`, 253,435 bytes, 34 sections; folder `SHA256SUMS` OK | `out/bundle-check.txt` |
| Bundle rebuild | from git (Lean `5333b29b`, other `11a14de2`): **byte-identical** | `out/bundle-rebuild.txt` |
| Head | `5333b29b`, one commit on `4ab012d9`; one file, `NTimeDiagonalizer.lean` (+20/−6; blob `3f67d257` → `026b52da`). PR open, base `lean/g4-cont1-partial` | `out/pr126.json` |
| Sources | `src/NTD-base.lean` (`4ab012d9`), `src/NTD-head.lean`, `src/NTimeHierarchy-head.lean`, `src/ExhaustiveReplay-head.lean` | — |
| Scratch worktree | `$Z/wt`, detached at `5333b29b`, `.lake/packages` linked | — |
| Elaboration | `tools/leanelab.sh $Z/wt $S/oleans-lx2 <file>`, 2 runs (two wordings), one at a time | `out/elab-NTD-patched*.out` |

## (a) The findings at the head

| # | Auditor | Verified | Grade | Basis |
|---|---|---|---|---|
| 1 | minor | **true** | minor | `NTimeDiagonalizer.lean:290`: "…`NTimeHierarchy`, which imports this module for". `NTimeHierarchy` imports `NDCodes`, `NTIME`, `TimeConstructible` and `NDNormalForm` only (`out/imports-and-x1.txt`). The PR body and pack describe the import as future (body lines 6–7) |
| 2 | minor | **true** | minor (records) | `x2/replay-lx2.sh:17–18` checks ancestry and the diff against `4ab012d9`, but its message names `0a5878ed` (`$S/review/gate41/out/replay-diagnostics.txt`) |
| 3 | note | true (reproduced) | note | Comment-aware freeze: 22 → 22, order kept, the only code change is `exists_diagonalizer` (`out/freeze-commentaware.txt`). Removing the `hBF` binder makes the whole comment-stripped source equal to the base's (`out/binder-only.txt`) |
| 4 | note | true (reproduced) | note | Whitespace-normalized, `hBF` equals the conclusion of `exists_ndAcceptsWithin_decider c` (`NTimeHierarchy.lean:190`) **and** of `ndAcceptsWithin_decider_of_universal` (`ExhaustiveReplay.lean:79`) (`out/hbf-match.txt`) |
| 5 | note | true | note | The sketch's top rung reads `hBF` only (`NTimeDiagonalizer.lean:307–309, 325`); `C = max 1 (max C_R C_BF)` is named at line 333 |
| 6 | note | true | note | The application `exists_diagonalizer hf hg c (exists_ndAcceptsWithin_decider c)` follows from row 4. `ntime_hierarchy`'s sketch is still the superseded prefix-clause route (`NTimeHierarchy.lean:249, 257, 274`; blob `cbb0cef8`, unchanged since gate 40) |
| 7 | note | true (checked) | note | `exists_timed_universal_NDTM`, `exists_ndAcceptsWithin_decider` and `FinNDTM.exists_exhaustiveDecider` are `sorry`; `ndAcceptsWithin_decider_of_universal` is proved (`out/admissions.txt`) |
| 8 | note | true | note | Mathematical instantiations; nothing to run |
| 9 | note | true | note | Row 3: the five definitions and `exists_queryTM` are code-identical |
| 10 | note | true (checked) | note | Imports unchanged (3). Gate 40's X3 lines are present at lines 32 and 197. The live PR body equals `x2/pr-body.md` (`out/pr126-body-live.md`) |
| 11 | note | true (reproduced) | note | `Diagonalization/` lint at the head: 0 FAIL, 1 WARN (`EXPCOM`), identical to `x2/lint-head.txt` (`out/lint-head-Diagonalization.txt`) |
| 12 | note | true | note | `x2/elab.out`: warnings at 270 and 334, `exit=0`; replay footer `# modules=2 failed=0`, static total 2 |

**Reviewer additions:** none beyond the shared replay-message item (gate 41's review, X1).

## (b) The minors' exact fixes

### Minor 1, `.lean` (`lean-ntd-import-docstring.patch`, SHA-256 `220e090b…73f4`)

`TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean:290–292`. The blob goes from
`026b52da` to `caafcb34`; the line count stays 360 and every line is at most 100 characters:
```
`TCSlib.Complexity.Diagonalization.NTimeHierarchy`, whose `ntime_hierarchy` needs this module, so
this module cannot import it; that proof supplies it from `Turing.exists_ndAcceptsWithin_decider`.
Taking it as a hypothesis keeps the two modules' imports acyclic.
```
- **Why not the auditor's wording.** The auditor's "which will import this module when
  `ntime_hierarchy` is filled" is also correct today, but it goes stale the day H's fill adds the
  import, and would then need reverting. The wording above states the need, which is true before
  and after.
- **The auditor's version is drafted too**, if preferred: `lean-ntd-import-docstring-auditor.patch`
  (SHA-256 `818e2132…c0b7`, blob `d5168782`). It gives the same elaboration result
  (`out/elab-NTD-patched-auditor.out`).

| Check (recommended wording) | Result |
|---|---|
| Elaboration against `oleans-lx2` | exit 0, the two contracts' warnings at 270 and 334, as in `x2/elab.out` (`out/elab-NTD-patched.out`) |
| Freeze, head → patched | no code change (`out/freeze-patch.txt`) |
| Lint | unchanged (`out/lint-patched-Diagonalization.txt`) |

**Where it should land: a commit on #126 itself.**
- **No restack.** #126 is the top of the stack, so nothing is restacked.
- **Who reads the text.** E-Q's and E-D's briefs issue after #126 and read this docstring, so the
  text should be right on their base.
- **The re-replay** is 2 modules, chained from `oleans-lg4c1`: `replay-lx2b.sh` (SHA-256
  `4b63ac21…c543`), derived from `replay-lx2.sh` by `scripts/mk-replay-lx2b.py` with asserted
  edits.
  - It pins blob `caafcb34`.
  - Its message names `4ab012d9` (minor 2).
  - It writes `oleans-lx2b` and `replay-lx2b.log`.
  - It needs `$S/wt-x2` advanced to the pushed head first.
  - If #124's resolution restacks #125, re-derive it from the new chain instead.
- **No regate needed, in my view.** The change is docstring only, and is the auditor's finding
  resolved. The user may still want gate 45's records to name it, which they do.
- **The commit message (draft):**
  ```
  C1-E: exists_diagonalizer's docstring, the import as a need (gate 45, minor 1)

  NTimeHierarchy does not import NTimeDiagonalizer yet; ntime_hierarchy's fill adds that import.
  The sentence now says why the import cannot go the other way, which stays true after that fill.
  Docstring only; the line count is kept.

  Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
  ```
- **PR #126's body (draft additions):**
  - under its change list: "A second commit (gate 45, minor 1): the docstring's import sentence
    states the need, not a present import. Docstring only."
  - in Checks: "Replay re-run: `replay-lx2b.sh` at the new head."

**The alternative:** leave #126 unchanged, and carry the fix to E-Q's landing, which edits the
same file and has its own fill gate. E-Q's and E-D's workers would then read the false sentence.

### Minor 2, records (`records-gate45.patch`, SHA-256 `a7deaab5…875c`; applies cleanly at `a5128d97`)

| # | File | Change |
|---|---|---|
| R-1 | new `audits/ntime-diag-bf-statements-resolutions.md` | round 1, gate closed: minor 1 (the fix, its home, the replay), minor 2 (kept as run; `replay-lx2b.sh` carries the correct message; the three other copies), notes 3–12, carry-forward, and "**#126 is not yet clear to merge**" with the reason |
| R-2 | `audits/ntime-diag-statements-resolutions.md` (X2's paragraph) | appends "**Done:** PR #126 (`5333b29b`); gate 45, PASS 0/0/2/10 (`audits/ntime-diag-bf-statements-resolutions.md`)." |

**After the re-replay**, the records gain `x2/replay-lx2b.sh`, `.log` and `-static.txt`, and the
minor-1 patch.

## (c) Carry-forward

- **E-D's brief** (notes 5 and 8):
  - extract `hBF`'s machine before building `D`;
  - `C = max 1 (max C_R C_BF)`;
  - the top's bound is `C_BF·2^{C_BF(T*+1)} ≤ C·2^{C(T*+1)} ≤ n ≤ g n`;
  - keep the first-verdict stop, silent provisional output, and the clock's inclusive finish
    deadline;
  - sanity checks: BF rejects at budget 0, and a timed-out simulation that emitted `[true]`
    rejects.
- **H's brief** (notes 6 and 10):
  - add `import TCSlib.Complexity.Diagonalization.NTimeDiagonalizer`;
  - apply `exists_diagonalizer hf hg c (exists_ndAcceptsWithin_decider c)`;
  - fix every constant before choosing a late recurring stage.
  - **X1 (gate 40's review, L-2) is still unapplied** at #126's head. It waits for UN's
    integration, before H's brief.
  - If the auditor's wording is chosen for minor 1, H's fill reverts it to "imports".
- **Admissions** (note 7): BF's and UN's statements and the exhaustive decider stay `sorry`, and
  their gates must keep them explicit. `ndAcceptsWithin_decider_of_universal` is conditional.
- **Bundles** (note 11): carry every file the lint scope reads (gate 40's review's
  recommendation, still open; this bundle had 2 of 5).

## (d) Bottom line

- **The PASS stands:** 0 blockers, 0 majors. Both minors are true. Notes 3–12 are true. I
  reproduced 3, 4 and 11, and checked 7 and 10.
- **#126 is not yet clear to merge.** The preconditions:
  1. **Stack order:** #125 merges first, and #125 waits on #124 (gate 43 FAILED). If the user
     restacks #125 and #126 onto #123 instead, #126's replay is re-derived from the new chain.
  2. **If minor 1's commit lands:** `replay-lx2b.sh` (or its re-derived successor) passes at the
     new head.
  3. **Gate 45's records** (R-1, R-2) are committed.
- Then #126 is clear to merge.
