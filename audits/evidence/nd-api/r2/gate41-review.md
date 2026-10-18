# Gate 41 review: PR #122, the ND inventory API round 2 (PASS 0/0/1/14)

Reviewer: read-only review sub-agent, 2026-10-17. `$S` is the scratchpad; `$Z = $S/review/gate41`.
Every claim cites a saved output under `$Z/out/`.

**The PASS stands: 0 blockers, 0 majors.** All 15 findings are true at the auditor's severities.
Minor 1 is records only: the PR body's proof-method sentence, and a "final" lint log that is
actually commit 3's (`423b6536`), not the head's.

**#122 (`lean/nd-api-r2` at `6a48b93e`): clear to merge** once gate 41's records are committed.
It is the bottom of the stack: its base is the campaign branch, and #121 is merged. The replay
passed (313 of 313, static-equal 96). Its minor needs no `.lean` change.

## Inputs

| Input | Value | Evidence |
|---|---|---|
| Findings | `audits/nd-api-r2-findings.md` at `a5128d97` (verbatim; SHA-256 `ee9ff27a…947c`), read as data. It quotes the bundle's SHA-256 (row 2) | `out/bundle-check.txt` |
| Bundle | `41-nd-api-r2-gate/nd-api-r2-bundle.md`, SHA-256 `94f7c977…7b36`, 1,166,801 bytes, 60 sections. Folder `SHA256SUMS`: both OK | `out/bundle-check.txt` |
| Bundle rebuild | my own rebuild from git (Lean from `6a48b93e`, the rest from `2ce32d65`, `BUNDLE-FILES.txt` order): **byte-identical** | `scripts/rebuild.py`, `out/bundle-rebuild.txt` |
| Head | `6a48b93e` (local, `origin/lean/nd-api-r2` and GitHub agree; PR open, base the campaign branch). `0a5878ed` is an ancestor (#121, merged) | `out/pr122.json` |
| Worktree | `$S/wt-ndapi2` (read only). Lint re-run there | `out/lint-head-*.txt` |
| Lean | none run: minor 1 needs no `.lean` edit. The replay log in the records equals `$S/fills/replay/replay-lndapi2.log` (SHA-256 `80964291…5858`) | — |

The top-level `infra_local/gate-dispatches/SHA256SUMS` lists nothing after folder 26; the
per-folder `SHA256SUMS` is the one each README names, and it checks.

## (a) The findings at the head

| # | Auditor | Verified | Grade | Basis |
|---|---|---|---|---|
| 1 | minor | **true** | minor (records) | The saved and live PR bodies are identical (`out/pr122-body-live.md`), and both say "Every new equation is `rfl` except `codeSkipActionK_append`" (`r2/pr-body.md:30–31`). At the head, 19 proofs are `rfl`, `agreeOn_iff` is `Iff.rfl`, and two rewrite (`codeSkipActionK_append`, `bufferTape_of_neg`) (`out/proof-methods.txt`). `lint-head-final-TuringMachine.txt` is commit 3's: `Simulation.lean` has 1,175 lines at `423b6536` and 1,189 at `63d69835` and `6a48b93e`. My head re-run differs from it **only** in those two figures (1,189 lines, 60 publics); the totals are the same, 0 FAIL / 63 WARN, and `ClassNP/` 0 / 15 (`out/lint-head-*.txt`). Also, `lint-wt-ndapi2-*.txt` are commit 1's (`CounterLoop` at 2,252 lines, before `counterValue_eq`) |
| 2 | note | true | note | Bundle rebuilt byte for byte. Lean diff: 9 files, +141/−4. The four deleted lines are docstring text (`out/statements.txt`). Comment-aware freeze of all nine files: 22 declarations added, none removed, order kept, **no existing declaration's code changed** (`out/freeze-commentaware.txt`) |
| 3 | note | true (checked) | note | `workReadsK_zero = [Fin.elim0]`; `workReadsK_succ` puts tape 0 outermost (`Fin.cons w r`), so at three tapes the choice tape (tape 2) is innermost; `tableBitsK_eq` nests state, input read, work reads (`out/statements.txt`) |
| 4 | note | true | note | Read `actionBitsK_eq` and `codeSkipActionK_append` (the latter by `rw [← codeEraseActionK, codeReadActionK_append]`) |
| 5 | note | true (checked) | note | All 12 encoder equations match the definitions' match arms exactly; `none` write `[f,f]` differs from `some none` `[f,t]`; halt `[false]` differs from successor `true :: unaryFin s` (`out/statements.txt`) |
| 6 | note | true (checked) | note | `counterValue_eq` is `rfl`; `counterValue_bits` exists; `hostedLoopTM_run`'s `ht : Nat.ofDigits 2 (w.map Bool.toNat) = t` (`StepBlockLoop.lean:307, 435`) follows by `(counterValue_eq _).symm.trans (counterValue_bits t)` |
| 7 | note | true | note | `agreeOn_iff … := Iff.rfl` (`Simulation.lean:1144–1147`) |
| 8 | note | true (checked) | note | `bufferTape w z = if 0 ≤ z then w[z.toNat]? else none`; `summaryCells_eq` reads `bufferTape word (z − 2)` off cell 0, so cell 0 is `summary` and `bufferTape word (−2) = none` by `bufferTape_of_neg` |
| 9 | note | true (checked) | note | The third tape's no-write/right field is `optOptBoolBits none ++ signBits .pos = [f,f] ++ [t,f]`, as the auditor says |
| 10 | note | true | note | The three docstrings are the four deleted lines' replacements (`out/head-diff.patch`) |
| 11 | note | true | note | Not re-run here (the auditor reproduced both screens byte for byte) |
| 12 | note | true | note | The 20 axiom lines I read in `r2/logs/` agree with the pack (16 none; `propext` for the two work-read equations, the table and the counter; `propext, Quot.sound` for the skip law) |
| 13 | note | true | note | Corroborated by my re-run: 0 FAIL, 63 WARN; check 8 no longer lists `AgreeOn` or the four encoders (`out/lint-head-TuringMachine.txt`) |
| 14 | note | true | note | The records' replay log and static report equal the `$S/fills/replay/` copies (SHA-256); footer `# modules=313 failed=0` |
| 15 | note | true | note | Matches `audits/nd-api-resolutions.md:27` (the controller-contract ruling) |

**Reviewer additions** (not in the findings):

- **X1 (records note, affects gates 42–45):** this round's replay script is the template of the
  next four, and its precheck message "the Lean diff from 0a5878ed" was copied unchanged.
  - The message is correct here (`replay-lndapi2.sh` compares against `0a5878ed`).
  - It is wrong in `replay-lc1w.sh` (compares `6a48b93e`), `replay-lseam.sh` (`c567568f`),
    `replay-lg4c1.sh` (`0355da56`) and `replay-lx2.sh` (`4ab012d9`)
    (`out/replay-diagnostics.txt`).
  - Gates 42 and 45 flagged their own copy; gate 44's auditor missed its copy. It is a message
    only: no check is affected.

## (b) Minor 1's exact fix (records only; campaign branch)

`records-gate41.patch` (SHA-256 `680ee351…0c8b`) applies cleanly at `a5128d97`, which is also
the content at the origin tip `4cb6ceb0`, since that commit touches other files. It was made by
`scripts/records.py`, with every replacement asserted unique.

| # | File | Change |
|---|---|---|
| R-1 | `audits/nd-api-resolutions.md:57` | "Gate 41 is staged." becomes the gate's folder and bundle line. A new subsection, **"Round 2's result: PASS (0/0/1/14). The gate is closed."**, follows: minor 1's resolution, the notes' one-line disposition, X1, and "**#122 is clear to merge** at `6a48b93e`" |
| R-2 | new `audits/evidence/nd-api/r2/lint/lint-head-6a48b93e-TuringMachine.txt` and `-ClassNP.txt` | the head's lint (`out/lint-head-*.txt`, byte for byte). The old logs are kept, with the erratum in R-1 |
| R-3 | new `audits/evidence/nd-api/r2/pr-body-v2.md` | the corrected PR body (below). `pr-body.md` is kept as retrieved |

**PR #122's body** (the maintainer edits the live body, for example with
`gh pr edit 122 --body-file`, using R-3's text without its first two lines). There are two
edits:
- The proof-method sentence (body lines 28–29) becomes:
  ```
  Every new equation is `rfl` (`agreeOn_iff`: `Iff.rfl`) except two: `codeSkipActionK_append` goes
  through `codeEraseActionK` and `codeReadActionK_append`, and `bufferTape_of_neg` rewrites with
  `bufferTape_eq`. The first commit's statements are the review's draft
  ```
- The Replay bullet gains "**Passed (user, 2026-10-17):** 313 of 313, static-equal (96)", and a
  new "Gate 41: PASS 0/0/1/14" bullet points to the head's lint.

No `.lean` edit is needed.

## (c) Carry-forward

- **NF's brief** (note 15): cite the separately stated and gated `ndWriterTM_run_controller`,
  never the plan.
- **RC's brief** (notes 3, 5 and 9):
  - read the three-tape table through `tableBitsK_eq`, `workReadsK_succ` and `workReadsK_zero`;
  - read the choice field through the 12 encoder equations, with the third tape's no-write and
    right-move field `[false,false,true,false]`;
  - use the record boundaries from `codeReadActionK_append` and `codeSkipActionK_append`;
  - use the probe `r2/RCApiDraft.lean.txt` only for its consumer section, since its equations
    are redeclared there.
- **R's continuation** (note 6): read the loop's value hypothesis as
  `(counterValue_eq _).symm.trans (counterValue_bits t)`.
- **WC's continuation** (note 7): introduce the join's agreement with `(agreeOn_iff _ _ _).2`.
- **G2's seam layout** (note 8): read cell 0 through `summaryCells_eq` and `bufferTape_of_neg`.
  This closes the equation gap only. The seam-layout machine is gate 43's matter.
- **Replay scripts** (X1): the template's message should be parameterized on its base variable,
  so that derived scripts cannot carry a stale hash.

## (d) Bottom line

- **The PASS stands:** 0 blockers, 0 majors. Minor 1 is true (records). Notes 2–15 are true. I
  checked 2, 3, 5, 6, 8 and 9 in substance, and corroborated 12–14.
- **#122 is clear to merge at `6a48b93e`** once R-1 to R-3 are committed. The live PR body edit
  can follow at any time. There is no stack precondition: #122 is first, on the campaign
  branch.
