# Gate 42 review: PR #123, C1-W landed (`ndWriterTM_run_block` proved) (PASS 0/0/2/11)

Reviewer: read-only review sub-agent, 2026-10-17. `$S` is the scratchpad; `$Z = $S/review/gate42`.
Every claim cites a saved output under `$Z/out/`.

**The PASS stands: 0 blockers, 0 majors.** All 13 findings are true at the auditor's severities.
- **Minor 1** is a `.lean` status line. I recommend landing it in a follow-up rather than on
  #123.
- **Minor 2** is records only.

**#123 (`lean/c1-writer` at `c567568f`): clear to merge** once gate 42's records are committed,
**after #122**, which is its base. Once #122 merges, retarget #123 to the campaign branch. The
replay passed (2 of 2, static-equal 0).

## Inputs

| Input | Value | Evidence |
|---|---|---|
| Findings | `audits/c1-writer-fill-findings.md` at `a5128d97` (verbatim; SHA-256 `30a50eda…11c9`), read as data. Row 3 quotes the bundle's SHA-256 | `out/bundle-check.txt` |
| Bundle | `42-c1-writer-fill-gate/c1-writer-fill-bundle.md`, SHA-256 `132a9861…c6ca`, 2,081,768 bytes, 38 sections; folder `SHA256SUMS` OK | `out/bundle-check.txt` |
| Bundle rebuild | from git (Lean `c567568f`, other `11a14de2`): **byte-identical** | `out/bundle-rebuild.txt` |
| Head | `c567568f` = `6a48b93e` + `7fdd7797` (the proof) + `c567568f` (facade). PR open, base `lean/nd-api-r2` | `out/pr123.json` |
| Sources | `src/NDHost-base.lean` (`6a48b93e`), `src/NDHost-head.lean` (`c567568f`) | — |
| Scratch worktree | `$Z/wt`, detached at `c567568f`, `.lake/packages` linked | — |
| Elaboration | `tools/leanelab.sh $Z/wt $S/oleans-lc1w <file>`, 2 runs, one at a time | `out/elab-*.out` |

## (a) The findings at the head

| # | Auditor | Verified | Grade | Basis |
|---|---|---|---|---|
| 1 | minor | **true** | minor | `NDHost.lean:68–69` still reads "`Turing.guessRunTM_silent_spec` (proved modulo the / writer)". It is the only such text left in the module and in the facade: a grep for "modulo", "sorried" and "writer…sorr" finds nothing else. The facade's line 194 belongs to another module. `guessRunTM_silent_spec` prints standard axioms (`land/elab-NDHost.out`; `out/elab-NDHost-patched-axioms.out`) |
| 2 | minor | **true** | minor (records) | `land/freeze.txt:4` says "UNAUTHORIZED BODY CHANGE: guessRunTM_runWith_handoff". My comment-aware comparison finds 6 privates added, none removed, order kept, and the **only** code change is `ndWriterTM_run_block`, whose signature is byte-identical (`out/freeze-commentaware.txt`, `out/target-signature.txt`). `land/replay-lc1w.sh:19` compares against `6a48b93e`, but its message says `0a5878ed`. The records' script and log equal the `$S/fills/replay/` copies (SHA-256) |
| 3 | note | true | note | Bundle rebuilt byte for byte; 25 → 25 publics, 2 → 8 privates (`out/lint-head-TuringMachine.txt` INFO line) |
| 4 | note | true | note | Read `wr_cfg` and `ndWriterTM_run_block` at the head |
| 5 | note | true (checked) | note | The names in the helpers' `rw`/`simp` lists are lemmas, locals, the six privates, and the file's own `ndWriterTM` and `wr_cfg`. No foreign definition appears (`out/route-names.txt`) |
| 6 | note | true (checked) | note | The second clause applies `wr_prefix` to `w'` at `u = w'.length` with `List.take_length`, so it covers every shorter word, not only prefixes of `w` |
| 7 | note | true | note | Follows from `wr_cfg_stepWith`'s two branches. I did not run them as tests |
| 8 | note | true (checked) | note | Dropping `hblock` breaks the conclusion: with a blank at the head cell, the first step enters `done` and the head stays put |
| 9 | note | true | note | Not re-run (the auditor reproduced both screens). The pairs come from the frozen statement's tape-update expression |
| 10 | note | true | note | The PR body's credit and the pack's ruling agree (`out/pr123-body-live.md` equals `land/pr-body.md`) |
| 11 | note | true | note | `land/elab-NDHost.out`: 8 axiom lines, all standard, `exit=0` |
| 12 | note | true (reproduced) | note | Lint at the head: 0 FAIL, 63 WARN over 79 files, **identical** to `land/lint-head.txt`. NDHost has 1,098 → 1,236 lines, the widest 98 characters |
| 13 | note | true | note | Footer `# modules=2 failed=0`; the precheck pins as described |

**Reviewer additions:** none of substance. The stale replay message is the shared X1 of gate
41's review: four derived scripts carry it, and this is one of them.

## (b) The minors' exact fixes

### Minor 1, `.lean` (one docstring line pair; `lean-ndhost-status.patch`, SHA-256 `e8779c9d…fa6d`)

`TCSlib/Complexity/TuringMachine/Build/NDHost.lean:68–69`. The blob goes from `034ef7d9` to
`6f57dcf8`, and the line count is unchanged (1,236):
```
* `Turing.guessRunCfg_clean` (proved), `Turing.guessRunTM_silent_spec` (proved) — the
  interpreter core's interface: precondition, emission capture, live verdicts.
```
It was made by `scripts/edit-ndhost.py` (asserted unique) and applied in `$Z/wt` at `c567568f`.

| Check | Result |
|---|---|
| Elaboration against `oleans-lc1w` | exit 0, no warnings (`out/elab-NDHost-patched.out`); with `#print axioms` appended, the target and three assembly theorems print `[propext, Classical.choice, Quot.sound]` (`out/elab-NDHost-patched-axioms.out`) |
| Freeze, head → patched | no code change in any declaration (`out/freeze-patch.txt`) |
| Lint | identical to the head's (`out/lint-patched-TuringMachine.txt`) |
| Up the stack | NDHost is the same blob `034ef7d9` at `0355da56`, `4ab012d9` and `5333b29b`, so the patch applies unchanged on any later base |

**Where it should land: a follow-up, not #123.** The options:

- **A commit on #123.** I advise against it:
  - every replay above #123 pins its parent's head and requires its Lean diff from that head to
    be "exactly" its own files (`replay-lseam.sh:18–19`, `replay-lg4c1.sh:17–18`,
    `replay-lx2.sh:17–18`);
  - so a commit here forces #124–#126 to be restacked, their scripts re-derived, and all four
    PRs re-replayed;
  - the snapshot chain from `oleans-lc1w` would be rebuilt as well.
- **On the top of the stack (#126).** This mixes scopes: #126 is a `Diagonalization` statement
  PR, and its gate has passed. It would also grow #126's replay list.
- **Recommended: the next PR that edits `Build/NDHost`.** That is the controller-contract
  statement PR (`ndWriterTM_run_controller`; `C1-fill-plan.md`, last section: "after W
  integrates"). Its gate pack names the line. The precedent is gate 40's L-1, which rode on
  #122. If that PR is far off, a one-commit docstring PR after the stack merges does the same,
  with a 2-module replay (NDHost and the facade).

### Minor 2, records (`records-gate42.patch`, SHA-256 `235899b6…882a`; applies cleanly at `a5128d97`)

| # | File | Change |
|---|---|---|
| R-1 | new `audits/evidence/c1/fills/writer-1/land/freeze-commentaware.txt` | the comment-aware result, with a 4-line header explaining `freeze.txt:4`'s false positive. `freeze.txt` is kept as run |
| R-2 | new `audits/c1-writer-fill-resolutions.md` | round 1, gate closed: minor 1 (the fix and its home), minor 2 (the freeze record; the script's message, kept as run; the same message in the three later scripts), notes 3–13, carry-forward, and "**#123 is clear to merge** … after #122" |

The script `replay-lc1w.sh` is not edited: it ran, and its records copy is evidence.
- **If it is ever re-derived:** line 19's message should read "the Lean diff from 6a48b93e
  must be exactly NDHost and the TuringMachine facade".
- **The same applies to the other copies:** `replay-lseam.sh:19` should name `c567568f`, and
  `replay-lg4c1.sh:18` should name `0355da56`. `replay-lx2.sh:18` is gate 45's.

## (c) Carry-forward

- **To the controller-contract statement PR:** minor 1's line, named in its pack. Also its
  boundary probe at `m = 0` (the stop on the first step, nothing written; gate 37's resolution,
  finding 2).
- **To W's continuation** (the controller flavor's fill):
  - reuse the one-lemma step pattern (`wr_cfg_stepWith` branches on the scanned cell), not a
    step/finish pair, which made the 91% screen pair;
  - keep the second clause uniform over all shorter words (note 6).
- **Note 9:** the accepted `wr_cfg`/`guessRunCfg` pairs (56%, 50%) are part of the screen base
  for the next NDHost brief (787 declarations, 1,020 pairs, 380,919 characters).
- **Note 13's attestation limits** stay in the packs: the snapshot chain and closure
  calculation are maintainer- and user-attested.

## (d) Bottom line

- **The PASS stands:** 0 blockers, 0 majors. Both minors are true. Notes 3–13 are true. I
  checked 5, 6 and 8 in substance, and reproduced 3 and 12.
- **#123 is clear to merge at `c567568f`** once R-1 and R-2 are committed, with one stack
  precondition: **#122 merges first**, then #123 is retargeted to the campaign branch. Minor 1's
  line does not hold the merge; it rides on the next NDHost PR.
