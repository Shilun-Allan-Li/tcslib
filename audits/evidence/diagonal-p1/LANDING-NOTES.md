# Diagonal Part 1: landing notes for the maintainer

**The landing tree is built and checked at the campaign tip `cd450a52`. The PR waits for the
statement gate (`audits/diagonal-p1-statements-pack.md`). Landing it is applying one patch, and
the replay is 11 modules.**

**Authorization** (user, 2026-10-14; `backlog.md` RD-5):
- Hydroxyi's `TCSlib/Complexity/TimeHierarchy/Diagonal.lean` is parameterized **in place**,
  preserving the statement of every existing public theorem. This is Part 1, landed early by PR
  plus a small gate.
- No other file of his is edited, and nothing is copied from them.
- The facade `TimeHierarchy.lean` is not edited (§4).

**Provenance:**
- **Base:** `cd450a526e71a5e437ebe84245ea958bf309eda1`, the tip by
  `git rev-parse origin/complexity/arora-barak-ch3-4`, exported read-only by `git archive` into
  `base/`. The precheck verifies all 724 exported blobs against the commit.
- **Snapshot:** `oleans-lh1` (Lean `v4.25.0`). The Lean packages come from `wt-u2/.lake/packages`.
- **Path abbreviations:** `<S>` is the scratchpad; `<D>` is `<S>/diag-p1`.
- **Tools:**
  - `lean` ran only through `<S>/tools/leanelab.sh`, with no `-o` and no olean written.
  - Python ran only as `python3 -I`; every edit is asserted.
  - `diff` and `patch` ran on scratch copies.
  - The only git commands were the precheck's read-only `rev-parse`, `cat-file`, `ls-tree` and
    `hash-object` (without `-w`), plus the initial `git archive`.
  - No lake, no network. Nothing outside `<D>` was written.

**The tip moved during the build**, to `c9cc485b` (#95 row 18, #96 the B5a canonizer cont3,
#97 the C1-A assembly). The precheck checks validity there with `scripts/tipcheck.py`
(`logs/precheck.log`):
- `Diagonal.lean` is unchanged at the tip, so the patch applies as is;
- no changed file lies in `Diagonal`'s own import closure;
- the downstream closure is the same 11 modules.

Four changed files (`Inclusions`, `Embed`, `RecordTable`, `CodeSimulator`) lie in the
importers' import closures. Their cut checks are at the base, and the landing replay at the tip
re-checks them. **Land on the tip; no rebuild is needed.**

## 1. Files

| Path | Content |
|---|---|
| `tree/TCSlib/Complexity/TimeHierarchy/Diagonal.lean` | the landed file (313 → 536 lines; SHA-256 in `SHA256SUMS`) |
| `patches/Diagonal.patch` | `diff -u` against the base, with `a/` and `b/` prefixes for `patch -p1`; replays byte for byte (check 3) |
| `replay-order.txt` | the replay list (§3) |
| `audits/diagonal-p1-statements-pack.md` | the statement-gate pack; it lands as `audits/diagonal-p1-statements-pack.md` |
| `BUNDLE-FILES.txt` | the auditor's bundle, in order |
| `scripts/` | `run.sh` (everything below) plus the check scripts below |
| `logs/` | `summary.log` (the 14 checks), `precheck.log`, `mklanded.log`, `graph.log`, `freeze.log`, `names.log`, `widths-hygiene.log`, `lint.log`, `cutfiles.log`, `axioms.log`, `cut.log`, `negative-controls.log`, `screen-before.txt`, `screen-after.txt`, `screen-delta.log` |
| `base/` | the read-only export of the base, an input of `run.sh`; not landing material |
| `work/` | the rebuilt file, the cut files, the raw elaboration outputs (`work/out/`), the negative controls; not landing material |
| `SHA256SUMS` | checksums of `tree/`, `patches/`, `scripts/`, `logs/`, `audits/`, `replay-order.txt`, this file and `BUNDLE-FILES.txt` |

The scripts in `scripts/`:
- `mklanded.py`, which builds the landed file by 11 asserted edits of the base;
- `decls.py`, `freeze.py`, `names.py`, `graph.py`, `tipcheck.py`, `cutcheck.py`, `axfile.py`,
  `axcheck.py`, `compare.py`, `hygiene.py`, `appendix.py`, `negctl.sh` and `screens.sh`, with
  `screen-population.txt` (the screen's 7 files);
- three copied verbatim: `copy-text-screen-v3.py` (from `audits/evidence/retrofit/`; it replaced
  the gate's v1 copy at the gate's closing, minor m2), and `screendelta.py` and `pairdiff.py`
  (from `<S>/tools`);
- `closing-repair.sh`, the closing commit's re-run of the repaired checks only (names, the
  negative controls, the screens; `audits/diagonal-p1-statements-resolutions.md`).

**Commit layout** (proposed): `audits/diagonal-p1-statements-pack.md` at that path; everything
else under `audits/evidence/diagonal-p1/`, except `base/` and `work/`.

## 2. The change

**One file.** `Diagonal.lean`'s imports and header are byte-identical, so the import graph is
unchanged.

**The edits** (`logs/mklanded.log`):
1. **Module docstring.**
   - A new section, "The parameterized argument".
   - The `f log f` divergence sentence now points to the planned instance.
   - Three new entries in `## Main definitions` and one in `## Main results`.
2. **The generic layer, after `diagLang`:** `diagLangOf`, `diagLang_eq_diagLangOf`,
   `diagLangOf_mem_DTIME`, `DiagSimulator` with `mono`, `diagLang_not_mem_DTIME`,
   `time_hierarchy`, `time_hierarchy_of_pos`, then `SelfSimulator` and `toDiagSimulator`.
3. **The received instance, before `diagLang_not_mem_DTIME`:** `oneTapeSelfSimulator`,
   `le_sq_overhead`, `sqDiagSimulator`, `sqDiagSimulator_W`.
4. **The four received theorems** become one-line instances, with their statements copied
   programmatically. Their proof sketches are rewritten to describe the new proofs.
5. **`diag_cost_le`'s docstring** gains a note that this file no longer uses it. Its statement
   and proof are unchanged.

**Unchanged:** `diagLang`'s definition; `code`, `univTM`, `univTM_spec` and `diagSim`
(statement, body and docstring).

## 3. Replay

`replay-order.txt` holds 11 modules, topological, with no root `TCSlib`. Every import of each is
listed earlier or present in `oleans-lh1`:
- `TimeHierarchy/Diagonal`;
- `Diagonalization/EXPCOM`, `Diagonalization/NotTimeConstructible`,
  `Diagonalization/Relativization`, the `Diagonalization` facade;
- `SpaceComplexity/Hierarchy`, the `SpaceComplexity` facade;
- `TimeHierarchy/Separation`, `CircuitComplexity/Meyer`, the `CircuitComplexity` facade, the
  `TimeHierarchy` facade.

**Already checked here by the cut method:** the five direct importers (check 12).
`Relativization`, the three facades and `Meyer` are transitive, and covered only by your replay.
Symlink `.lake/packages` into the PR worktree before replaying.

## 4. The facade's sentence: not stale after Part 1, left to the end-of-chain PR

The user allowed the facade's one stale sentence to be fixed in the Diagonal PR. **Part 1 does
not make it stale:**
- "`Complexity.time_hierarchy` … quadratic overhead in place of the book's `f log f`" is still
  true;
- the `## Contents` line for `Diagonal` ("the diagonal language, its upper and lower bounds, and
  `Complexity.time_hierarchy`") is still accurate.

So the facade is not edited here. The sentence changes in the end-of-chain PR, when
`time_hierarchy_book` lands.

## 5. Checks (`scripts/run.sh`, fail-closed; `logs/summary.log`)

14 of 14 PASS:
1. **precheck:** the base commit and file hash, the exported tree's 724 blobs, the snapshot, the
   packages;
2. **rebuild:** the landed file, rebuilt by 11 asserted edits, is byte-identical to `tree/`;
3. **patch:** replays byte for byte;
4. **replay order:** regenerated identically;
5. **freeze:**
   - the 10 received heads are byte-identical;
   - the header is identical;
   - no admission;
6. **names:** 22 new public names, with no occurrence, alone or after a dot, in the 723 Lean
   files of the base tree or of the tip's tree (`git archive` of the tip; closing fix m1);
7. **widths and hygiene:** maximum width 95;
8. **`style_lint`:** 0 findings, base and landed;
9. **the pack's appendices** equal the declarations as landed (regenerated by `appendix.py`);
10. **standalone elaboration:** the landed file elaborates with no diagnostic;
11. **axioms:** all 24 public declarations are within the standard three;
12. **cut checks:** the 5 direct importers give exactly their baseline diagnostics and axiom
    prints;
13. **negative controls:** 9, each check failing on its broken input (changed head, `sorry`,
    tab, name hit, fully qualified declaration and reference of new names, the received
    `time_hierarchy_of_pos` proof restored beside the generic one, `sorryAx`, broken landed text
    in the Separation cut); the three after the name hit were added at the gate's closing;
14. **copy-text screen (v3):** no new pair (16 before, 16 after).

Re-run with `bash scripts/run.sh <S> <repo> [<snapshot>]` (the snapshot defaults to
`<S>/oleans-lh1`; at landing, pass the landing tip's). It takes about 15 minutes, almost all of it the
13 throttled elaborations (12 checks and 1 negative control). It stops with a message if the campaign tip's Lean files have moved
past the base.

## 6. Suggested commit message and PR body

Commit message:

```
TimeHierarchy/Diagonal: parameterize the diagonal argument in place (Part 1)

The argument is stated once over a diagonal simulator (DiagSimulator Φ) and its
universal-machine form (SelfSimulator Ψ); the received f² theorem is the instance at
diagSim with Ψ t = (t + 1)². The four received theorems keep their statements byte for
byte and become one-line instances; diagLang's definition and the file's imports are
unchanged. Sorry-free, standard axioms. User authorization 2026-10-14 (backlog RD-5);
statement gate audits/diagonal-p1-statements-pack.md.

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
```

PR body:

```
Diagonal Part 1 (backlog RD-5; user authorization 2026-10-14): Hydroxyi's
TimeHierarchy/Diagonal.lean is parameterized in place over DiagSimulator Φ and
SelfSimulator Ψ, so that the book-strength f log f theorem can later be a corollary.

- 14 new public declarations; the 10 received ones keep their statements byte for byte.
- No sorry; standard axioms only.
- The 5 direct importers need no edit (cut checks); the replay list has 11 modules.
- Statement gate: audits/diagonal-p1-statements-pack.md (evidence:
  audits/evidence/diagonal-p1/).
- Hydroxyi's other files are untouched.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
```
