# What in this folder should not be copied into the records

Copy these:
- `REVIEW.md` and `NOT-COPIED.md`;
- `scripts/`;
- `out/`, without the items below;
- `probe/`, without the items below;
- `land/`.

The rest is large, reproducible, or not the review's own work.

| Path | Why not copied | How to reproduce |
|---|---|---|
| `wt-head/`, `wt-base/`, `wt-land/` | The review's worktrees: the delivery head `7b1b9353`, the base `c8b07114`, and the head with the landed file copied in. Each has a `.lake/packages` symlink. All three are removed, registration included, at the end of the review | `git worktree add --detach <dir> <rev>`; for `wt-land`, `cp land/NTimeDiagonalizer.lean.txt <dir>/TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean` |
| `oleans-clone/`, `oleans-land/`, `oleans-tipclone/` | Copy-on-write clones of `oleans-leqc3` (×2) and `oleans-lsm5`, with the head's or the landed file's oleans compiled in. All are deleted at the end | `cp -cR $S/oleans-leqc3 <dir>`, then `scripts/compile-head.sh`, `compile-land.sh`, `compile-tip.sh` |
| `screen-head/` | The frozen copy (4 MB) of the brief's 38-file population at the head, the screen's input | `scripts/freeze-population.sh` |
| `probe/seal/`, `probe/seal-land/` | Generated sealed and unsealed copies (8,600 lines, about 0.5 MB each) of the head file and the landed file, with the seal and control blocks | `python3 -I scripts/mkseal.py <file> out/16-sealgen.out <dir>` |
| `out/07-added.txt` | The diff's added lines (176 KB), the input of `hygiene.py`, `tacargs.py` and the forbidden-name count | `git diff -U0 <base> <head> -- <owned file> \| grep '^+' \| grep -v '^+++' \| sed 's/^+//'` |
| `out/aux-brief-base.md` | The brief as committed at the base, the input of `scripts/dispatch.sh` | `git show <base>:campaign/fills/eq/briefs/eq-fill-diagonalizer.md` |
| `out/13-tacargs.json`, `out/13-tacargs-heads.txt`, `out/13-heads-classified.txt`, `out/13-ownnames.txt` | Working rows of the rule-10 inspection. `out/14b-inspection-table.txt` summarizes them | `scripts/tacargs.py`, then the classification in `scripts/` |
| `out/18-hits-raw.txt`, `out/18-dzprefix-raw.txt`, `out/18-refs.txt`, `out/18-patterns.txt` | The rule-11 grep's raw files. The hit files are empty; `out/18-rule11.txt` is the record | `scripts/rule11.sh` |
| `out/superseded/` | The first seal run, whose control code did not parse (its body result, 0 errors, agrees); the landed file's first test round (E1–E6, before E7's docstring text); and the polluted first rule-11 grep | — |
| `out/11-audit-head.out`, `out/11b-audit-base.out`, `out/33-land-audit.out` (about 0.2–0.3 MB each), `out/16-sealgen.out` (0.4 MB) | Large but **worth keeping**. They carry: the per-constant axiom lines and hashes behind the kernel-level freeze (out/11d) and the land comparison (out/33b); the public-constant lists behind F10; and the generator's seal, erasure and skip lists. Copy them unless the records have a size limit | — |

Keep `land/NTimeDiagonalizer.lean.txt` (the tested landed file, git blob
`fc65a848032abfd935b8d847453e047eabb71d24`) and `out/30-landing-edits.diff`: the landing PR applies
that diff, and `scripts/landing_edits.py` reproduces it from the head with every replacement
asserted.
