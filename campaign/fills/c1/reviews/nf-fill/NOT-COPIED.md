# What in this folder should not be copied into the records

**What to copy:**
- `REVIEW.md` and `NOT-COPIED.md`;
- `scripts/` (without `scripts/lintroot/`, which `lint_run.sh` deletes after each run anyway);
- `out/`, without the items below;
- `land/NDNormalForm.lean`;
- the probe sources listed as kept below.

Copy every `.lean` file under `probe/` and `land/` with `.txt` appended (`*.lean.txt`, the
records' convention), so that no tool treats it as a module. The `out/` files name the `.lean`
paths that existed when they ran.

| Path | Why not copied | How to reproduce |
|---|---|---|
| `wt-head/` | The review's worktree at `4af97d46`, with a `.lake/packages` symlink. Already removed at the end of the review (the link unlinked, then `git worktree remove --force`); it is no longer in the folder | `git worktree add --detach <dir> 4af97d4679f8024ea5bcbf11c04d1e4e5e0373cb` |
| `src/` | `base.lean`, `head.lean` and `cp1.lean` are the owned file at `951251f6`, `4af97d46` and `2dc36b95` | `git show <rev>:TCSlib/Complexity/ClassNP/NDNormalForm.lean` |
| `out/aux-fp/` | This host's `git format-patch` of the series. out/01 compares it with the delivered patches, which differ only in the git-version trailer | `git format-patch -o <dir> 951251f6..4af97d46` |
| `out/aux-imports-head.json`, `out/aux-imports-tip.json` (180 KB each) | Import maps of the head tree and the records tip; out/15 holds the closures computed from them | `python3 -I scripts/imports.py <tree> <out.json>` |
| `out/aux-locals.txt`, `out/aux-land-ids.txt`, `out/aux-land-tacargs.tsv` | Working lists: the module's constants, extracted from out/05 (and summarized in out/02d), and the landed file's tactic arguments, used to build its audit probe | `scripts/tacargs.py`; the `sed` in out/02d's header |
| `probe/NFSeal_sealed.lean`, `probe/NFSeal_unsealed.lean`, `probe/land/NFSeal_*.lean` | Generated copies of the module with the 223-definition seal block and 450 controls (about 1,000 lines each). Out/06 and out/20 hold their outputs | `python3 -I scripts/mkseal.py <owned file> out/05c-alldefs.txt <dir>` |
| `probe/NFAudit.lean`, `probe/NFLandAudit.lean`, `probe/NFUsers.lean`, `probe/NFSimpQ.lean`, `probe/NFSpot.lean`, `probe/NFInst.lean`, `probe/NFRouteShape.lean`, `probe/NDNormalForm_base.lean` | Generated: the module (head, landed or base) plus a tail from `scripts/`. NFSimpQ is the head with four `simp` calls turned into `simp?` | `scripts/mkaudit.py` with `scripts/audit_tail.lean.txt`, `kinds_tail.lean.txt` and `sorry_tail.lean.txt` (NFAudit, NFLandAudit); `scripts/append_tail.py` with `spot_tail`, `inst_tail` or `route_tail` (NFSpot, NFInst, NFRouteShape; checked to reproduce byte for byte); `scripts/mksimpq.py` (NFSimpQ: four asserted replacements at head lines 137, 145, 153 and 580); NFUsers is the head with `import Lean`, `audit_tail` and `users_tail` appended, then the `#nf_users` lines that out/05b echoes; `cp src/base.lean` (the base copy) |
| `probe/NFImportProbe-brief.lean`, `probe/NFImportExtended2-worker.lean` | Byte-identical copies of `campaign/fills/c1/inputs/c1-fill-nf/NFImportProbe.lean.txt` and of the delivery's `probes/NFImportExtended2.lean`, made in order to elaborate them | `cp` |

**Keep:**
- `probe/NFExact.lean`: written by hand, the `exact?` probe of out/10;
- `land/NDNormalForm.lean`: the tested landed file, git blob `e6432b1e`, SHA-256 `b3fa9998…1279`;
- `out/19-landing-edits.diff`: the landing PR applies it;
- `scripts/landing_edits.py`: it regenerates the landed file from the head, with every edit
  asserted.

**Large but worth keeping:** `out/05-audit.out` and `out/20b-land-audit.out` (65 KB each). They
hold the full walk (80 TCSlib and 388 core/Mathlib constants), the ALLDEFS list behind the seal,
the kinds table and every axiom print.
