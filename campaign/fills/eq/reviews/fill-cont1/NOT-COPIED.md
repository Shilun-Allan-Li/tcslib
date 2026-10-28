# What in this folder should not be copied into the records

Copy `REVIEW.md`, `NOT-COPIED.md`, `scripts/` (without `scripts/lintroot/`), `out/` (without the
items below) and `probe/` (without the items below). The rest is large, reproducible, or not the
review's own work.

| Path | Why not copied | How to reproduce |
|---|---|---|
| `delivery/` | The extraction of `exchange/inbox/fill-eq-query-cont1.zip` (100 files, 3.4 MB). It is the worker's delivery, not review output, and the zip itself is the record (SHA-256 `aa8e3ab1…1125e`, out/00-zip-sha.txt) | `python3 -I scripts/zipextract.py <zip> delivery` |
| `wt-head/` | The review's worktree at `e952bc50`, with a `.lake/packages` symlink. It is removed (and its registration with it) at the end of the review | `git worktree add --detach <dir> e952bc50924ae7cea3364298087148fe1540a534` |
| `scripts/lintroot/` | A scratch copy of `scripts/campaign_style_lint.py` and of the `Diagonalization` subtree, which `scripts/lint_run.sh` rebuilds on every run | `bash scripts/lint_run.sh <tree root> [<owned file copy>]` |
| `out/aux/` | Working copies: `head.lean` and `base.lean` (the owned file at the head and the base), the two `imports-*.json` maps, the tactic-argument rows (`tacargs.tsv`, `tacids*.txt`), the ALLDEFS list, the reached-definition list, the probe's name list, the root lists and the pair lists for `tiles_run.sh`. All are reproducible from git and the scripts. The ALLDEFS list is also in `out/13-audit-head.out` (lines 3786–4060) | `git show <rev>:<path>`; `devtools/seyoon/imports.py`; `scripts/tacargs2.py` |
| `out/aux-fp/` | This host's `git format-patch` of the series, compared with the delivered patches in out/01-integrity.txt (they differ only in the trailing git-version line) | `git format-patch -o <dir> 43fe918f..e952bc50` |
| `out/16z-superseded-*` | The first seal run (`scripts/mkseal2.py`, `probe/seal/Seal_*.lean`). Its controls raised errors, and the CLI's cap of 100 errors hid most of their results. It is superseded by `out/16-seal3-*` and `out/16-seal-summary.txt`. Its body result (0 errors) agrees | — |
| `probe/seal/Seal_sealed.lean`, `probe/seal/Seal_unsealed.lean` | The superseded first seal's sources (1.2 MB with the others) | `python3 -I scripts/mkseal2.py …` |
| `probe/seal/Seal3_*.lean`, `probe/land/Seal3_*.lean`, `probe/AuditHead.lean`, `probe/AuditBase.lean`, `probe/KindsHead.lean`, `probe/ReachHead.lean`, `probe/land/AuditLand.lean` | Generated copies of the 5,400-line module with appended audit commands (about 0.3 MB each). Each is reproducible exactly by its generator from `out/aux/head.lean` (or the landed file) and the tails in `scripts/` | `scripts/mkseal3.py`, `scripts/mkaudit2.py`, `scripts/mkkinds.py`; the reach probe is the head plus `scripts/reach_tail.lean.txt` |
| `probe/QyImportProbe.worker.lean` | A byte-identical copy of the delivery's `probe/QyImportProbe.lean`, made so that it could be elaborated outside the extraction (SHA-256s in out/19-probe-scan.txt) | `cp` |
| `out/13-audit-head.out`, `out/28-land-audit.out` (about 0.2 MB each) | Large but **worth keeping**: `out/13a-walk-summary.txt` summarizes the first, but the full walk lists (964 core/Mathlib constants, 1,324 locals) are evidence for F7 and rule 10. Copy them unless the records have a size limit | — |

Keep `probe/land/NTimeDiagonalizer.lean` (the tested landed file, SHA-256 `2e29f0d8…5f1e`) and
`out/25-landing-edits.diff`: the landing PR applies that diff.
