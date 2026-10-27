# Not copied from the review's scratch folder

- `wt/`: the review's worktree, detached at `9d0af8cb` (no tracked change; its `rvprobe/` holds the
  same Lean files as `probe/` here).
- `lintroot/`: the scratch tree the review linted (the filled file in place); its results are
  `out/lint-base.txt` and `out/lint-filled.txt`.
- The `.raw` and `.time` outputs are kept in `out/` beside the path-stripped `.out` files.

The Lean probes are renamed `*.lean.txt` so that the library build never picks them up. The
pre-ship runner is kept as `scripts/run-preship.sh.txt` with the scratch path replaced by `$S`.
