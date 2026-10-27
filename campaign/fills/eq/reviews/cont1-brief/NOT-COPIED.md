# Not copied from the review's scratch folder

- `wt/`: the review's worktree, detached at `599497bc` (no tracked change; its `rvprobe/` holds the
  same Lean files as `probe/` here).
- The `.raw` and `.time` outputs are kept in `out/` beside the path-stripped `.out` files.

The Lean files are renamed `*.lean.txt` so that the library build never picks them up. The
elaboration wrapper is kept as `scripts/elab.sh.txt` with the scratch path replaced by `$S`.
