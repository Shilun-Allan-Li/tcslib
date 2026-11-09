# Parallel local-only coordinator — unexecuted

The explicit user reply “you're free to run in parallel” supersedes the global host barrier. Exact canonical ruling3f0730086b324c2773bcf5239eadfdb86f7c026bbbb5bf2f344283372fa7f9fa is copied verbatim here and checked against the original. Its six existing simp approvals introduce no code/flag/Rule10 change in this tool.

Run only after Root/peer review, from the integration checkout:

```
python3 -I .lake/ps-maintainer/gate06-combined-20261108/native-runtime-parallel-r1/continue_native.py local
```

This350-line successor preserves base921959c0 unchanged. CLI is local-only and accepts only completed BOOT RESULTe1fa6d0282b1e683f971a3e4088ec5e36228615b279634745e1ff4ea1ace8cca and manifestf26e727bea498ad3287c5d928ccb09dce11b3e36bec1574b13f10d36880bc70c, with original bootstrap coordinator9219 rather than this new self. Output remains the absent `native-local-resume-r1/`.

The new in-memory native-process filter reads actual `ps pid/pgid/comm/args`, matches the own absolute `oleans-r1` path at an argv path boundary, and returns only PID/PGID/executable. Other trees do not trigger waiting or collision. The pinned checker emits `-o "$OL/$rel.olean"`, so its active Lean command carries the absolute own-tree output. This lexical filter does not enumerate process environments or resolve arbitrary aliases. The own-tree lease, own-child PGID cleanup, global4GiB resource floor, source/object/prerequisite/marker checks and failure retention stay intact. Initial/between-success idle is0.5seconds for the own tree; any same-tree activity retains the longer30-second guard. No other-host wait is imposed.

Every call, lease and final result records the exact execution scope, user approval hash/quote and coordinator code hash. There is no standalone scope digest; the metadata, pinned approval and code hash bind it. Historical R1/BOOT records retain their original strict-host policy. Final counts still distinguish warm437, fresh638, final1075 and all old/new attempts; the prior fail-closed terminal-call reporting limitation remains separately documented by peer review.

`from-9219.diff` records the narrow delta. Unchanged methods were compared structurally; seven independent argv-boundary fixtures passed. Neither coordinator nor engine was imported/executed by the author. No native/tree/source/config/prep/old-evidence changes were performed. Local native and Rule10 outcomes remain unestablished.
