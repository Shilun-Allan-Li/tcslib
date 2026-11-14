# Direct user instruction, 2026-11-13 PST

At about 2026-11-14 05:42 UTC, after the worker reported other active Lean jobs,
the user replied:

> Override this; for now, you can run as many Lean checks as you want. After 20 minutes; let's say <= 3 concurrent Lean jobs at a time.

This overrides the addendum's host-wide single-Lean-process restriction. From
2026-11-14 06:02 UTC, the worker caps its concurrent Lean jobs at three. Checks
still use one module per `scripts/lean_check_tree.sh` invocation. The bootstrap
itself is sequential and uses this checkout's own olean tree.

The user's original request explicitly authorizes exchange pushes to
`inbox/fills/hash-sign/`, superseding the older generic exchange README's
chat-only transport rule for external Codex workers.

A later user-authorized coordination note clarified that the
three-process cap applies across the host, including other projects, and asked
to leave one slot for dl-crh's bootstrap. The launcher now counts existing
native Lean processes and conservatively uses one worker slot while two other
projects are active. Existing stale diagnostic checks were cancelled for their
identified proof-code corrections; unrelated jobs were not interrupted.

The user subsequently explicitly authorized the prepared eight-import patch to
`TCSlib/Cryptography/Authentication.lean`, overriding the brief's freeze for
these eight import additions only. The question identified the exact prepared
patch and the eight parent-facade lint failures; the user answered:

> Authorize the eight imports

A final user-authorized Lamport coordination note clarified that the shared
three-process count includes bare `lean` executable names as well as full
toolchain paths, and requested capacity for one Lamport check. The launcher's
`Path(comm).name == 'lean'` check already covers both forms. All hash-sign native
checks had closed before this note; no further hash-sign Lean jobs were launched.
