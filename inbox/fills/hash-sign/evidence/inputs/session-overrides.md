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
