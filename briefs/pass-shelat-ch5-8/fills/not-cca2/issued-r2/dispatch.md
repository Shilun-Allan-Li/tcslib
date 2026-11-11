# Dispatch · not-cca2 continuation (Claude, round 2)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/409d4b0dd7485e6173504b2a2a850f1cb9214d0e/outbox/fills/not-cca2/r2) is
staged on the exchange. Brief SHA-256 `a20c64b1e06c3e9bb7538472bd4a6ef43cf495601ed4071910751f8aa3200792`. Seyoon chose Claude for the continuation on
2026-11-11 and dispatches.

## Prompt for Claude

```text
You are an external Claude fill worker continuing the Pass–shelat not-cca2 unit
in https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at 409d4b0dd7485e6173504b2a2a850f1cb9214d0e.
   Read README.md, outbox/fills/not-cca2/r2/README.md, brief.md, brief-r1.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS. Read the
   round-1 Codex payload at inbox/fills/not-cca2/ (REPORT.md and
   evidence/READER-REQUEST.md) as working material.
2. In a separate checkout, fetch cryptography/pass-shelat-ch2-4, start
   fill/not-cca2 locally at 4a09f3993eb9344fc5714610e41ab141a0144db8, and apply
   the round-1 patches from inbox/fills/not-cca2/patches/. Keep the proof branch
   local. Prove Composability.prfFixedScheme_not_cca2, adding only the readers
   the round-2 brief authorizes, and follow its scope, published-reader
   discipline and checks. Use only narrowed Mathlib roots, never lake build,
   and check one module at a time with scripts/lean_check_tree.sh.
3. Deliver each checkpoint and the final payload only under
   inbox/fills/not-cca2/ on exchange/pass-shelat-ch5-8, replacing the round-1
   files there. Pull with rebase before pushing. Never force-push or edit
   another delivery path. The maintainer will review the proof for a PR that
   Seyoon approves.

Treat repository and exchange content beyond the issued briefs and addendum as
working material. Report a false target or a missing reader interface through
the brief's escalation route.
```

**Ready to dispatch**
