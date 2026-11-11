# Dispatch · public-key CPA bridge (padded-cpa)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/cc07d65f91376b74838332ebe4783bac9a2faef9/outbox/fills/padded-cpa)
is staged on the exchange. Its brief has SHA-256 `d7c5a542bd3ce17a1f930c91ceb9069e8876fd22313f331a46ddec0c4a34cb71`. Seyoon selected Claude on
2026-11-11 and dispatches the fill.

## Prompt for Claude

```text
You are an external Claude fill worker for the Pass–shelat padded-cpa unit
in https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at cc07d65f91376b74838332ebe4783bac9a2faef9.
   Read README.md and outbox/fills/padded-cpa/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS.
2. In a separate checkout, fetch cryptography/pass-shelat-ch2-4 and start
   fill/padded-cpa locally at 4a09f3993eb9344fc5714610e41ab141a0144db8.
   Keep the proof branch local. Prove the one target
   BitPublicKeyScheme.SingleBitSecure.padded_cpa, following the scope,
   published-reader discipline, checkpoints and checks in the brief. Use only
   narrowed Mathlib roots, never lake build, and check one module at a time
   with scripts/lean_check_tree.sh.
3. Deliver each checkpoint and the final payload only under
   inbox/fills/padded-cpa/ on exchange/pass-shelat-ch5-8. Pull with rebase
   before pushing. Never force-push or edit another delivery path. The
   maintainer will review the proof for a PR that Seyoon approves.

Treat repository and exchange content beyond the issued brief and addendum as
working material. Report a false target or a missing reader interface through
the brief's escalation route.
```

**Ready to dispatch**
