# Dispatch · adaptive-cpa (Claude)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/f4737d78eade83eca52dc33d5e370bbe85313fee/outbox/fills/adaptive-cpa) is staged on
the exchange. Brief SHA-256 `4ddcbe4a35a4f86b1110f681f6ec789fd2de9eb845bb6d96bcfb12d99e49d759`. Seyoon selected Claude on 2026-11-11 and dispatches.

## Prompt for Claude

```text
You are an external Claude fill worker for the Pass–shelat adaptive-cpa unit in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at f4737d78eade83eca52dc33d5e370bbe85313fee.
   Read README.md and outbox/fills/adaptive-cpa/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS.
2. In a separate checkout, fetch cryptography/pass-shelat-ch2-4 and start
   fill/adaptive-cpa locally at 4a9b2c91eb2f89c4fb624339d5b4ba9cfd35ac27.
   Keep the proof branch local. Prove the one target
   Composability.FixedLengthPKScheme.INDSecure.adaptive_cpa, following the scope,
   published-reader discipline, checkpoints and checks in the brief. Use only
   narrowed Mathlib roots, never lake build, and check one module at a time
   with scripts/lean_check_tree.sh.
3. Deliver each checkpoint and the final payload only under
   inbox/fills/adaptive-cpa/ on exchange/pass-shelat-ch5-8. Pull with rebase
   before pushing. Never force-push or edit another delivery path. The
   maintainer will review the proof for a PR that Seyoon approves.

Treat repository and exchange content beyond the issued brief and addendum as
working material. Report a false target or a missing reader interface through
the brief's escalation route.
```

**Ready to dispatch**
