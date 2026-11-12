# Dispatch · nm-cca2 (Claude)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/3f6d6783a1e4527e5287c63a9f1a0075fb6d0369/outbox/fills/nm-cca2) is staged on the
exchange. Brief SHA-256 `1a6aed038a3e1218fffc88163f967e801b79b3c2c27bd7935ea8fd83a19c35fb`. Worker by Seyoon's standing ruling; Seyoon dispatches.

## Prompt for Claude

```text
You are an external Claude fill worker for the Pass–shelat nm-cca2 unit in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at 3f6d6783a1e4527e5287c63a9f1a0075fb6d0369.
   Read README.md and outbox/fills/nm-cca2/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS.
2. In a separate checkout, fetch cryptography/pass-shelat-ch2-4 and start
   fill/nm-cca2 locally at b96ab3ccc1915497ea3138df499eec00b6581db0.
   Keep the proof branch local. Prove the target
   FixedLengthPKScheme.indSecure_cca2_iff_nmSecure_cca2 (PS10 Theorem 175.9),
   following the scope, published-reader discipline, duplication rule,
   checkpoints and checks in the brief. Use only narrowed Mathlib roots, never
   lake build, and check one module at a time with scripts/lean_check_tree.sh.
3. Deliver each checkpoint and the final payload only under
   inbox/fills/nm-cca2/ on exchange/pass-shelat-ch5-8. Pull with rebase
   before pushing. Never force-push or edit another delivery path. The
   maintainer will review the proof for a PR that Seyoon approves.

Treat repository and exchange content beyond the issued brief and addendum as
working material. Report a false target or a missing reader interface through
the brief's escalation route.
```

**Ready to dispatch**
