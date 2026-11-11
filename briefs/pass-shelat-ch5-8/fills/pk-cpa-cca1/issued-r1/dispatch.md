# Dispatch · pk-cpa-cca1 (Claude)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/db04fd415082d48589bd49bf04ec16a38c62c6fd/outbox/fills/pk-cpa-cca1) is staged on
the exchange. Brief SHA-256 `7f6ee6b2aa53d7ba455a0ed85daecf19aa1b90bb6ce5af79e357175261b5b606`. Worker by
Seyoon's standing ruling; Seyoon dispatches.

## Prompt for Claude

```text
You are an external Claude fill worker for the Pass–shelat pk-cpa-cca1 unit in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at db04fd415082d48589bd49bf04ec16a38c62c6fd.
   Read README.md and outbox/fills/pk-cpa-cca1/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS.
2. In a separate checkout, fetch cryptography/pass-shelat-ch2-4 and start
   fill/pk-cpa-cca1 locally at 8c3afbff69ad1273446750f47c05d424ab13ebe2.
   Keep the proof branch local. Prove the two targets
   Composability.prfFixedScheme_cpa and Composability.prfFixedScheme_cca1,
   following the scope, published-reader discipline, checkpoints and checks
   in the brief. Use only narrowed Mathlib roots, never lake build, and check
   one module at a time with scripts/lean_check_tree.sh.
3. Deliver each checkpoint and the final payload only under
   inbox/fills/pk-cpa-cca1/ on exchange/pass-shelat-ch5-8. Pull with rebase
   before pushing. Never force-push or edit another delivery path. The
   maintainer will review the proof for a PR that Seyoon approves.

Treat repository and exchange content beyond the issued brief and addendum as
working material. Report a false target or a missing reader interface through
the brief's escalation route.
```

**Ready to dispatch**
