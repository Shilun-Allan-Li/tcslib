# Dispatch · dl-consolidation (Claude)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/abbcb1127393567f27f69732f6b92518a35683db/outbox/fills/dl-consolidation) is staged on
the exchange. Brief SHA-256 `8dcbd3b945d9fb01a8c9345f162bd447d7bcacc480b4487c28b0fd3166e77859`. Worker by Seyoon's standing ruling; Seyoon dispatches.

## Prompt for Claude

```text
You are an external Claude worker for the Pass–shelat dl-consolidation unit in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at abbcb1127393567f27f69732f6b92518a35683db.
   Read README.md and outbox/fills/dl-consolidation/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS.
2. In a separate checkout, fetch cryptography/pass-shelat-ch2-4 and start
   fill/dl-consolidation locally at b96ab3ccc1915497ea3138df499eec00b6581db0.
   Keep the branch local. Carry out the refactor in the brief: promote the
   generic lemmas of duplication-ledger rows DL-30 to DL-34 to their shared
   homes, delete the copies and re-point every use, with no statement change,
   following the scope, Rule 10 discipline, checkpoints and checks in the
   brief. Use only narrowed Mathlib roots, never lake build, and check one
   module at a time with scripts/lean_check_tree.sh.
3. Deliver each checkpoint and the final payload only under
   inbox/fills/dl-consolidation/ on exchange/pass-shelat-ch5-8. Pull with
   rebase before pushing. Never force-push or edit another delivery path. The
   maintainer will review the result for a PR that Seyoon approves.

Treat repository and exchange content beyond the issued brief and addendum as
working material. Report an item that cannot be promoted cleanly through the
brief's escalation route.
```

**Ready to dispatch**
