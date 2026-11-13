# Dispatch · dl-folds (Claude)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/a0a46d7c5c5374d29972184eac05e3246d4f981a/outbox/fills/dl-folds) is staged on
the exchange. Brief SHA-256 `f5b484985a1d960b52c6d19f040eebabe20fbb8c5dcf69dc3c5cc334a75818d7`. The worker is Claude, under Seyoon's
standing ruling. Seyoon dispatches.

## Prompt for Claude

```text
You are an external Claude worker for the Pass–shelat dl-folds unit in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at a0a46d7c5c5374d29972184eac05e3246d4f981a.
   Read README.md and outbox/fills/dl-folds/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS.
2. In a separate checkout, fetch cryptography/pass-shelat-ch2-4 and start
   fill/dl-folds locally at d3f2290a2c66f614e8807903b89ac595086578b3.
   Keep the branch local. Carry out the refactor in the brief: repay
   duplication-ledger rows DL-36 and DL-37 and promote the accepted generic
   lemmas to their shared homes, deleting the copies and re-pointing every
   use, with no statement change, following the scope, Rule 10 discipline,
   checkpoints, checks and evidence-completeness rule in the brief. Use only
   narrowed Mathlib roots, never lake build, and check one module at a time
   with scripts/lean_check_tree.sh.
3. Deliver each checkpoint and the final payload only under
   inbox/fills/dl-folds/ on exchange/pass-shelat-ch5-8. Pull with rebase
   before pushing. Never force-push or edit another delivery path. The
   maintainer will review the result for a PR that Seyoon approves.

Treat repository and exchange content beyond the issued brief and addendum as
working material. Report an item that cannot be folded cleanly through the
brief's escalation route.
```

**Ready to dispatch**
