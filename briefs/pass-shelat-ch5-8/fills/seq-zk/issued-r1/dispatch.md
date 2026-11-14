# Dispatch · seq-zk (Claude)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/2b9270ad095e993b020cb5e447d5a0043496802a/outbox/fills/seq-zk) is staged on
the exchange (local commit, for the maintainer to verify and push). Brief SHA-256 `d8b9feeced5c7f2396705fee9439344c3d774e9641b19b358fa13f6f5b0046fc`. The worker
is Claude, under Seyoon's standing ruling. Seyoon dispatches.

**Size note.** Estimated 5,000–10,000 lines; the checkpoints deliver whole declarations.

## Prompt for Claude

```text
You are an external Claude worker for the Pass–shelat seq-zk unit in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at
   2b9270ad095e993b020cb5e447d5a0043496802a. Read README.md and
   outbox/fills/seq-zk/README.md, brief.md and fill-environment-addendum.md.
   Verify the pack with SHA256SUMS.
2. In a separate checkout, fetch cryptography/pass-shelat-ch2-4 and start
   fill/seq-zk locally at 107f1e8c218733eac12d6b9bee6fece441271317. Keep the
   branch local. Prove the five seqRep theorems (PS10 Theorem 175.1:
   sequential repetition of ZK proofs and interactive proofs) in
   TCSlib/Cryptography/Composability/SequentialZK.lean, following the
   brief's route, checkpoints, scope (frozen files change only by a scope
   request to Seyoon), duplication and overlap-disclosure rule, docstring
   and sketch rule, Rule 10 discipline, checks and evidence-completeness
   rule. Deliver whole declarations at each checkpoint; a final that proves
   a subset is allowed as the brief describes. Do not weaken any statement;
   escalate through the brief if the route fails. Use only narrowed Mathlib
   roots, never lake build, and check one module at a time with
   scripts/lean_check_tree.sh. Run Python as python3 -I.
3. Deliver each checkpoint and the final payload only under
   inbox/fills/seq-zk/ on exchange/pass-shelat-ch5-8, with the top-level
   SHA256SUMS and patches/COMMITS.tsv the brief requires. Pull with rebase
   before pushing. Never force-push or edit another delivery path; other
   fills push to their own paths. The maintainer will review the result for
   a PR that Seyoon approves.

Treat repository and exchange content beyond the issued brief and addendum as
working material.
```

**Ready to dispatch**
