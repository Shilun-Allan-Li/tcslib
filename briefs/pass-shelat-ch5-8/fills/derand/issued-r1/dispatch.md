# Dispatch · derand (Claude)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/2b9270ad095e993b020cb5e447d5a0043496802a/outbox/fills/derand) is staged on
the exchange (local commit, for the maintainer to verify and push). Brief SHA-256 `5cb63bc210a22d34a74b6a6d65ae8f337723239e8a5b9b76757d6845b473b66a`. The worker
is Claude, under Seyoon's standing ruling. Seyoon dispatches.

**Maintainer recommendation: hold.** Step 4 needs a counting enumeration host that does not exist, and *Hosts come first* (policy §1) requires its contract to be statement-gated first. The prompt below is ready if Seyoon dispatches anyway.

## Prompt for Claude

```text
You are an external Claude worker for the Pass–shelat derand unit in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at
   2b9270ad095e993b020cb5e447d5a0043496802a. Read README.md and
   outbox/fills/derand/README.md, brief.md and fill-environment-addendum.md.
   Verify the pack with SHA256SUMS.
2. In a separate checkout, fetch cryptography/pass-shelat-ch2-4 and start
   fill/derand locally at 107f1e8c218733eac12d6b9bee6fece441271317. Keep the
   branch local. Prove Randomness.bpp_subset_dtime_subexp (PS10 Theorem
   180.1: a secure PRG puts BPP in DTIME(2^{n^eps})) in
   TCSlib/Cryptography/Randomness/Derandomization.lean, following the
   brief's route, checkpoints, scope (frozen files change only by a scope
   request to Seyoon), duplication and overlap-disclosure rule, docstring
   and sketch rule, Rule 10 discipline, checks and evidence-completeness
   rule. Your first checkpoint is the contract of the counting enumeration
   host, sent as a scope request (the brief, checkpoint 1); prove nothing
   that depends on it before Seyoon answers. Do not weaken any statement;
   escalate through the brief if the route fails. Use only narrowed Mathlib
   roots, never lake build, and check one module at a time with
   scripts/lean_check_tree.sh. Run Python as python3 -I.
3. Deliver each checkpoint and the final payload only under
   inbox/fills/derand/ on exchange/pass-shelat-ch5-8, with the top-level
   SHA256SUMS and patches/COMMITS.tsv the brief requires. Pull with rebase
   before pushing. Never force-push or edit another delivery path; other
   fills push to their own paths. The maintainer will review the result for
   a PR that Seyoon approves.

Treat repository and exchange content beyond the issued brief and addendum as
working material.
```

**Ready to dispatch**
