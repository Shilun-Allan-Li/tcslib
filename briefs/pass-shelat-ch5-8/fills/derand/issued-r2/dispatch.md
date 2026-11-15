# Dispatch · derand, issued-r2 (Claude)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/fd1ba58e97fb8168cc55757883392845c6289da3/outbox/fills/derand-r2) is staged on
the exchange (local commit, for the maintainer to verify and push). Brief SHA-256 `5375acb095037660b7ec54c6c51fd00ac569f7ea8d2cfff6f3935fe40cf21a13`. The worker
is Claude, under Seyoon's standing ruling. Seyoon dispatches.

**Reissue.** This replaces the held `issued-r1` pack (`outbox/fills/derand/`). The host H17 is merged (#312),
so the old first checkpoint (the host contract as a scope request) is gone. Seyoon pre-approved three
additions to frozen shared files (2026-11-15). Their downstream modules outside the 377-module order are
rebuilt by the maintainer at review.

## Prompt for Claude

```text
You are an external Claude worker for the Pass–shelat derand unit in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at
   fd1ba58e97fb8168cc55757883392845c6289da3. Read README.md and
   outbox/fills/derand-r2/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS. This issue
   (r2) replaces outbox/fills/derand/ (r1).
2. In a separate checkout, fetch cryptography/pass-shelat-ch2-4 and start
   fill/derand locally at 01de2d8baed9113e4a099e13c5d50c81e6dbc66f. Keep the
   branch local. Prove Complexity.exists_seedMajorityTM and
   Complexity.seedMajority_mem_DTIME (host H17, the seed-majority machine
   contract and its DTIME corollary) in
   TCSlib/Complexity/Randomized/SeedMajority.lean, and
   Randomness.bpp_subset_dtime_subexp (PS10 Theorem 180.1: a secure PRG puts
   BPP in DTIME(2^{n^eps})) in
   TCSlib/Cryptography/Randomness/Derandomization.lean. Follow the brief's
   route, checkpoints and proved-modulo rule; its scope, with exactly the
   three pre-approved additions (computesFunInTime_find in
   Randomized/Build/IterateFind.lean, mem_DTIME_iff and
   FinTM.decidesInTime_iff in ClassP/DTIME.lean) and any other frozen-file
   change only by a scope request to Seyoon; the frozen-statement rule and
   its header check; the duplication and overlap-disclosure rule; the
   docstring and sketch rule; Rule 10 discipline; and the checks and
   evidence-completeness rule. Your first checkpoint is the harvest, the two
   readers and the corollary proved from the contract. Do not weaken any
   statement; escalate through the brief if the route fails. Use only
   narrowed Mathlib roots, never lake build, and check one module at a time
   with scripts/lean_check_tree.sh. Run Python as python3 -I.
3. Deliver each checkpoint and the final payload only under
   inbox/fills/derand/ on exchange/pass-shelat-ch5-8, with the top-level
   SHA256SUMS and patches/COMMITS.tsv the brief requires; commit with
   commit.gpgsign=false, or record the signing in COMMITS.tsv. Pull with
   rebase before pushing. Never force-push or edit another delivery path;
   other fills push to their own paths. The maintainer will review the
   result for a PR that Seyoon approves.

Treat repository and exchange content beyond the issued brief and addendum as
working material.
```

**Ready to dispatch**
