# Dispatch · sc-compose (Claude)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/2b9270ad095e993b020cb5e447d5a0043496802a/outbox/fills/sc-compose) is staged on
the exchange (local commit, for the maintainer to verify and push). Brief SHA-256 `f3fe74c1d1e94ccd8b262d281daaa55d066aa874970e9d51d0e18151e1a9843a`. The worker
is Claude, under Seyoon's standing ruling. Seyoon dispatches.

## Prompt for Claude

```text
You are an external Claude worker for the Pass–shelat sc-compose unit in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at
   2b9270ad095e993b020cb5e447d5a0043496802a. Read README.md and
   outbox/fills/sc-compose/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS.
2. In a separate checkout, fetch cryptography/pass-shelat-ch2-4 and start
   fill/sc-compose locally at 107f1e8c218733eac12d6b9bee6fece441271317. Keep
   the branch local. Prove composeP_efficient, composeV_efficient and
   hbcSecure_compose (Gol04 Theorem 7.3.3: the semi-honest composition
   theorem) in TCSlib/Cryptography/SecureComputation/ComposeSecurity.lean,
   following the brief's route, checkpoints, scope (frozen files change only
   by a scope request to Seyoon), duplication and overlap-disclosure rule,
   docstring and sketch rule, Rule 10 discipline, checks and
   evidence-completeness rule. Do not build an l-output PRF (Seyoon:
   separate job prf-long); escalate if you need one. Do not weaken any
   statement; escalate through the brief if the route fails. Use only
   narrowed Mathlib roots, never lake build, and check one module at a time
   with scripts/lean_check_tree.sh. Run Python as python3 -I.
3. Deliver each checkpoint and the final payload only under
   inbox/fills/sc-compose/ on exchange/pass-shelat-ch5-8, with the top-level
   SHA256SUMS and patches/COMMITS.tsv the brief requires. Pull with rebase
   before pushing. Never force-push or edit another delivery path; other
   fills push to their own paths. The maintainer will review the result for
   a PR that Seyoon approves.

Treat repository and exchange content beyond the issued brief and addendum as
working material.
```

**Ready to dispatch**
