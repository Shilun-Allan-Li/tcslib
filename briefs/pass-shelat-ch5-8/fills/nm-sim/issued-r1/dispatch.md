# Dispatch · nm-sim (Claude)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/6f1e13ae6938b08e0b7439e789aea4dd9f8afe33/outbox/fills/nm-sim) is staged on the
exchange. Brief SHA-256 `b2fee9cbf1ac9714c50fbf7770471f8ef62f8989a0e0ec7cbd0c980d8128c318`. Worker by Seyoon's standing ruling; Seyoon dispatches.

## Prompt for Claude

```text
You are an external Claude fill worker for the Pass–shelat nm-sim unit in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at 6f1e13ae6938b08e0b7439e789aea4dd9f8afe33.
   Read README.md and outbox/fills/nm-sim/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS.
2. In a separate checkout, fetch cryptography/pass-shelat-ch2-4 and start
   fill/nm-sim locally at 262d6e9ae526c82eb68fe5a6169156bd1504e6d8.
   Keep the proof branch local. Prove the targets
   FixedLengthPKScheme.nmSecure_of_simNMSecure and
   FixedLengthPKScheme.simNMSecure_of_nmSecure_cpa (PS10 Theorem 174.8, in the
   SIM-NME' form of PSV07), following the scope, published-reader discipline,
   duplication rule, checkpoints and checks in the brief. Use only narrowed
   Mathlib roots, never lake build, and check one module at a time with
   scripts/lean_check_tree.sh.
3. Deliver each checkpoint and the final payload only under
   inbox/fills/nm-sim/ on exchange/pass-shelat-ch5-8. Pull with rebase
   before pushing. Never force-push or edit another delivery path. The
   maintainer will review the proof for a PR that Seyoon approves.

Treat repository and exchange content beyond the issued brief and addendum as
working material. Report a false target or a missing reader interface through
the brief's escalation route.
```

**Ready to dispatch**
