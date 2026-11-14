# Dispatch · cca2-ett (Claude)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/3f8f3744b8507597074a8480193034e806e0764c/outbox/fills/cca2-ett) is staged on
the exchange. Brief SHA-256 `ebffc5220138b4ae0a02c938284add41d37373886d3c8f5f83dbb24f9b60ccf0`. The worker is Claude, under Seyoon's
standing ruling. Seyoon dispatches.

## Prompt for Claude

```text
You are an external Claude worker for the Pass–shelat cca2-ett unit in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at 3f8f3744b8507597074a8480193034e806e0764c.
   Read README.md and outbox/fills/cca2-ett/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS.
2. In a separate checkout, fetch cryptography/pass-shelat-ch2-4 and start
   fill/cca2-ett locally at eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9.
   Keep the branch local. Prove Composability.ccaScheme_cca2 (PS10 Theorem
   170.4: encrypt-then-tag is CCA2-secure from a PRF) in
   TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag.lean, following
   the brief's route, checkpoints, scope, duplication rule, Rule 10
   discipline, checks and evidence-completeness rule. Do not weaken the
   statement; escalate through the brief if the route fails. Use only
   narrowed Mathlib roots, never lake build, and check one module at a time
   with scripts/lean_check_tree.sh.
3. Deliver each checkpoint and the final payload only under
   inbox/fills/cca2-ett/ on exchange/pass-shelat-ch5-8. Pull with rebase
   before pushing. Never force-push or edit another delivery path. The
   maintainer will review the result for a PR that Seyoon approves.

Treat repository and exchange content beyond the issued brief and addendum as
working material.
```

**Ready to dispatch**
