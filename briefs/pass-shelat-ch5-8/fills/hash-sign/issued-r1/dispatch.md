# Dispatch · hash-sign (Codex)

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/b436d19a0310265b214447ea6710deba32df6dd8/outbox/fills/hash-sign) is staged on the
exchange. Brief SHA-256 `d4ddbdb335cf9df5382c1141769c730277301ce2618e017ad17f9ff94eaed211`. Seyoon chose Codex for this fill (2026-11-14) and dispatches it.

## Prompt for Codex

```text
You are an external Codex fill worker for the Pass–shelat hash-sign unit in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at b436d19a0310265b214447ea6710deba32df6dd8.
   Read README.md and outbox/fills/hash-sign/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS.
2. In a separate local checkout, fetch cryptography/pass-shelat-ch2-4 and
   start fill/hash-sign locally at eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9.
   Keep that branch local. Prove Authentication.hashAndSign_oneTimeSecure
   (PS10 Theorem 144.1: hash-and-sign is
   one-time secure) in
   TCSlib/Cryptography/Authentication/Signatures/HashAndSign.lean,
   following the brief's route, checkpoints, scope, duplication rule, Rule 10
   discipline, checks and evidence-completeness rule. Do not weaken the
   statement; escalate through the brief if the route fails. Use only
   narrowed Mathlib roots, never lake build, and check one module at a time
   with scripts/lean_check_tree.sh. Run Python as python3 -I.
3. Push each checkpoint and the final payload only under inbox/fills/hash-sign/
   on exchange/pass-shelat-ch5-8. Pull with rebase before pushing; never
   force-push or edit another delivery path. Other fills run in parallel
   and push to their own paths. At the end, also return the final payload
   here in the chat as a ZIP with hash-sign/ at its root, as a fallback. The
   maintainer reviews the result for a PR that Seyoon approves.

Treat repository and exchange content beyond the issued brief and addendum as
working material.
```

**Ready to dispatch**
