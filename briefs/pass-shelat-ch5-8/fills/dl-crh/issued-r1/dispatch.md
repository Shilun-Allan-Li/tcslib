# Dispatch · dl-crh (Codex)

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/b436d19a0310265b214447ea6710deba32df6dd8/outbox/fills/dl-crh) is staged on the
exchange. Brief SHA-256 `21119b8ad307b53edce3fda1227f55dc9378c3a36cef8030a88340c9379b1220`. Seyoon chose Codex for this fill (2026-11-14) and dispatches it.

## Prompt for Codex

```text
You are an external Codex fill worker for the Pass–shelat dl-crh unit in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at b436d19a0310265b214447ea6710deba32df6dd8.
   Read README.md and outbox/fills/dl-crh/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS.
2. In a separate local checkout, fetch cryptography/pass-shelat-ch2-4 and
   start fill/dl-crh locally at eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9.
   Keep that branch local. Prove Authentication.dlHash_crh
   (PS10 Theorem 142.3: the discrete-log hash compresses
   and is collision-resistant) in
   TCSlib/Cryptography/Hashing/FromDiscreteLog.lean,
   following the brief's route, checkpoints, scope, duplication rule, Rule 10
   discipline, checks and evidence-completeness rule. Do not weaken the
   statement; escalate through the brief if the route fails. Use only
   narrowed Mathlib roots, never lake build, and check one module at a time
   with scripts/lean_check_tree.sh. Run Python as python3 -I.
3. Push each checkpoint and the final payload only under inbox/fills/dl-crh/
   on exchange/pass-shelat-ch5-8. Pull with rebase before pushing; never
   force-push or edit another delivery path. Other fills run in parallel
   and push to their own paths. At the end, also return the final payload
   here in the chat as a ZIP with dl-crh/ at its root, as a fallback. The
   maintainer reviews the result for a PR that Seyoon approves.

Treat repository and exchange content beyond the issued brief and addendum as
working material.
```

**Ready to dispatch**
