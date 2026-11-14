# Dispatch · ext-nosrc (Codex)

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/b436d19a0310265b214447ea6710deba32df6dd8/outbox/fills/ext-nosrc) is staged on the
exchange. Brief SHA-256 `30a0e02d3d5973b41c937fb13b044b49722290ad837fc99ed45bbc7c159dde52`. Seyoon chose Codex for this fill (2026-11-14) and dispatches it.

## Prompt for Codex

```text
You are an external Codex fill worker for the Pass–shelat ext-nosrc unit in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at b436d19a0310265b214447ea6710deba32df6dd8.
   Read README.md and outbox/fills/ext-nosrc/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS.
2. In a separate local checkout, fetch cryptography/pass-shelat-ch2-4 and
   start fill/ext-nosrc locally at eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9.
   Keep that branch local. Prove Randomness.not_isExtractor_effSources
   (PS10 Theorem 183.6: no efficient one-bit
   1/4-extractor for efficiently samplable (n-2)-sources) in
   TCSlib/Cryptography/Randomness/Extraction.lean,
   following the brief's route, checkpoints, scope, duplication rule, Rule 10
   discipline, checks and evidence-completeness rule. Do not weaken the
   statement; escalate through the brief if the route fails. Use only
   narrowed Mathlib roots, never lake build, and check one module at a time
   with scripts/lean_check_tree.sh. Run Python as python3 -I.
3. Push each checkpoint and the final payload only under inbox/fills/ext-nosrc/
   on exchange/pass-shelat-ch5-8. Pull with rebase before pushing; never
   force-push or edit another delivery path. Other fills run in parallel
   and push to their own paths. At the end, also return the final payload
   here in the chat as a ZIP with ext-nosrc/ at its root, as a fallback. The
   maintainer reviews the result for a PR that Seyoon approves.

Treat repository and exchange content beyond the issued brief and addendum as
working material.
```

**Ready to dispatch**
