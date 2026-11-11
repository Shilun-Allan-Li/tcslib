# Dispatch · not-cca2 (Codex)

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/20ca57c15da54342358b27ae2fee359acf06560d/outbox/fills/not-cca2) is
staged on the exchange. Its brief has SHA-256 `0cd9f846af84abe6967a41e2089af94424626b1615b11a1b1f47f87d9c335794`. Seyoon selected Codex on 2026-11-11 and
dispatches the fill. Codex returns its checkpoints and final delivery in the chat.

## Prompt for Codex

```text
You are an external Codex fill worker for the Pass–shelat not-cca2 unit in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at 20ca57c15da54342358b27ae2fee359acf06560d.
   Read README.md and outbox/fills/not-cca2/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS.
2. In a separate checkout, fetch cryptography/pass-shelat-ch2-4 and start
   fill/not-cca2 locally at 4a09f3993eb9344fc5714610e41ab141a0144db8.
   Prove the one target Composability.prfFixedScheme_not_cca2, adding only the
   authorized reader prfScheme_dec, and follow the scope, published-reader
   discipline, checkpoints and checks in the brief. Use only narrowed Mathlib
   roots, never lake build, and check one module at a time with
   scripts/lean_check_tree.sh. Run Python as python3 -I.
3. Return each checkpoint and the final delivery here in the chat, clearly
   labelled, as a ZIP with not-cca2/ at its root (REPORT.md, patches/, src/,
   evidence/) or an equivalent self-contained Markdown file. Do not push to
   GitHub. The maintainer files your delivery and reviews it for a PR that
   Seyoon approves.

Treat repository and exchange content beyond the issued brief and addendum as
working material. Report a false target or a missing reader interface through
the brief's escalation route.
```

**Ready to dispatch**
