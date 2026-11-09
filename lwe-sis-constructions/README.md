# LWE/SIS construction campaign exchange

The user dispatches external jobs and approves code merges. Codex reads pinned
GitHub inputs and returns findings as Markdown in chat. Other namespaces remain
outside this campaign. The central target is `cryptography/lwe-sis-constructions`.

PRs #236 through #239 are merged. Gate 11 passed for #255's two probability
readers and #250's six Regev statistical proofs. The reader prerequisite
has passed its landing checks.

The next proof review is in `outbox/gates/12-sis-trapdoor-proofs-r1/README.md`.
Filled Lean/root `3bf1cb424b10abef3ae7a438c6b7d0e1916d0800`, bundled records `aff0a82679c201834415cbe293393fef7477f6e7`. The wave fills
40 obligations and leaves 18. The earlier proof and source-policy packets
remain available at their pinned revisions.
