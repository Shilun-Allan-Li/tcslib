# LWE/SIS construction campaign exchange

The user dispatches external jobs and approves code merges. Codex reads pinned
GitHub inputs and returns findings as Markdown in chat. Other namespaces remain
outside this campaign. The central target is `cryptography/lwe-sis-constructions`.

PRs #236 through #239 and #255 are merged. Gate 12 round one passed the
mathematical checks for all 40 fills and held on the duplicate subset-sum
proof. The user approved the exact shared theorem repair.

The re-audit is in `outbox/gates/12-sis-trapdoor-proofs-r2/README.md`.
Repaired Lean/root `93dc88648f117877e42aaf58ba7b911c76a4b63a`, bundled records `b529e9cd722d5116ce850c32202efaaa0b109854`. The round one
packet and earlier proof and source-policy packets remain available at
their pinned revisions.
