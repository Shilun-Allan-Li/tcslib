# Dispatch · Gate 20 round 2

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/ed63370ed1a9edaa412871a5529aa188928bc366/outbox/gates/20-dl-consolidation-gate-r2)
is staged on the exchange. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 20, round 2, in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at ed63370ed1a9edaa412871a5529aa188928bc366.
   Read outbox/gates/20-dl-consolidation-gate-r2/README.md, pack-r2.md and bundle.md.
   Verify the pack using SHA256SUMS. The round-1 pack is
   outbox/gates/20-dl-consolidation-gate/ at the same exchange commit.
2. Re-audit draft PR #298 at Lean head c2839c41ca6b3a9c34db1595a1ad287768316630,
   with campaign records 1ca834544fa2c866b5e370f97ecd338cad9f1b12, using the pack.
   Round 1 was HOLD (G20-01 major: omitted raw evidence; G20-02 minor: two
   missed folds). Check the evidence supplements, the new landing edit
   LE-gate20 and its complete evidence, and say whether each round-1 finding
   is closed.
3. Return gate20-dl-consolidation-r2-findings.md as Markdown in this chat. If
   you need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

**Ready to dispatch**
