# Dispatch · Gate 24 round 2

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/9bdc6e341003529631f2b5b2d61c5399deba0969/outbox/gates/24-dl-crh-gate-r2)
is staged on the exchange. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 24, round 2, in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 9bdc6e341003529631f2b5b2d61c5399deba0969.
   Read outbox/gates/24-dl-crh-gate-r2/README.md, pack-r2.md and bundle.md.
   Verify the pack using SHA256SUMS. The round-1 pack is
   outbox/gates/24-dl-crh-gate/ at the same exchange commit.
2. Re-audit draft PR #307 at Lean head d356381aadc350860f9a0e97123e84d9aefa585b,
   with campaign records a518558d26988753261c73b436c4493adbc16cb0, using the pack.
   Round 1 was HOLD (G24-01 major: inputWord_take re-proved the public
   take_ofFn_castLE; G24-02 and G24-03 minor: two record errors). Check the
   new landing edit LE-reuse and its evidence, the two errata, and the two
   trial-merge builds of #307 onto the merged tip; say whether anything is new
   since round 1, and whether each round-1 finding is closed.
3. Return gate24-dl-crh-r2-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

**Ready to dispatch**
