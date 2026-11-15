# Dispatch · Gate 29 round 2

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/3de4f1a6ee540b13250a6355c92b187878d35ed0/outbox/gates/29-learning-gate-r2)
is staged on the exchange (local commit, for the maintainer to verify and push). Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 29, round 2, in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 3de4f1a6ee540b13250a6355c92b187878d35ed0.
   Read outbox/gates/29-learning-gate-r2/README.md, pack-r2.md and bundle.md.
   Verify the pack using SHA256SUMS. The round-1 pack is
   outbox/gates/29-learning-gate/ at exchange
   341f61def10e0481a7c29fa4787a80d6ece7d5df.
2. Re-audit draft PR #313 at Lean head 2b6c29816de4cb1cd0e6b74fa3ae848c9f0f1be9,
   with campaign records fb8737f827e398fec2f819f89c0416dc7b52f03d, using the pack.
   Round 1 was HOLD at 8befc589 (G29-01 major: hj re-proved
   OneWay.uexp_const; G29-02 major: firstBit_of_pos re-proved the
   headD_drop_ofFn reader). Check that both are resolved: LE-gate29a
   (94b31964, rebased as 9b40c7ce; hj by OneWay.uexp_const, proof only)
   and LE-gate29b (2b6c2981; firstBit_of_pos from the merged
   TCSlib.Cryptography.headD_drop_ofFn of #316, proof only), with their
   evidence (landing-r1/, landing-r2/: the integration build 268/268, the
   seals and controls, the axioms, admissions 39 -> 38); the rebase onto
   6ce4658d (range-diff identical; base delta #314-#317); and that no new
   undisclosed copy appeared since round 1 (DL-47 lists the pre-existing
   headD/getD copies; any further undisclosed duplicate of a public lemma
   is a major). Say whether anything is new since round 1, and whether
   each round-1 finding is closed. The integration rebuilds on the merged
   tip with #318, #319, #323 or #324, whichever merges second, are pending
   merge conditions the maintainer runs, not audit items.
3. Return gate29-learning-r2-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

The records (pin `fb8737f8`, then this dispatch commit) and the exchange commit `3de4f1a6` (on the exchange tip
`b35fa7e3`) must be pushed first.

**Ready to dispatch**
