# Dispatch · Gate 36

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/ab34c528748af26491d896e0f504373b45e4ada1/outbox/gates/36-sc-garble-gate)
is staged on the exchange (local commit, for the maintainer to verify and push). Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 36 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at ab34c528748af26491d896e0f504373b45e4ada1.
   Read outbox/gates/36-sc-garble-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #323 at Lean head cd9a48438c2a6548fe9e246ce569be57c9df96b3,
   with campaign records fb18d199fdce1f8cd1ae94ea9e092c52b157ce86, using the pack.
   This is a proof audit of sc-garble (PS10 6.2.2-6.2.3): correctness of
   the seven targets (spDecStr_wrongKey, specialScheme_wrongKey,
   specialScheme_multiMessageSecure, nestedSpecial_wrongKeyBot,
   uprob_not_good_le, yaoSeed_good_whp, sliceMultiMessageSecure_of_prfOut)
   and of B2 against the frozen statements and the book, including
   specialScheme_multiMessageSecure directly from D4, the B1 maximization
   with the empty-set convention, and Gate 27's obligations (1)-(6);
   frozen-statement integrity (55 ADDED, 0 CHANGED, 0 REMOVED; the SG-1
   check exactly 6 REMOVED, 0 CHANGED, with both controls; the stricter
   Yao.lean rule); the one frozen-file change DAGCircuit.isFaninTwo_iff
   (approved, SG-F01); undisclosed duplication beyond DL-46 and DL-47
   (SG-F04 ruled ledger; any further undisclosed duplicate of a public
   lemma is a major); the Rule-10 seals and controls (coe-A canonical,
   the seal-B PolyExpr.eval attribution SG-F07); the landing edit LE-doc
   (docstrings only); and the docstring and sketch rules, under the
   rulings and dispositions in the pack. The integration rebuilds on the
   merged tip with #313, #318, #319 or #324, whichever merges second, are
   pending merge conditions the maintainer runs, not audit items.
3. Return gate36-sc-garble-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

The records (pin `fb18d199`, then this dispatch commit) and the exchange commit `ab34c528` (on the Gate 29
round-2 exchange commit `3de4f1a6`) must be pushed first.

**Ready to dispatch**
