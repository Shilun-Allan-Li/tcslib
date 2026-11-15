# Dispatch · Gate 34

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/a74d11833a0814bb686a4b961c5712957008d6a9/outbox/gates/34-sc-ot-gate)
is staged on the exchange (local commit, for the maintainer to verify and push). Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 34 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at a74d11833a0814bb686a4b961c5712957008d6a9.
   Read outbox/gates/34-sc-ot-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #318 at Lean head f62a25b3eda099c9cf9371900664752e7b89007d,
   with campaign records 5d719839503c1f29f65f5ffa200410349a782276, using the pack.
   This is a proof audit of sc-ot (otProtocol_polyTime and
   otProtocol_simulators, PS10 Protocol 160.4 and Proposition 161.5):
   correctness against the frozen statements and the book, including
   Alice's 2*delta(n) bound at every n and Bob's side through
   tdpPredictor/viewDist with the signed-predictor identity and the 16
   hEHC instances summed; frozen-statement integrity (141 ADDED, 0 CHANGED,
   0 REMOVED, frozencheck 0, EnhancedHardCore unchanged under G3-8);
   undisclosed duplication beyond DL-48 (F-01 fixed by LE-reuse, F-02 and
   F-04 ruled ledger debt, F-07 notes; any further undisclosed duplicate of
   a public lemma is a major); the Rule-10 seals and controls (coe-A
   canonical, the strict ctlCoeReader attribution F-09); the landing edits
   LE-doc (docstrings only) and LE-reuse (proof only); and the docstring and
   sketch rules, under the rulings and dispositions in the pack. The
   integration rebuild on the merged tip (#316 and #317 have merged since
   the PR base; and with #319, whichever merges second) is a pending merge
   condition the maintainer runs, not an audit item.
3. Return gate34-sc-ot-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

The records (pin `5d719839`, then this dispatch commit) and the exchange commit `a74d1183` (on the exchange tip
`a6be22fa`) must be pushed first.

**Ready to dispatch**
