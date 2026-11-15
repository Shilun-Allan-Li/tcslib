# Dispatch · Gate 37

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/5fab5874b1411ab7a4f8343e6dd4e1add234516b/outbox/gates/37-sc-compose-gate)
is staged on the exchange (local commit, for the maintainer to verify and push). Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 37 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 5fab5874b1411ab7a4f8343e6dd4e1add234516b.
   Read outbox/gates/37-sc-compose-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #324 at Lean head a6eaebd78c48e7fdfd06263edb84b70bc00ec593,
   with campaign records c44557596ee5c714e1277891591cc8b5d51a0ab0, using the pack.
   This is a proof audit of sc-compose (HybridProtocol.composeP_efficient,
   composeV_efficient and hbcSecure_compose, Gol04 7.3.1, Theorem 7.3.3):
   correctness against the frozen statements and the book, including the
   five-step sketch with epsilon = epsilon_A + epsilon_B; frozen-statement
   integrity (185 ADDED, 0 CHANGED, 0 REMOVED, frozen check 0); undisclosed
   duplication beyond DL-49 (SC-F01 ruled ledger debt; anything further is
   a major); the Rule-10 seals and controls (coe-A canonical); the landing
   edits LE-doc (70 formulas, docstrings only) and LE-prose (a6eaebd7, the
   prose-only exception Seyoon approved for SC-F03); and the docstring and
   sketch rules, under the rulings and dispositions in the pack. The review
   build ran at LE-doc f61ce08f; LE-prose was checked doc-only by stripping
   doc comments and was not rebuilt. Its rebuild in #324's integration
   build, and the integration rebuilds on the merged tip with #313, #318,
   #319 or #323, whichever merges second, are pending merge conditions the
   maintainer runs, not audit items.
3. Return gate37-sc-compose-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

The records (pin `c4455759`, then this dispatch commit) and the exchange commit `5fab5874` (on the Gate 36
exchange commit `ab34c528`) must be pushed first.

**Ready to dispatch**
