# Dispatch · Gate 35

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/8b5e96ad8a796a7f3158ffdaa7a6138f83d7a269/outbox/gates/35-canonizer-gate)
is staged on the exchange (local commit, for the maintainer to verify and push). Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 35 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 8b5e96ad8a796a7f3158ffdaa7a6138f83d7a269.
   Read outbox/gates/35-canonizer-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #319 at Lean head 6421ac1631ef08feed297c810f0839b178d2a2bb,
   with campaign records 034da63a3408d0112fa45df00abb3de3080246d2, using the pack.
   This is a proof audit of canonizer (TCSlib.Cryptography.exists_canonizerExp,
   PS10 section 2.13, run-3 audit P3-4): correctness against the frozen
   statement, including the bound d*(k+1)^d <= d*2^(d*k) and its edge cases
   (k = 0, d = 0, malformed codes); that the two frozen-file readers in
   CodeFormat and CodeSimulator are exactly the ones Seyoon pre-approved on
   2026-11-14, with nothing else changed in a frozen file; that the axiom
   closure of the target avoids the admitted appendBitTM_computes; C-F01,
   the whitespace-only re-wrap that changes two headers' bytes, as an
   LE-width-class acceptance; Rule 10, including that each reader is needed
   and sufficient and the full-file -DmaxErrors=0 CodeSimulator seals of
   C-F02 (coe-A canonical); duplication; and the docstring and sketch rules,
   under the rulings and dispositions in the pack. The integration rebuild
   on the merged tip (#316 and #317 have merged since the PR base; and with
   #318, whichever merges second) is a pending merge condition the
   maintainer runs, not an audit item.
3. Return gate35-canonizer-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

The records (pin `034da63a`, then this dispatch commit) and the exchange commit `8b5e96ad` (on the Gate 34 exchange
commit `a74d1183`) must be pushed first.

**Ready to dispatch**
