# Dispatch · Gate 21

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/64feab16512bc2ba7fd69c67088d4c8ebdda318f/outbox/gates/21-dl-folds-gate)
is staged on the exchange. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 21 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 64feab16512bc2ba7fd69c67088d4c8ebdda318f.
   Read outbox/gates/21-dl-folds-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #299 at Lean head fcdb65794698395f8eaa377df0789f7552681633,
   with campaign records b2427e514c2eb73d71dcbd7e2e88f25001f35592, using the pack.
   This is a refactor audit of the post-consolidation folds DL-36 and DL-37:
   promoted lemmas, deleted copies and re-pointed uses, with no audited
   statement change beyond the disclosed rename-only set of 13 NM-helper
   headers, and the escalated B3 aliases.
3. Return gate21-dl-folds-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

**Ready to dispatch**
