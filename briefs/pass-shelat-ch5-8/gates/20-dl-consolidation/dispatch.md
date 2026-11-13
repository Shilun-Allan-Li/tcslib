# Dispatch · Gate 20

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/1350b6083bb08760ab32ada31da63a860377c7f9/outbox/gates/20-dl-consolidation-gate)
is staged on the exchange. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 20 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 1350b6083bb08760ab32ada31da63a860377c7f9.
   Read outbox/gates/20-dl-consolidation-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #298 at Lean head 6f853adc61d5d175ee83c69f6c07ab2da112cabc,
   with campaign records 3015c622434a0321e784a3da1d83c125b426bf7e, using the pack.
   This is a refactor audit of the duplication consolidation DL-30 to DL-34:
   promoted lemmas, deleted copies and re-pointed uses, with no audited
   statement change, plus the maintainer's five landing edits (including the
   re-point of the nm-sim files merged in #297).
3. Return gate20-dl-consolidation-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

**Ready to dispatch**
