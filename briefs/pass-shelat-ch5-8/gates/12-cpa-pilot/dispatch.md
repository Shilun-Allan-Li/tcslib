# Dispatch · Gate 12

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/2b8a52de306d6d2bd097887d6cfc6a173479aca9/outbox/gates/12-cpa-pilot-gate)
is staged on the exchange. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 12 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 2b8a52de306d6d2bd097887d6cfc6a173479aca9.
   Read outbox/gates/12-cpa-pilot-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #287 at Lean head 135d54511dc0e5c42d93d1d680bf1f26c6aba5cc
   and campaign records 8e8bc7672630a99abb9fee646006357d4153bacb using the pack.
   This is a statement audit of the CPA pilot: the adaptive CPA lift
   FixedLengthPKScheme.INDSecure.adaptive_cpa, the padded bitwise CPA theorem
   BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa, their corollaries
   and three new readers.
3. Return gate12-cpa-pilot-findings.md as Markdown in this chat. If you need
   multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

**Ready to dispatch**
