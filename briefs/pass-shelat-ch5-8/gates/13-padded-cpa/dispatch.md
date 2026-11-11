# Dispatch · Gate 13

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/35ea3015a726096b19e1852b58114991ba332be9/outbox/gates/13-padded-cpa-gate)
is staged on the exchange. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 13 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 35ea3015a726096b19e1852b58114991ba332be9.
   Read outbox/gates/13-padded-cpa-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #288 at Lean head 892a3f3c78abcde8bdf822a3b4168ab3302b4272
   and campaign records f6b8de11291e56858eeb76990d53469cacc3f852 using the pack.
   This audits the proof of BitPublicKeyScheme.SingleBitSecure.padded_cpa,
   its two helper modules and the maintainer's landing edits.
3. Return gate13-padded-cpa-findings.md as Markdown in this chat. If you need
   multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

**Ready to dispatch**
