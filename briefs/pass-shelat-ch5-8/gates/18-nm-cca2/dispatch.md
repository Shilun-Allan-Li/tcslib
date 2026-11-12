# Dispatch · Gate 18

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/5f79e1a72d300eb6bc737532167ee6a4384b6595/outbox/gates/18-nm-cca2-gate)
is staged on the exchange. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 18 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 5f79e1a72d300eb6bc737532167ee6a4384b6595.
   Read outbox/gates/18-nm-cca2-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #294 at Lean head 1636480237286f538bb75b0021b2285edcd0b5b9,
   with campaign records 3c6ee34a713a6a3db4c930b6b16f195484c63896, using the pack.
   This audits the proof of FixedLengthPKScheme.indSecure_cca2_iff_nmSecure_cca2
   (PS10 Theorem 175.9), its three helper modules, the two authorized
   PublicKey/OracleSecurity readers and the maintainer's landing edits.
3. Return gate18-nm-cca2-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

**Ready to dispatch**
