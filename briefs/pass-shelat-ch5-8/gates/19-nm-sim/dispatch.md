# Dispatch · Gate 19

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/d17ee1ca7e57fa3e9e0e7425fff5e8991b666678/outbox/gates/19-nm-sim-gate)
is staged on the exchange. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 19 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at d17ee1ca7e57fa3e9e0e7425fff5e8991b666678.
   Read outbox/gates/19-nm-sim-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #297 at Lean head 5da558b4d97aca00efd6dc396a1b0f3bffff268b,
   with campaign records 40213c18618ed1fa6df725b32a6bd3ed9c4054a3, using the pack.
   This audits the proofs of FixedLengthPKScheme.nmSecure_of_simNMSecure and
   FixedLengthPKScheme.simNMSecure_of_nmSecure_cpa (PS10 Theorem 174.8),
   their ten helper modules under NonMalleability/Simulation/, and the
   maintainer's landing edits.
3. Return gate19-nm-sim-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

**Ready to dispatch**
