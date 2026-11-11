# Dispatch · Gate 15

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/c53e2baace2497ceca5814ffc8b1f57e9c04eaf8/outbox/gates/15-cpa-pilot-proofs-gate)
is staged on the exchange. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 15 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at c53e2baace2497ceca5814ffc8b1f57e9c04eaf8.
   Read outbox/gates/15-cpa-pilot-proofs-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #290 at Lean head 95df0b4fa15e140ffd8f692699c66d0683fc916d and
   draft PR #291 (stacked on #290) at Lean head c286bc6a9b372036f959a033729d841ce10dfa16,
   with campaign records 315f781b6d7daf051c9f639fe6fba2e12839d4c2, using the pack.
   This audits the proofs of FixedLengthPKScheme.INDSecure.adaptive_cpa and
   BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa, their helper modules
   and the maintainer's landing edits.
3. Return gate15-cpa-pilot-proofs-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

**Ready to dispatch**
