# Dispatch · Gate 17

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/93dfe35805c56c063a111f0cf7bbe9817c77c53f/outbox/gates/17-pk-cpa-cca1-gate)
is staged on the exchange. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 17 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 93dfe35805c56c063a111f0cf7bbe9817c77c53f.
   Read outbox/gates/17-pk-cpa-cca1-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #293 at Lean head 63ca0eb3dccb65542e90c181b7ceb0a4a4a46272,
   with campaign records 8260a492ed740fcfc6019b355d142ac7bb587c3d, using the pack.
   This audits the proofs of Composability.prfFixedScheme_cpa and
   Composability.prfFixedScheme_cca1 (PS10 Theorem 168.2), their six helper
   modules, the four authorized OracleSecurity readers and the maintainer's
   landing edits.
3. Return gate17-pk-cpa-cca1-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

**Ready to dispatch**
