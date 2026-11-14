# Dispatch · Gate 26

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/81225b67422a472381f041a3dc57c4f2de2d0e8b/outbox/gates/26-lamport-gate)
is staged on the exchange. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 26 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 81225b67422a472381f041a3dc57c4f2de2d0e8b.
   Read outbox/gates/26-lamport-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #309 at Lean head 987efb5156b3ae20cff4576b379eb1c607f33cb0,
   with campaign records 156949a315a04a8fe7035a67680979de6d949905, using the pack.
   This is a proof audit of lamport_oneTimeSecure [PS10, Theorem 137.2]:
   the proof against the theorem, frozen-statement integrity, the approved
   facade imports, the seal-B disposition and the Rule-10 seals, the
   LE-rule10 proof edit, the LE-doc formula docstrings and sketches, the
   opacity blocks, and duplication, under the rulings and dispositions in
   the pack.
3. Return gate26-lamport-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

**Ready to dispatch**
