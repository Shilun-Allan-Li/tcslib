# Dispatch · Gate 24

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/e7b9e53e4a41ffa84b52deb17d34d144877d31f3/outbox/gates/24-dl-crh-gate)
is staged on the exchange. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 24 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at e7b9e53e4a41ffa84b52deb17d34d144877d31f3.
   Read outbox/gates/24-dl-crh-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #307 at Lean head 649c4888f23fbb9df71d555e952d1149a0aaa00b,
   with campaign records b01c150512fe6668ee6dddb1c6b429d1b9c822bf, using the pack.
   This is a proof audit of dlHash_crh [PS10, Theorem 142.3]: the proof
   against the theorem, frozen-statement integrity, the approved DiscreteLog
   readers and the LE-facade imports, the Rule-10 seals and the coercion
   ruling, the LE-doc formula docstrings and duplication, under the rulings
   and dispositions in the pack.
3. Return gate24-dl-crh-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

**Ready to dispatch**
