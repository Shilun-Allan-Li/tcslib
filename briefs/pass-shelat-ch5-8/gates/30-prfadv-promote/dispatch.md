# Dispatch · Gate 30

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/341f61def10e0481a7c29fa4787a80d6ece7d5df/outbox/gates/30-prfadv-promote-gate)
is staged on the exchange. Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 30 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 341f61def10e0481a7c29fa4787a80d6ece7d5df.
   Read outbox/gates/30-prfadv-promote-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #314 at Lean head 5757bc0604527602d790a1a57e9703374ce02c7b,
   with campaign records 7bd85992f8bd61df48f43092bc5c845d5fac1b27, using the pack.
   This is a promotion audit under ruling F-01 (DL-44): the placement of
   TCSlib.Cryptography.prfAdv_eq_expect beside prfAdv, the new
   Games.Bridges.Experiments import in Pseudorandom/Functions/Defs.lean
   (acyclic and justified), the proof-only re-derivation of
   ETTGame.prfAdv_eq_expect with its API unchanged, any other copies of the
   identity (the private prfAdv_prfReduction stays deferred), and Rule 10,
   under the rulings and dispositions in the pack.
3. Return gate30-prfadv-promote-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

**Ready to dispatch**
