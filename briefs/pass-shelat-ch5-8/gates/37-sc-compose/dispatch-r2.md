# Dispatch · Gate 37 round 2

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/f4287c3c7804dbae3b21fe831222941c2fc08d22/outbox/gates/37-sc-compose-gate-r2)
is staged on the exchange (local commit, for the maintainer to verify and push). Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 37, round 2, in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at f4287c3c7804dbae3b21fe831222941c2fc08d22.
   Read outbox/gates/37-sc-compose-gate-r2/README.md, pack-r2.md and bundle.md.
   Verify the pack using SHA256SUMS. The round-1 pack is
   outbox/gates/37-sc-compose-gate/ at exchange
   5fab5874b1411ab7a4f8343e6dd4e1add234516b.
2. Re-audit draft PR #324 at Lean head 4bd2d80bfb58fab5243c66c9f1a697a30b533756,
   with campaign records 4de7ff85bfb4eaa53b4531218fca44fdf7cd64e2, using the pack.
   Round 1 was HOLD at a6eaebd7 (G37-01 major: ComposeMachines.encodeMsgs_append
   re-proved the public CommitmentLemmas.encodeMsgs_append; G37-02 major:
   ComposeBound.length_encodeMsgs_le re-proved CommitmentLemmas.length_encodeMsgs_le;
   G37-03 minor: truncated reader formulas). The head is the round-1 head
   plus one signed commit, LE-gate37, with no rebase. Check that G37-01 and
   G37-02 are closed (both re-derived from the public lemmas through the
   CommitmentLemmas import, headers kept; the import acyclic, +47 modules),
   and that G37-03 is closed (all 20 truncated formulas completed, docstrings
   only). Assess the side effect: the import brings
   TCSlib.Cryptography.splitCoins into Runs.lean's closure and shadows the
   bare splitCoins there, so the new helper def composeCoins and the
   statements of composeCoins_fst and composeCoins_snd now read
   ComposeSim.splitCoins. decls2 against round 1 is therefore not empty: 2
   statements CHANGED in text only. Confirm whether the elaborated types are
   identical (the pack gives the source argument; the combined build and the
   census are the build evidence). Check that no new undisclosed copy appeared
   since round 1 (any further undisclosed duplicate of a public lemma is a
   major). Say whether anything is new since round 1, and whether each
   round-1 finding is closed. The integration evidence is the combined build
   of all open PRs (integration/), which the pack shows is exactly the final
   merged state; the merge order (#324 after #326 and #327) and any rebuild
   for whichever PR merges second are merge conditions the maintainer runs,
   not audit items.
3. Return gate37-sc-compose-r2-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

The records (pin `4de7ff85`, then this dispatch commit) and the exchange commit `f4287c3c` (on the exchange tip
`acc86827`) must be pushed first.

**Ready to dispatch**
