# Dispatch · Gate 34 round 2

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/7add7297c4021ea4c68d3b890814e02f71c1f9b8/outbox/gates/34-sc-ot-gate-r2)
is staged on the exchange (local commit, for the maintainer to verify and push). Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 34, round 2, in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 7add7297c4021ea4c68d3b890814e02f71c1f9b8.
   Read outbox/gates/34-sc-ot-gate-r2/README.md, pack-r2.md and bundle.md.
   Verify the pack using SHA256SUMS. The round-1 pack is
   outbox/gates/34-sc-ot-gate/ at exchange
   a74d11833a0814bb686a4b961c5712957008d6a9.
2. Re-audit draft PR #318 at Lean head b0bad23ae611983e3323460bb8c564da90ad6e8c,
   with campaign records 4c95a8437dec980209d12327e6208c5ae967e178, using the pack.
   Round 1 was HOLD at f62a25b3 (G34-01 major: OT.getD_zero_eq and
   OT.getD_one_eq' re-proved the public headD_drop; G34-02 major:
   OT.length_ofFn_coins copies the public NMSim.length_ofFn_coins).
   Check that G34-01 is closed by LE-gate34 (b0bad23a; both readers from
   TCSlib.Cryptography.headD_drop, proof only, no import), with its
   evidence (landing-r1/: the integration build 270/270, the seals run with
   -DmaxErrors=0, the controls, the axioms, admissions 216 -> 214); that the
   G34-02 disposition (ruled ledger debt, DL-48) is recorded; the rebase
   onto 05d26fe5 (range-diff 5/5 identical; base delta #316 and #317, with
   #314 and #315 already in round 1's base); and that no new undisclosed
   copy appeared since round 1 (any further undisclosed duplicate of a
   public lemma is a major). Say whether anything is new since round 1, and
   whether each round-1 finding is closed. The integration rebuilds on the
   merged tip with #313 (merged), #319, #323, #324, #326 or #327, whichever
   merges second, and the concurrent combined build of all open PRs, are
   pending merge conditions the maintainer runs, not audit items.
3. Return gate34-sc-ot-r2-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

The records (pin `4c95a843`, then this dispatch commit) and the exchange commit `7add7297` (on the exchange tip
`816971fc`) must be pushed first.

**Ready to dispatch**
