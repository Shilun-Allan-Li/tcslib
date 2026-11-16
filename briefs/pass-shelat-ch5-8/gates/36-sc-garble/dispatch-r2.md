# Dispatch · Gate 36 round 2

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/0bdffba74f2798b9f8aba4df3234e4dea58e9369/outbox/gates/36-sc-garble-gate-r2)
is staged on the exchange (local commit, for the maintainer to verify and push). Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 36, round 2, in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 0bdffba74f2798b9f8aba4df3234e4dea58e9369.
   Read outbox/gates/36-sc-garble-gate-r2/README.md, pack-r2.md and bundle.md.
   Verify the pack using SHA256SUMS. The round-1 pack is
   outbox/gates/36-sc-garble-gate/ at exchange
   ab34c528748af26491d896e0f504373b45e4ada1.
2. Re-audit draft PR #323 at Lean head 8c3f3e3fe2912784f680c10f8c478d2eeeeb7f6a,
   with campaign records 298338e34bb6a4c1754d406244ceeed7e8be6338, using the pack.
   Round 1 was HOLD at cd9a4843 (G36-01 major:
   SliceReduction.length_le_encodeList re-proved the public
   length_le_length_encodeList). Check that G36-01 is closed by LE-gate36
   (8c3f3e3f on cd9a4843, not rebased: the duplicate deleted, its one use
   in slicePost_encode re-pointed at the public lemma, an acyclic import
   of Asymptotic/BlockEncryptor adding 2 modules), with its evidence
   (landing-r1/: built on a scratch replica of the branch rebased onto the
   tip 654323f2 with the same patch; merge-tree(654323f2, 8c3f3e3f) is
   exactly the built tree 5662520d; 392 modules rc 0, decls2 exactly 1
   REMOVED, the frozen check 0, the seals, the axioms, admissions
   215 -> 208, the trial merge with #324); and that no new undisclosed
   copy appeared since round 1 (any further undisclosed duplicate of a
   public lemma is a major). Say whether anything is new since round 1, and
   whether each round-1 finding is closed. The integration rebuilds on the
   merged tip with #318, #319, #324, #326 or #327, whichever merges second,
   and the concurrent combined build of all open PRs, are pending merge
   conditions the maintainer runs, not audit items.
3. Return gate36-sc-garble-r2-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

The records (pin `298338e3`, then this dispatch commit) and the exchange commit `0bdffba7` (on the Gate 34 round-2
exchange commit `7add7297`, itself on the exchange tip `816971fc`) must be pushed first.

**Ready to dispatch**
