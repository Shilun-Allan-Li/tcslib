# Dispatch · Gate 39 round 2

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/30acab69c5ca5ad4b2dae1344736a6039d6010c6/outbox/gates/39-seq-zk-gate-r2)
is staged on the exchange (pushed). Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 39, round 2, in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 30acab69c5ca5ad4b2dae1344736a6039d6010c6.
   Read outbox/gates/39-seq-zk-gate-r2/README.md, pack-r2.md and bundle.md.
   Verify the pack using SHA256SUMS. The round-1 pack is
   outbox/gates/39-seq-zk-gate/ at exchange
   da8f8f66e505a9e27034667ff68a3b104036e84e.
2. Re-audit draft PR #327 at Lean head a94ba750b2f21ea5f2c3e58bc7959ad5ac9de871,
   with campaign records 2c42911bf538feb40d2f124a6cc8c21f0cbe3307, using the pack.
   Round 1 was HOLD at bd19c433 (G39-01 major: the local hsource in
   PaddedProverSpec.realPrefix_bounds re-proved the PR's own public
   PaddedProverSpec.next_length_le, undisclosed). The head is the round-1
   head plus one signed commit, LE-gate39, with no rebase. Check that
   G39-01 is closed: hsource is now d.next_length_le y B hbound tape hist;
   the added import of SequentialZK.ProofTransfers is acyclic and adds only
   that module to the closure; the header of realPrefix_bounds is unchanged,
   its sketch gains one inserted sentence, and nothing else in the code
   changes (decls2 against round 1 empty; 196 ADDED, 0 CHANGED, 0 REMOVED
   against the base). Check the rebuild and seal evidence in landing-r1/:
   #327 alone on the tip with #326 merged, 679/679 rc 0, admissions
   202 -> 197; the final combined tree with #324, 26/26 rc 0, admissions
   194; the RealPrefixBounds seals and controls; the axioms. Confirm that
   nothing regressed and that no new undisclosed copy appeared since round
   1 (any further undisclosed duplicate of a public lemma is a major). Say
   whether anything is new since round 1, whether the round-1
   confirmations still hold, and whether each round-1 finding is closed.
   The merge order (#327 before #324, #324 last) and the integration of the
   other open PRs (#331, #332, #333) are merge conditions the maintainer
   runs, not audit items.
3. Return gate39-seq-zk-r2-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

The records (pin `2c42911b`, then this dispatch commit) and the exchange commit `30acab69` (on the exchange
tip `3b5e3d4d`) are pushed.

**Ready to dispatch**
