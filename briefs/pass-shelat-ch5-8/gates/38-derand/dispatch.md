# Dispatch · Gate 38

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/4b6ee799d15bac4042288fcb165d5c4d2d8f6a31/outbox/gates/38-derand-gate)
is staged on the exchange (local commit, for the maintainer to verify and push). Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 38 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 4b6ee799d15bac4042288fcb165d5c4d2d8f6a31.
   Read outbox/gates/38-derand-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #326 at Lean head c27005d67298f79c785a4e8ac1648da0a67d3614,
   with campaign records 24f4405205542f810157cbaf29a36ab99a52cbe8, using the pack.
   This is a proof audit of derand: Complexity.exists_seedMajorityTM (host
   H17), Complexity.seedMajority_mem_DTIME and
   TCSlib.Cryptography.Randomness.bpp_subset_dtime_subexp (PS10 8.2,
   Theorem 180.1). Check correctness against the frozen statements and the
   book, including the margins 7/12 and 5/12 and the Gate 28 route (binary
   fuel, terminal rank in range, no final_bound); frozen-statement integrity
   (53 ADDED, 0 CHANGED, 0 REMOVED); that the shared-file additions are
   exactly E1-E3 (pre-approved) plus SR-01 (Randomized.inBPP_iff and the
   Classes.lean size exception to 1415 lines, confirmed by Seyoon); Rule 10,
   where F-01 is ruled debt with a planned fix (deferred work DW-5): E1 reads
   hostTM by definition, giving 9 new seal failures that copy the 11
   pre-existing ones in polyTimeComputable_find, so verify that this
   attribution is exact and that nothing else fails; undisclosed duplication
   (anything undisclosed is a major); the docstrings and sketches, with the
   landing edit LE-doc (F-04, one docstring); and the axioms, under the
   rulings and dispositions in the pack. The integration evidence is the
   combined build of all open PRs (integration/), which the pack shows is
   exactly the final merged state; the merge order (#324 last) and any
   rebuild for whichever PR merges second are merge conditions the
   maintainer runs, not audit items.
3. Return gate38-derand-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

The records (pin `24f44052`, then this dispatch commit) and the exchange commit `4b6ee799` (on the Gate 37 round-2
exchange commit `f4287c3c`) must be pushed first.

**Ready to dispatch**
