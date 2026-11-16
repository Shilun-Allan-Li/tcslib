# Dispatch · Gate 39

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/da8f8f66e505a9e27034667ff68a3b104036e84e/outbox/gates/39-seq-zk-gate)
is staged on the exchange (local commit, for the maintainer to verify and push). Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Pass–shelat Gate 39 in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at da8f8f66e505a9e27034667ff68a3b104036e84e.
   Read outbox/gates/39-seq-zk-gate/README.md, pack.md and bundle.md.
   Verify the pack using SHA256SUMS.
2. Audit draft PR #327 at Lean head bd19c433a4cf3d4027ffc891d7d3c06e927e9dfa,
   with campaign records d5a3e2d0c399b918d72e5a51732905625e500bd2, using the pack.
   This is a proof audit of seq-zk: the five seqRep theorems ZK.seqRep,
   StatZK.seqRep, InteractiveProof.seqRep, InteractiveProofErr.seqRep and
   EfficientProverProofErr.seqRep. Check correctness against PS10 Theorem
   175.1 and Gol01 4.3.4; frozen-statement integrity (196 ADDED, 0 CHANGED,
   0 REMOVED; frozen check 0); StatZK_iff in ZeroKnowledge/Defs.lean, which
   Seyoon approved (S-01); the multi-agent provenance (each helper has a
   single owner, and the lead ran the final sweep); Rule 10 (only the
   pre-existing Defs failures, in the same 6 declarations at the base);
   undisclosed duplication (anything undisclosed is a major); the
   docstrings, with the landing edit LE-doc (S-02, 81 formulas, including 11
   cut at 240 characters, graded by the Gate 37 G37-03 standard) and the
   strict-PPT versus expected-PPT simulator note; and simulator uniformity
   (the uniformity audit found SQ uniform), under the rulings and
   dispositions in the pack. The integration evidence is the combined build
   of all open PRs (integration/), which the pack shows is exactly the final
   merged state; the merge order (#324 last) and any rebuild for whichever
   PR merges second are merge conditions the maintainer runs, not audit
   items.
3. Return gate39-seq-zk-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

The records (pin `d5a3e2d0`, then this dispatch commit) and the exchange commit `da8f8f66` (on the Gate 38 exchange
commit `4b6ee799`) must be pushed first.

**Ready to dispatch**
