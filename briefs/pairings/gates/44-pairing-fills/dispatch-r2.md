# Dispatch · Gate 44 round 2

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/2e0152540aae5bb1ce7f8061572aedc5a4fc5437/outbox/gates/44-pairing-fills-gate-r2)
is staged on the exchange. The commit is local and signed, and is not pushed yet; the maintainer pushes it. Seyoon
dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Gate 44 of the pairing campaign (the
fills of T1 and T4), round 2, in https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 2e0152540aae5bb1ce7f8061572aedc5a4fc5437.
   Read outbox/gates/44-pairing-fills-gate-r2/README.md, pack-r2.md and
   bundle.md. Verify the pack using SHA256SUMS, and verification-r2.zip using
   the SHA256SUMS inside it. The round-1 pack is
   outbox/gates/44-pairing-fills-gate/ at exchange
   30ef1257a56873489b599007782046b7dedeb7fc; the round-1 findings are
   findings-r1.md in the round-2 folder.
2. Re-audit two draft PRs together, using the pack, with campaign records
   4f4a7592a54cf82fa04f96b83645d7936672614c:
   - PR #340 at Lean head 916afc25c21f5e52b4b01958186ad55d2f615fd1, unchanged
     since round 1 (T1 BilinearGen.bdhAssumption_of_dbdhAssumption);
   - PR #346 at Lean head 98cb0e521a94e94c304c78348fb5d3033435a3ed (T4
     exists_bb1_distinguisher): round 1's head
     89a18a8225be1b76166af12a15179da291747783 plus the landing edit LE-g44.
   Their merge with the records pin is
   T44' = bee027f0903d531b3a43511cea16bfa123210291 in every order. Its code
   differs from round 1's T44 33681cb8ed893a897ca2028d5ada70ca29237978 only in
   the three LE-g44 files.
   Round 1 was HOLD (0 blockers, 1 major, 1 minor, 1 note; no mathematical
   gap). Say whether each round-1 finding is closed:
   - G44-01 (major): Seyoon's ruling accepts the two disclosed re-derivations
     and repays them in cleanup Stage 2: ledger rows DL-55 (T1's inline
     verdict identity vs TrapdoorPredictor.decide_singleton_eq_true) and DL-56
     (poly_rU/rZ/rW/rS vs Games/Efficiency's polyTimeComputable_r*), with the
     Stage 2 scope lines. Both reports' "nothing for the duplication ledger"
     lines carry dated corrections, and the bb1-machine review a matching
     note (pack section 1). Do these record the explicit acceptance, the
     shared home and the repayment point that policy section 1 requires?
   - G44-02 (minor), by LE-g44 98cb0e52: docstrings only, in
     BonehBoyenMachine/Draws.lean, Words.lean and Handler.lean. The bounded
     sampler and its bound are attributed to Candidates.sampleBelowL and
     Candidates.statClose_sampleBelowL (Candidates/DiscreteLog.lean), with
     PS10 Theorem 52.3 kept as context only and the three References entries
     corrected. Is the attribution right, and is the edit comment-only (each
     file byte-identical to its parent with comments stripped)?
   - G44-03 (note): are the corrected control figures right (per variant 2
     sealed and 2 unsealed probes, 25 negatives, 12 in A and 13 in B; 50
     across strict and coe)?
   Check the T44' evidence and its binding (pack section 4):
   - the merges;
   - the replay of the 10 modules downstream of the three files, on a copy
     of round 1's output: rc 0, state check, link counts, olean comparison,
     snapshot #4 rehash;
   - admissions 196, unchanged, and the axioms log;
   - the canonical coe-A seals on Draws, Words, Handler and
     BonehBoyenMachine (0 errors, request sets row-identical to round 1's);
   - lint.
   Round 1's other seals are carried forward by comment-strip identity, with
   the collector log byte-identical. Say whether that suffices or a re-run is
   necessary. Say whether round 1's passes still hold (pack section 5) and
   whether anything new is undisclosed (section 6 and the known slips).
   Round 1's passes are not re-audited. Gate 40, the bb1-sim fill (T2, T3)
   and #351/#352 are out of scope. The merge order and the snapshot adoption
   are maintainer merge conditions, not audit items.
3. Return gate44-pairing-fills-r2-findings.md as Markdown in this chat. If you
   need multiple evidence files, return a ZIP containing that Markdown and
   evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

## State at staging

- **Records pin:** `4f4a7592a54cf82fa04f96b83645d7936672614c`, the records tip just before this staging commit, as in
  rounds 1 and 2 of Gate 42 and round 1 here. The pack's own files and the three report corrections are filed after the
  pin.
- **Records commit:** one SSH-signed commit on `cryptography/pass-shelat-ch2-4` that carries this file. It is **not
  pushed**. It adds or changes only these paths:
  - in `briefs/pairings/gates/44-pairing-fills/`: `resolutions-r1.md`, `pack-r2.md`, `dispatch-r2.md`,
    `le-g44.diff.txt`, `pr346-r2.diff.txt`, `source-head-r2.json`, `sources-r2.zip`, `verification-r2.zip` and
    `SHA256SUMS-r2`;
  - the corrections in `fills/pair-bdh/inhouse-r1/REPORT.md`, `fills/bb1-machine/inhouse-r1/REPORT.md` and
    `fills/bb1-machine/final-r1/review.md`;
  - one decision-log row in `PairingCryptographyPlan.md`.
- **#346:** LE-g44 is `98cb0e521a94e94c304c78348fb5d3033435a3ed`, one SSH-signed commit on `89a18a82`. It is on the
  local branch `land/pairings-bb1-machine`, in the sparse worktree `$SP/wt-le-g44`. It is **not pushed**: the PR branch
  is still at `89a18a82` until the maintainer pushes it.
- **Exchange:** the commit is `2e0152540aae5bb1ce7f8061572aedc5a4fc5437`. It is one SSH-signed commit on the exchange tip
  `d7a9adb5b70c70c1b6fb8dc3d0aa5a60d720c1ef` ("stmt gsw-6a: final"), fetched at staging.
  - The local branch is `stage/gate44r2-exchange`, in the sparse worktree `$SP/wt-exch-g44r2`.
  - The commit adds only `outbox/gates/44-pairing-fills-gate-r2/` (15 files), as Gate 42 round 2 did. It is **not
    pushed**.
  - `SHA256SUMS` verifies 14/14 from a fresh `git archive` of the commit.
  - `bundle.md` has 30 sections and is not committed to the records (workflow §3).
  - `verification-r2.zip` (`384befe6…`) has 133 entries and verifies against its own `SHA256SUMS` from a fresh extract.
- **Olean trees:** `$SP/olean-replay-g44b` is kept (map without Mathlib `fca1b6a3…`). It becomes snapshot #5 if #340 and
  #346 both merge with Lean = T44′. `$SP/olean-replay-g44` was deleted after its map `ded2f64d…` was rechecked and
  recorded. Snapshot #4 rehashed 0/0/0 at the end.
- **PR descriptions:** drafts went to Seyoon. #346's adds LE-g44 and the new head; #340's corrects the overlap bullet
  (DL-55). They are not posted by this job.

**Before dispatch:** push LE-g44 to `land/pairings-bb1-machine`, the exchange commit and the records commit, and post
the two PR body updates. Then the pack is **ready to dispatch**.
