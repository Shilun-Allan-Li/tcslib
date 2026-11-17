# Dispatch · Gate 48 round 1 (the bb1-sim gate)

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/827065642ff5965c6f7c51c592f18b9f32dc2811/outbox/gates/48-bb1-sim-fill-gate)
is staged on the exchange. The commit is local and signed, and is not pushed yet; the maintainer pushes it. Seyoon
dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Gate 48 of the pairing campaign (the
bb1-sim gate: the T2/T3 fill and its reader insertions), round 1, in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 827065642ff5965c6f7c51c592f18b9f32dc2811.
   Read outbox/gates/48-bb1-sim-fill-gate/README.md, pack-r1.md and bundle.md.
   Verify the pack using SHA256SUMS, and verification-r1.zip using the
   SHA256SUMS inside it.
2. Audit draft PR #357, using the pack, with campaign records
   e6cdf4d4eed898acd71d48bd60082140eb076cfe:
   - PR #357 at Lean head 7a98ba0140ce6334bef1f2a8d39c6dfceb6ccaff (base
     cryptography/pass-shelat-ch2-4 at e1d39836ed4a69a34914c35f4c73c71de853dcc6,
     the merge base; its Lean equals the #346 merge
     3f540c22360c869069a0fba684e23ce6f3cb20db, olean snapshot #5): the proofs
     of T2 bb1_sim_real and T3 bb1_sim_random (BB04 Theorem 4.1, the
     simulation steps) and of Games.ProbComp.expect_simulate_rel and
     expect_sample_rel in Games/Relational.lean; the ten approved readers in
     IdentityBased/Defs.lean and BonehBoyen.lean; five helper modules under
     IdentityBased/BonehBoyenSecurity/; and the landing edit LE-bsf1
     (7a98ba01). With it, bb1_sidSecure has an empty sorryAx trace.
   Check (pack, questions 1-10):
   - that the four targets are true as frozen and the proofs establish
     them, for every input, with the edge cases; that no helper is false,
     vacuous or an assumption in disguise; that bb1_sidSecure is now free of
     sorryAx;
   - that the four headers and statement prose, bb1_sidSecure and
     prob_simulate_rel are unchanged (frozen check 12/12, 8 controls), and
     every other frozen declaration too (decls2 69 ADDED / 0 CHANGED /
     0 REMOVED); that the ten readers are exactly the approved blocks,
     inserted verbatim at the approved anchors and nothing else (Seyoon's
     ruling of 2026-11-17; pins 97ecb6e0... and 88454d6f...); that LE-bsf1
     is docstring-only apart from the rfl reader bb1RealState_eq;
   - Rule 10: the 36 seals (9 owners; A and B; strict and coe, coe-A
     canonical; PolyExpr.eval and the FinDist coercion are notation), the
     paired controls (per harness 32 probes and 485 sealed negatives, each
     failing exactly once; bb1RealState_eq has no sealed negative because
     the abbrev is never requested; RealReads has no pair, BSF-F05), and
     the explicit-unfold scan;
   - sources and citations: the new [BB04] tags and locators, the glue
     notes, and the fill-local variants;
   - duplication (an undisclosed or unaccepted re-proof of a public lemma is
     a major): DL-57 against T4's private twins, any overlap with Games/
     (including cleanup Stage 1's Games/Tapes in open PR #355) and with
     Mathlib or Pairing/Group;
   - docstrings, proof sketches, file sizes, the axioms and the phase-2
     replay on olean snapshot #5 (19/19 rc 0, admissions 196 -> 192,
     exactly the four targets), and whether that evidence binds to the head;
   - whether anything is undisclosed (pack, known slips), and grade the
     review findings BSF-F01 to BSF-F08.
   #351 and #352 (merged) are out of scope: Seyoon assigned them to a later
   combined gate (DW-11). Gate 44 (T1, T4) and Gate 40 (the statements) are
   closed. The merge order and the snapshot adoption are maintainer merge
   conditions, not audit items.
3. Return gate48-bb1-sim-findings.md as Markdown in this chat, with
   findings numbered G48-01, G48-02, ..., counts by severity, and a verdict:
   CLEAR (zero blockers and zero majors) or HOLD. If you need multiple
   evidence files, return a ZIP containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

## State at staging

- **Records pin:** `e6cdf4d4eed898acd71d48bd60082140eb076cfe`, the tip of `origin/cryptography/pass-shelat-ch2-4` after
  `git fetch` at staging ("Records: bb1-sim fill phase 2 PASS on snapshot #5; draft PR #357"). It is the PR base
  `e1d39836` plus that one records-only commit (0 code paths); the pack's own files are filed after the pin.
- **Records copy:** this directory, `briefs/pairings/gates/48-bb1-sim-fill/`, written on the records checkout and **not
  committed**; the maintainer commits it (explicit paths). `bundle.md` is not committed to the records (workflow §3).
- **Exchange:** the commit is `827065642ff5965c6f7c51c592f18b9f32dc2811`, one SSH-signed commit on the exchange tip
  `f333bf7f6b7a9f75df4fa9baf202c3f52d712a51` ("Outbox: gate 155 bundle (PR #354, head 718dddc6)"), fetched at staging.
  - The local branch is `stage/gate48-exchange` in the records checkout's repository (the sparse worktree
    `$SP/wt-exch-g48` used to build it was removed after the commit). Push it with
    `git push origin stage/gate48-exchange:exchange/pass-shelat-ch5-8`.
  - The commit adds only `outbox/gates/48-bb1-sim-fill-gate/` (12 files).
  - It is **not pushed**. If the exchange tip moves before the push, replay the commit onto the new tip and put the new
    hash here and in the prompt (the pack and its sums do not name the exchange commit).
  - `SHA256SUMS` (`1cbb04d4f607090eba9fbddcdc936c3d4dddca86a32ab60b4b090956303728f1`) verifies 11/11 from a fresh
    `git archive` of the commit; `bundle.md` is `7d149217fabb00a2a4fbdf9f5fe1b84e3bd5eb0a3aed0aba92697dd91bc8a700`, 55
    sections, each checked equal to its source; `verification-r1.zip`
    (`3430e1c3ef83a991e1eae618fd6f3b3238b25298068f4d586b304d4ad48581d7`) has 190 entries and verifies against its own
    `SHA256SUMS` from a fresh extract.
- **PR #357:** draft, head `7a98ba01`, base `e1d39836` (REST `base.sha`), updated 2026-11-17T09:11:22Z; the description in
  the pack is the body read then.
- **No Lean, no `lake`** was run for this staging; the pack reuses the phase-1 and phase-2 evidence as recorded.

**Ready to dispatch** once the exchange commit and the records copy are pushed.
