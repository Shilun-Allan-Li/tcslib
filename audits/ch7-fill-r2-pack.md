# External audit pack — Chapter 7 fill gate, round 2: the duplication question

**Audited surface:** the Chapter 7 fill surface on the **merged tree**, branch
`complexity/arora-barak-ch3-4` of `https://github.com/Shilun-Allan-Li/tcslib`,
at the commit named in the dispatch. It comprises:

- `TuringMachine/Build/EmitIterEmbed.lean` and `Build/EmitIterBody.lean`;
- `ClassNP/PolyTimeBlockLoop.lean`, `PolyTimeBlockTests.lean` and
  `PolyTimeBlockMajority.lean`;
- the three block headlines `mem_P_of_blockAny`, `mem_P_of_blockMajority` and
  `mem_P_of_blockXorAny` in `ClassNP/PClosure.lean`.

Record findings in `audits/ch7-fill-r2-findings.md`. **The gate closes on zero
blockers and zero majors.**

## Why a second round

Round 1 (`audits/ch7-fill-findings.md`, attached) returned 0 blockers, 0
majors, 2 minors and 2 notes. It ran on the bundle from Aparna's fork
(`00be8b1d…`, sources at `a-gupte/tcslib@0c22ae33`), not on this repository's
merged-tree adaptation. That adaptation added a duplication question, which
round 1 therefore never answered. **This round asks only that question, plus
a check of the round-1 sweep.** Questions 1–6 are not reopened. Their
transfer to the merged tree rests on the attestation below; challenge it if
it does not hold.

## Questions

1. **Duplication** (`audits/TEMPLATE.md` failure mode 5, attached). Screen the
   surface for duplicated proved material, and verify the maintainer's
   pre-screen (`audits/evidence/ch7/ch7-fill-duplication-screen.md`, its
   script, and the re-run at this commit, all attached).
   - **What the pre-screen reports.** No copies of pre-existing repository
     material. One family of renamed re-proofs inside the stack: the OR, XOR
     and majority loops each carry their own copy of the same orbit, length
     and init lemmas. That puts `PolyTimeBlockMajority` at 4 of 14
     declarations (28.6%), over the one-fifth threshold.
   - **How to report.** Report each confirmed copy family at **major**, with
     the proposed fix "human acknowledgment required"; the gate may not close
     over it until the human maintainer accepts the debt and names its
     resolution.
   - **The family above is already acknowledged** (the human maintainer,
     2026-10-10: it is resolved in the 12.2c refactor as one generic lemma
     set, with statements unchanged; `audits/duplication-ledger.md`,
     `backlog.md` CH7-D1). Confirm its extent. It then does not hold the
     gate, though any further family you find does.
   - **Coverage.** Say whether the screen missed any copy, including
     re-derivations it cannot detect: the screen matches contiguous text,
     exact or consistently renamed, and does not see restructured proofs.
   - **Classification.** Judge the screen's mirror pairs (Class B) and its
     two borderline cases.
2. **The EmitIter layer against §12, as facts.** Compare the public
   `EmitIterEmbed` embedding layer (`SafeRun`, `padAction`, `embedCfg`,
   `embed_step`, `embed_run`) with the §12 layer `Build/Embed.lean`
   (attached). Report what each states that the other does not, for example:
   - state injection;
   - padding-tape contents;
   - relocation along an arbitrary tape embedding;
   - emission handling;
   - first-return and avoidance clauses.

   Do not propose a merge. It is already scheduled as 12.2c item 6, and your
   facts will scope it.
3. **The round-1 sweep.** Verify that `audits/evidence/ch7/ch7-fill-r1-minor-sweep.diff`
   is comment-only and accurate:
   - finding 1's corrected XOR bullet;
   - finding 2's corrected *Main results* and "control steps" bullet;
   - note 3's paragraph in `PClosure`'s "Block-query closure" section.

   Check that the paragraph describes the three headlines' behaviour on
   malformed words exactly, nested pairs included, and that no new text
   misstates anything.

## Repository-side attestations (verify or challenge)

- **Transfer** (`audits/logs/ch7-fill-r2-transfer.log`). Of the nine Lean
  files round 1 audited, six are byte-identical here to `0c22ae33`.
  `EmitIterEmbed`, `PolyTimeBlockLoop` and `PClosure` differ in comments only
  (comment- and whitespace-stripped identical): the P0 finding-5 docstrings
  and the round-1 sweep.
- **Screen re-run** (`audits/evidence/ch7/ch7-fill-duplication-screen-rerun.txt`).
  The unmodified script at this commit screens 112 declarations against 562
  files, one more file than the recorded run (the new `Build/CounterLoop.lean`).
  All 24 overlaps of at least 50% it reports (3 exact, 21 renamed) are among
  those the recorded classification lists, and none is new, so the
  classification is unchanged.
- **Re-check after the sweep** (`audits/logs/ch7-fill-r2-docfix-sweep.log`).
  The seven-module chain from `Build/EmitIterEmbed` to
  `Randomized/PolyTimeModel` re-checks with 0 errors and 0 sorry warnings.
  Lint reports 0 FAIL in `ClassNP` and `TuringMachine/Build`.
- **Earlier evidence carried from round 1:** the merged-tree sweep, 23/23
  (`audits/logs/ch7-fill-merged-sweep.log`), and the 36 axiom prints.

## Brief for the auditor

This round is narrow. Answer the three questions with evidence, in the
standard findings table (blocker / major / minor / note). Justify an empty
table with the screen facts you verified and any non-mechanical comparison
you made.
