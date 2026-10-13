# B5b fill gate: resolutions (round 1 → round 2)

**Gate:** the B5b fill gate (`audits/ch34-b5b-fill-pack.md`; round-1 bundle
`audits/ch34-b5b-fill-bundle.md`, 67 sections).
**Round 1** (`audits/ch34-b5b-fill-findings.md`, preserved verbatim): **0 blockers, 2 majors,
3 minors, 17 notes; does not close.** The auditor found no mathematical defect in the
conditional summit or in the four promoted lemmas, and confirmed:
- the cumulative freeze, byte for byte, including the reversal of CH34-D4 and of the maintainer's
  comments;
- the dispatcher, the guard and the image correctness, on all 16,383 words of length at most 13;
- the summit's compositional route, and the probe transcriptions after normalization;
- the factoring's retirements, its one acknowledged pair, and the admission boundary.

Both majors concern the packet. The round-2 materials are `audits/ch34-b5b-fill-r2-pack.md` and
`audits/ch34-b5b-fill-r2-bundle.md`.

## Majors

1. **Input identity.** The kickoff named SHA-256 `f6858d96…`, but the attached bundle hashed to
   `6e4ad39959ca9b0387f045a9f9958aff03a062dc3283be42fed41332dcc578f5`. **Erratum: the attached
   bytes are authoritative.** `f6858d96…` was the first build of the bundle. It was rebuilt as
   `6e4ad399…` once the user's acknowledgement of the factoring's new pair (backlog F6-1(j)) was
   recorded in the pack, the CH34-D4 record and the backlog. The dispatch folder held the rebuilt
   bundle, but the kickoff text reused the first build's digest. The rebuilt bundle is the one
   now committed (`3d012949`). The round-2 kickoff names both digests, and round 2 repeats the
   identity check.
2. **The union screen's population was not attached.** 42 of the 66 files were missing, among
   them `ClassNP/SAT.lean`, and the delivery screen's historical neighbours were absent too.
   **Resolved:** the round-2 bundle carries:
   - all 66 union-population files at `56258cb5`, the union screen's revision (the maintainer
     checked each file against the tree the screen read: 66 of 66 identical);
   - the delivery screen's 22-file population at its base `ebc58d67`, and the delivered
     `EXPCOM.lean` at the agent commit `7a2ed9ed`;
   - the maintainer's rerun of the delivery screen from those files
     (`audits/logs/ch34-b5b-fill-r2-delivery-screen-{before,after}.txt`).

   The maintainer also rechecked the SAT pair: `expcom_front_poly` and `SAT.sat_pipeline_poly`
   share only the names of the polynomial-time closure rows they cite
   (`polyTimeComputable_of_linear` with `computesFunInTime_pairValid`, `polyTimeComputable_and`,
   `polyTimeComputable_ite`, `polyTimeComputable_const`), composed over different functions.
   The pack's erratum records the completeness correction.

## Minors

3. **The cumulative ledger missed `expcom_inc_prefix`** (107 characters). The corrected
   historical count is 5,037 of 13,500, **37.31%**. The delivery's 36.52% stays as reported.
   Recorded as an erratum in backlog CH34-D4 and in the pack.
4. **The live tracker lagged the ruling.** Backlog CH34-D4 now records the completed factoring
   (`6c7e35bd`) and what stays open: the colleague-owned retirements (F6-1(j)) and the
   triple-uniqueness request. F6-1(a) and (e) are marked done, with their open remainders.
5. **The D4 freeze log miscounted ConfigGraph's publics** (17 → 17; correctly 16 → 16), because
   the maintainer's tool counted a docstring line as a declaration. The tool now ignores lines
   that start inside a comment. The regenerated log `audits/logs/ch34-d4-freeze-r2.log` differs
   from the original only in that count. Erratum in `audits/ch34-d4-record.md`.

## Notes

Notes 6–19 and 21–22 record no findings. **Note 20** is applied: the `expcom_summit_budget`
sketch now states the strict bound `g + 1 ≤ G`. The change is comment-only, and `EXPCOM.lean`
elaborates after it with no errors and no warnings.
