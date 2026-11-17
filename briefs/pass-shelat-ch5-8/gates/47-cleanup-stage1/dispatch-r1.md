# Dispatch · Gate 47 round 1 (the cleanup Stage 1 gate: DW-5 #347 and Stage 1 #355)

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/eae18c1b2a4c78e96d124fb0433288f9f739eafb/outbox/gates/47-cleanup-stage1-gate)
is pushed to the exchange (`eae18c1b2a4c78e96d124fb0433288f9f739eafb`; see State at staging). The duplication items B1–B7 are ruled (DL-59, DL-60).
Seyoon dispatches.

## Prompt for Codex

```text
You are an external Codex auditor for Gate 47 (the cleanup Stage 1 gate: DW-5 and
the Stage 1 promotions), round 1, in https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at eae18c1b2a4c78e96d124fb0433288f9f739eafb.
   Read outbox/gates/47-cleanup-stage1-gate/README.md, pack-r1.md and bundle.md.
   Verify the pack using SHA256SUMS, and verification-r1.zip and sources-r1.zip
   using the SHA256SUMS inside each.
2. Audit two stacked draft PRs together, using the pack, with campaign records
   659542ecd9413b504d30da8c937b9805e6c1f71f. Their joint tree with the records tip
   at phase 2 (e1d39836ed4a69a34914c35f4c73c71de853dcc6) is
   TS1 = 1eaf940b938bb52e3919f5569893b58522df599b, on which all Lean evidence was
   produced:
   - PR #347 (DW-5) at head daa6e173cdd94cad1475b9a96eca613bce53ba61 (branch
     cleanup/dw5-derand-readers; base cryptography/pass-shelat-ch2-4, merge base
     2da7e0f3cd65ec93ed71813b7828c3b66ba18942): audit it as a proof/refactor. Nine
     typed-view readers in ModuleHost and IterateFindHost: are they exact
     definitional readers in their owners, pure insertions where stated (the two
     deleted IterateFindHost lines are module-docstring bullets), and placed and
     documented right? E1 computesFunInTime_find and polyTimeComputable_find are
     re-derived through them with every statement unchanged (frozen check: one
     ORDER difference); do they clear derand F-01's 20 IterateFind seal failures
     (20 -> 0 reproduced at TS1 in all four variants)? DW-9's 26 pre-existing
     host-file failures are out of its scope.
   - PR #355 (Stage 1) at head d3c7cb00092ad5913904654d922f30fc7d5fce4a (branch
     land/cleanup-stage1; base cleanup/dw5-derand-readers at daa6e173): 69 new
     declarations by pure insertion (decls2 69/0/0; 21 files +1079/-0). Audit
     them as new public API: each true, general (every ledgered copy an
     instance), correctly placed in the shared homes the CS1 rulings set,
     additive (only ADDED; no existing declaration changed), with readers,
     formula docstrings, source tags or glue notes and proof sketches; the
     Stage 2 hand-over (repoint.tsv, stage2-addendum.tsv, the fourteen approved
     blocks-alias changes) recorded but NOT made here; and the ledger rows.
   Check (pack, questions A-E):
   - duplication: an undisclosed or unaccepted re-proof or restatement of a
     public TCSlib or Mathlib lemma is a major. The pack lists the overlaps the
     ledger already covered (part A) and seven more the maintainer's sweep
     found (B1-B7), which Seyoon ruled before dispatch: B1 (Games.extTape,
     extTape_of_lt, extTape_update against the public extendStream,
     extendStream_def, extendStream_update_of_ne in LazySampling.lean) accepted
     as ledger row DL-59 with its Stage 2 repayment, B2-B7 as DL-60. Confirm or
     refute each overlap, find any other, and say whether DL-59 and DL-60
     satisfy policy.md's duplication rule and the G44-01 standard;
   - the evidence: the TS1 replay on olean snapshot #5 (556/556 rc 0, state
     1429 OK, snapshot 0/0/0), its binding to the two heads, admissions
     196 = 196 per module, the axiom prints (69 and 27) and the census of the
     21 owners (1224 constants), the seals A/B strict/coe on 21 owners with the
     exact failure inventory classified as notation-only or pre-existing, the
     paired controls (20/20 and 30/30 per variant), the unfold scan (0 foreign
     in the 80 touched declarations), lint 92/104 -> 92/103, and phase 2's
     seven disclosures; exact per-variant counts;
   - whether anything is undisclosed, including the records/PR discrepancies
     the pack lists.
   Out of scope: Stage 2's changes (re-points, deletions, the fourteen
   blocks-alias changes, DW-9's and DW-10's fixes), DW-10's inventory, #351 and
   #352 (DW-11), the Complexity handoff, and #357-#360 except as the pack's
   merge interaction. The merge order and the re-replay and snapshot adoption
   are maintainer merge conditions, not audit items.
3. Return gate47-cleanup-stage1-findings.md as Markdown in this chat, with
   findings numbered G47-01, G47-02, ..., counts by severity per PR, and a
   verdict per PR (#347, #355) and overall: CLEAR (zero blockers and zero
   majors) or HOLD. If you need multiple evidence files, return a ZIP
   containing that Markdown and evidence.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

## State at staging

- **Records pin:** `659542ecd9413b504d30da8c937b9805e6c1f71f` ("Records: LE-g45b on #359; Gate 47 sweep rulings (DL-59,
  DL-60)"). It is a records-only advance (0 Lean, toolchain, manifest or lakefile paths) from `95da6120`, the tip at first
  staging, and carries Seyoon's rulings on the sweep (DL-59, DL-60, `cleanup-stages.md`, the Complexity handoff addendum,
  the decision-log row) and snapshot #6's adoption at T `8060f6b7`. Its Lean differs from phase 2's tip `e1d39836` in
  #357's 9 files; pin × #355 = `20d1101ade46ba26919f01e30f7ee9422495669b` = TS1 plus those 9 files (blob-equal to
  `dfdc56f2`).
  - Later records commits: `2f83708f` (gsw-6a-fills and DW-10 deliveries) and `fcb8adca` (the coordinator's commit of
    the work-in-progress records copy of this directory, made because a repository hook required it). Both are records-only.
    This directory's files now differ from `fcb8adca`'s copy and are **left uncommitted** for the maintainer.
- **Exchange:** the commit is `d9c1bd43970ab88a93bfc3db09760f438b7c0d4c`, one SSH-signed commit on the exchange tip
  `57cd9272d5739fae252cf486297c696f7b90d2bd` (fetched at staging). It replaces the earlier local `937e6a55`, which was
  never pushed: `stage/gate47-exchange` was reset to `57cd9272` and rebuilt.
  - **Pushed** (2026-11-17) by the maintainer with Seyoon's approval, after a permission check had refused the staging
    job's push: the commit was replayed with `git cherry-pick -S` onto the moved tip
    `8e09dc58baf3c6ee000dc05f4a3763cd0a78041b` (Gate 45 round 2's pack) as
    **`eae18c1b2a4c78e96d124fb0433288f9f739eafb`**; only `outbox/gates/47-cleanup-stage1-gate/` changes, and the folder verifies 13/13 from a fresh
    `git archive`.
  - The commit adds only `outbox/gates/47-cleanup-stage1-gate/` (14 files, 1.8 MB). The sparse worktree
    `$SP/wt-exch-g47` used to build it has been removed.
  - `SHA256SUMS` (`185e8b5be6a274bcbcd7d82e34ec94e0aca77c3cf34ed74c1c72430f113ee4a4`) verifies 13/13 from a fresh
    `git archive` of the commit. `bundle.md` is `48176f8c423f05a0ff88e773547856343455842d03641dba8af29ef26e60358d`, with
    64 sections, each built from its named source. `verification-r1.zip`
    (`5d2d6023c4ba7bfdd338dcd4031fb502e48d2a679558189632b3dea47ca10124`) has 173 entries and verifies against its own
    `SHA256SUMS` from a fresh extract (172/172); the `phase1/`, `phase2/` and `dw5/` copies also verify against their
    `SHA256SUMS.original`. `sources-r1.zip` (`91948ee4515a5bcff161e20582e8b46e62799434b95019991712b3f1150a79ed`)
    verifies 73/73.
- **PR descriptions edited at staging** (2026-11-17, through the GitHub connector), to remove stale statements:
  - **#347** now cites the TS1 replay, snapshot #6 and the re-replay, and Gate 47 (updated 16:08:30Z).
  - **#355**'s "Still to do: Phase 2 … about 551 modules" is replaced by phase 2's PASS on TS1, snapshot #6 and the
    re-replay, and Gate 47 with DL-59/DL-60 (updated 16:09:01Z).
  - Both bodies end with the required two-line attribution, and nothing else in them changed. The pack's descriptions
    are the edited bodies, re-read afterwards.
  - Heads are unchanged: #347 `daa6e173` (REST `base.sha` `7291f6b2`) and #355 `d3c7cb00` on `daa6e173`.
- **#359** is now at `d154c8830fc8ffc52671b41992e7dbef61e30959` (LE-g45 + LE-g45b); the merge checks use it.
  - Clean in both orders, with no shared path. The only modules downstream of both sides are the 3 aggregates.
- **No Lean, no `lake`** was run for this staging; the pack reuses the phase-1, phase-2 and DW-5 evidence as recorded.
  - Git-only work: `git merge-tree`, temporary unreferenced commit objects for three-way merges (`git commit-tree`, no
    ref), `git grep` and `git cat-file` on tree objects, and `grep` over the Mathlib, Batteries and core sources.

**Not ready to dispatch** until the exchange commit is pushed. Once pushed, the records copy can be committed and
Seyoon can dispatch with the prompt above.
