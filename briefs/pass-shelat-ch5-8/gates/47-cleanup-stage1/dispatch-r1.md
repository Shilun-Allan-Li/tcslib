# Dispatch · Gate 47 round 1 (the cleanup Stage 1 gate: DW-5 #347 and Stage 1 #355)

The Codex pack is staged on the exchange as a **local, unpushed** commit (see State at staging). Seyoon dispatches once
the maintainer has pushed it and resolved the duplication items B1–B7 of the pack, or chosen to dispatch with them
disclosed.

## Prompt for Codex

```text
You are an external Codex auditor for Gate 47 (the cleanup Stage 1 gate: DW-5 and
the Stage 1 promotions), round 1, in https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at 937e6a55d3f6f37a8643d3ce3b567225be38f6e0.
   Read outbox/gates/47-cleanup-stage1-gate/README.md, pack-r1.md and bundle.md.
   Verify the pack using SHA256SUMS, and verification-r1.zip and sources-r1.zip
   using the SHA256SUMS inside each.
2. Audit two stacked draft PRs together, using the pack, with campaign records
   95da6120f0b3b3c80e3078b1d497cbc93aa15fc4. Their joint tree with the records tip
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
     ledger covers (part A) and seven it does not (B1-B7, among them
     Games.extTape/extTape_update against the public extendStream and
     extendStream_update_of_ne in LazySampling.lean); confirm, refute or grade
     each, and find any other;
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

- **Records pin:** `95da6120f0b3b3c80e3078b1d497cbc93aa15fc4`, the tip of `origin/cryptography/pass-shelat-ch2-4` after
  `git fetch` at 2026-11-17 11:24 UTC ("Records: #357 merged (BB1 complete); snapshot #6 adoption pending"). It holds the
  #357 merge `8060f6b7`, so its Lean differs from phase 2's tip `e1d39836` in #357's 9 files; pin × #355 =
  `1a1548572d49879ee262d704da431180aefb3a39` = TS1 plus those 9 files (blob-equal to `dfdc56f2`).
  - **The tip moved again during staging**, records-only (0 Lean, toolchain, manifest or lakefile paths): `e4d6308a`
    ("Records: LE-g45 on #359") and `8c83367204e515af54ce9d0fe2012344094a3909` ("Records: olean snapshot #6 adopted (#357
    merge)"). The pack reads every record at the pin and is unaffected; snapshot #6 (T `8060f6b7`) is the one #347/#355
    re-replay on before merge.
- **Records copy:** this directory, `briefs/pass-shelat-ch5-8/gates/47-cleanup-stage1/`, written on the records checkout
  and **not committed**; the maintainer commits it (explicit paths). `bundle.md` is not committed to the records
  (`workflow.md` §3).
- **Exchange:** the commit is `937e6a55d3f6f37a8643d3ce3b567225be38f6e0`, one SSH-signed commit on the exchange tip
  `5df47d4a157a69065bc60dbd3964caf5cea10912` ("Outbox: gate 158 bundle (W6 final audit)", fetched at staging).
  - The local branch is `stage/gate47-exchange` in the records checkout's repository (the sparse worktree
    `$SP/wt-exch-g47` used to build it was removed after the commit). **Not pushed.** Push it with
    `git push origin stage/gate47-exchange:exchange/pass-shelat-ch5-8`; if the exchange tip has moved, replay it with
    `git cherry-pick -S` onto the new tip (only `outbox/gates/47-cleanup-stage1-gate/` changes) and update the hash in the
    prompt above.
  - The commit adds only `outbox/gates/47-cleanup-stage1-gate/` (14 files, 1.8 MB).
  - `SHA256SUMS` (`ca2ab626f72aaa4cdf175df3b134db49d3a3f9a6af349aa952ca72638d04a272`) verifies 13/13 from a fresh
    `git archive` of the commit; `bundle.md` is `4586a90f2c4caea8bc1ba00bc55547b9ef2db38e25879f0110f631a544e78a9b`, 62
    sections, each built from its named source; `verification-r1.zip`
    (`e5c77d55cdfbfdca32971e999248acdb2a671a9a37e9c01963965447777bc959`) has 171 entries and verifies against its own
    `SHA256SUMS` from a fresh extract (170/170; the `phase1/`, `phase2/` and `dw5/` copies also verify against their
    `SHA256SUMS.original`); `sources-r1.zip` (`91948ee4515a5bcff161e20582e8b46e62799434b95019991712b3f1150a79ed`)
    verifies 73/73.
- **PR #347:** draft, head `daa6e173`, REST `base.sha` `7291f6b2`, updated 2026-11-16T22:16:25Z. **PR #355:** draft, head
  `d3c7cb00`, base `cleanup/dw5-derand-readers` at `daa6e173`, mergeable_state `clean`, updated 2026-11-17T07:38:19Z. The
  descriptions in the pack are the bodies read then (both predate phase 2's result).
- **#359** moved to `ad9c4fc701ed145cbc96acceefaad447398c8321` (LE-g45) during staging; the merge checks use it.
- **No Lean, no `lake`** was run for this staging; the pack reuses the phase-1, phase-2 and DW-5 evidence as recorded.
  Git-only work: `git merge-tree`, temporary unreferenced commit objects for three-way merges (`git commit-tree`, no ref),
  `git grep`/`git cat-file` on tree objects, `grep` over Mathlib/Batteries/core sources.

**Not ready to dispatch** until the exchange commit is pushed and the records copy committed, and the maintainer has
resolved (or chosen to disclose unresolved) the duplication items **B1–B7** of `pack-r1.md`, of which B1 (`Games.extTape`
against `extendStream`) has the shape Codex graded major at G44-01, G45-01 and G48-01.
