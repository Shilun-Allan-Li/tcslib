# Gate 20 · resolutions, round 1

The round-1 verdict was HOLD, with counts 0 blockers, 1 major, 1 minor and 0 notes.
- **Findings:** `findings/gate20-dl-consolidation-findings.md` (SHA-256
  `d2938faf2840295cdc57560c748af301af1a8fb219dd8d30637cdd06b8fc4282`).
- **Audited head:** `6f853adc61d5d175ee83c69f6c07ab2da112cabc`.
- **New head:** `c2839c41ca6b3a9c34db1595a1ad287768316630`, tree `5eb486b8c2f1901e3c4db08b610840a12d13fe0f`.
  Its one new commit is LE-gate20.

| # | Severity | Disposition |
|---|---|---|
| G20-01 | major | **Fixed (evidence only).** The two supplements are in `supplement-r1/`. |
| G20-02 | minor | **Fixed** by **LE-gate20** `c2839c41`. Evidence: `landing-r1/`. |

## G20-01

`supplement-r1/` holds `verification-supp.zip` and `landing-supp.zip`.
- **Contents:** the 1028 and 92 omitted files. Every one is the original, byte-identical to the hash in its ZIP's
  inner manifest. Nothing was re-run.
- **Coverage:** the main ZIP and its supplement together cover every manifest entry: 2441/2441 and 188/188, with
  every hash matching, no overlap, and nothing outside the manifest (`supplement-r1/coverage-check.txt`).
- **The examples the finding names are all present:**
  - the base census and collector logs;
  - both `results.jsonl` files for the base and head seal runs;
  - the 80 base and 82 head seal logs;
  - `controls/out/controls-plan.json` and the control sources;
  - the 22 nm-sim seal logs;
  - `seals/{A,B}/manifest.json`.
- **The new evidence for LE-gate20** (`landing-r1/gate20-r1-evidence.zip`) leaves nothing out: `unzip -Z1` lists
  exactly the paths of its manifest `evidence-SHA256SUMS`.

**The 41-file seal table and the final landing.** Codex notes that the worker's seal corpus predates the landing
edits and the #297 rebase. The maintainer's head seals in `verification.zip` and its supplement already cover the
landing edits:
- the head seals were generated at landing head `8e43131f`;
- the three LE-rule10 modules were re-sealed at `7b7d07aa`.

Each later change touches only modules whose own seals were re-run:
- **#297 rebase:** none of the 41 sealed owners has a file or TCSlib closure containing a changed module
  (`landing.zip:logs/consolidation-seal-closure-check.txt`). The 11 nm-sim files were sealed at `6f853adc`.
- **LE-gate20:** it changes only proofs in its two files, which were re-sealed at `c2839c41`. A proof change in a
  dependency does not affect another file's seal: seals make foreign definitions opaque, and a theorem's proof is
  never unfolded.

## G20-02 · LE-gate20 (`c2839c41`)

The diff touches 2 files, +9 −17 (`landing-r1/LE-gate20.patch`).

**`Asymptotic/UniversalPadding.lean`**
- The private `PadQuad.ofFn_arrowCongr` is deleted.
- Its two uses, in `ofFn_appendEquiv` and `ofFn_splitCoins_symm_cast`, now rewrite with
  `ofFn_arrowCongr_finCongr`.

**`Asymptotic/OneWayLemmas.lean`**
- The statement of `OneWay.ofFn_block_eq_take_drop` is byte-identical.
- Its proof is now `FunFamily.ofFn_blocks`, read through the published `FunFamily.blocks_apply`. It unfolds neither
  `blocks` nor `blocksEquivX`.
- The docstring gains a proof sketch.

## Checks at `c2839c41`

These are in `landing-r1/`, and the raw runs are in `gate20-r1-evidence.zip`.

**Build**
- The two files and everything downstream were rebuilt on the consolidation's full tree: 114 modules through root
  `TCSlib` and both `audits/*/Checks`, all with rc 0.
- All 1198 TCSlib/`audits` modules end with rc 0 at the final-head source hash, with 219 admission warnings
  (unchanged).

**Statements** (re-run by the maintainer)
- decls2 over the two files from `6f853adc`: 0 rows.
- Whole PR from `2ea4df08`: 68 ADDED / 42 REMOVED / 2 MOVED / 0 CHANGED, unchanged.

**Axioms**
- The 164 stored constants of the two files are standard.
- `ofFn_block_eq_take_drop` and `length_take_drop_block` print `[propext, Classical.choice, Quot.sound]`.
- The 16 endpoints are unchanged.

**Rule 10**

| File | A, head vs `6f853adc` | B, head vs `6f853adc` |
|---|---|---|
| `OneWayLemmas` | pass, pass | pass, pass |
| `UniversalPadding` | fails at the same 4 declarations (`exists_family`, `family_inLen`, `invProbAt_family_le`, `lengthRegular_gStr`) | fails at the same 5 declarations (those 4 and `strongOneWay`) |

- These failures predate this PR: neither file is in the consolidation's seal table, and none of the failing
  declarations is touched.
- New failing declarations: 0.
- Paired controls: ALL_OK for both files. Every sealed negative fails exactly once.

**Lint:** an empty diff against `6f853adc`.

**Sizes and widths:** 909 and 522 lines; no new line over 100 characters.
