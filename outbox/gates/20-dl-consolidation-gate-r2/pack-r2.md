# Gate 20 · Duplication consolidation DL-30–DL-34 · round 2

The auditor is Codex. Round 1 was HOLD (0/1/1/0); its findings are `findings/gate20-dl-consolidation-findings.md`.
This round re-audits the two fixes and the one new commit. The round-1 pack (`pack.md`) still defines the scope; its
questions stand for anything round 1 left unverified.

- **PR:** draft [PR #298](https://github.com/Shilun-Allan-Li/tcslib/pull/298), now at
  `c2839c41ca6b3a9c34db1595a1ad287768316630` (tree `5eb486b8c2f1901e3c4db08b610840a12d13fe0f`).
- **Base:** `2ea4df08d009a4bbdb8042795ff062d7f22db325`, unchanged. Later base commits touch records only.
- **New since round 1:** one commit, **LE-gate20** `c2839c41`, on top of the round-1 head `6f853adc`.
- **Resolutions:** `resolutions-r1.md`.

## What to check

### 1. G20-01: is the raw evidence now complete?

**`supplement-r1/verification-supp.zip` and `landing-supp.zip`**
- They hold the 1028 and 92 files that `verification.zip` and `landing.zip` left out.
- Each file should be byte-identical to the hash in its main ZIP's inner `SHA256SUMS`.
- Main plus supplement should cover 2441/2441 and 188/188 entries. `supplement-r1/coverage-check.txt` records this.
- Please confirm, and check what the files show:
  - the baseline and head census and collector runs;
  - the 80 base and 82 head whole-file seal logs and their `results.jsonl`, with the seal sources, manifests and
    request records;
  - the control plan and sources, and the 22 nm-sim seal runs.
- Do the raw runs support the seal table (A 34/41, B 30/41 at head; 33/40, 28/40 at base; 0 new failing
  declarations), the census (2112 → 2099) and the nm-sim 22/22?

**Do the seals cover the final landing?** Your round-1 note said the worker's seal corpus predates the landing
edits. `resolutions-r1.md` § G20-01 explains why the maintainer's seals, together with the later re-seals, cover
`c2839c41`:
- the head seals were taken at `8e43131f`;
- LE-rule10's three modules were re-sealed at `7b7d07aa`;
- the 11 nm-sim files were sealed at `6f853adc`;
- LE-gate20's two files were re-sealed at `c2839c41`;
- the closure check covers the #297 rebase.

Is that argument sound?

### 2. G20-02 and LE-gate20

The diff is `landing-r1/LE-gate20.patch`, 2 files.

- **`UniversalPadding.lean`:** the private `PadQuad.ofFn_arrowCongr` is deleted. Its two uses rewrite with
  `ofFn_arrowCongr_finCongr`.
- **`OneWayLemmas.lean`:** `OneWay.ofFn_block_eq_take_drop` keeps its statement byte for byte. Its proof is
  `FunFamily.ofFn_blocks` through `FunFamily.blocks_apply`, with no unfolding of `blocks` or `blocksEquivX`.

Check that:
- the statement is unchanged;
- the proof uses only published lemmas;
- no other copy that the round-1 audit named remains.

**Evidence** (`landing-r1/`): `gate20-r1-evidence.zip` and its manifest `evidence-SHA256SUMS`. Nothing is left
out: the ZIP's entries are exactly the manifest's paths. Extracts:
- **Build:** 114 downstream modules through root `TCSlib` and both `audits/*/Checks` were rebuilt, all rc 0.
  `final-tree-check.txt` shows all 1198 modules with rc 0 at the head's source hashes.
- **Statements:** decls2 over the two files gives 0 rows. The whole PR is still 68/42/2/0.
- **Axioms:** the 164 constants of the two files are standard, and so are the 16 endpoints
  (`axioms-summary.txt`).
- **Seals:** see `seal-compare.txt`.
  - `OneWayLemmas` passes A and B, both at the head and at `6f853adc`.
  - `UniversalPadding` fails at the same 4 (A) and 5 (B) untouched declarations at the head and at `6f853adc`. It
    is not in the 41-file table.
  - 0 new failing declarations.
  - Paired controls ALL_OK.
- **Lint and widths:** lint shows an empty diff, and no line is newly over 100 characters (`widths-sizes.txt`).

## Updated files

- **`pr.diff-r2.txt`:** `git diff` from the base to `c2839c41`, over 53 paths.
- **`source-head-r2.json`:** hashes, line counts and over-width counts for the 52 changed files, and the 1 deleted
  file.

## Findings delivery

Return `gate20-dl-consolidation-r2-findings.md` as Markdown in this chat. If you have several evidence files, return
a ZIP. Use the same table and severities as round 1, and say for each round-1 finding whether it is closed. Report
the audited head and the counts by severity. The gate closes at zero blockers and zero majors.
