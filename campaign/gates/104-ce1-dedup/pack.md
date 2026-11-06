# External audit pack: dedup CE-1, one equal-codes lemma (PR #213, a dedup gate)

## Why this PR

The dedup window (12.2c), opened on 2026-11-06 by the user, retires the ledger's acknowledged
families one PR at a time. **CE-1** (`campaign/duplication-ledger.md`): equal codes of window
configurations give equal vertices. The same statement had the same one-line proof through
`coreSum_eq_of_cfgWord_eq` in two places:
- `Complexity.ExpBFS.coreSum_eq_of_code_eq`, in `SpaceComplexity/ExpBFS/Radius`;
- `Randomized.BPLInP.coreSum_eq_of_code_eq`, in `Randomized/BPLInPCount`.

The recorded disposition was to keep `ExpBFS`'s and re-point the other's uses. Both files are
Hydroxyi's. The user allowed mechanical edits there, with an FYI.

**The PR:** #213 on `lean/dedup-ce1`, head `fdc0e425` (full hash in the bundle header). It
changes two files, `Randomized/BPLInPCount` and `Randomized/SpaceAmplifyPolyCode`.

## What changed (verify)

- **`Randomized.BPLInP.coreSum_eq_of_code_eq` is deleted.** This removes one public declaration;
  no other file used it.
- **Its five uses cite `Complexity.ExpBFS.coreSum_eq_of_code_eq`:**
  - in `BPLInPCount`: `stepRel_iff`, `acceptLang_iff` and `haltsWithin_of_codes`;
  - in `SpaceAmplifyPolyCode`: `mem_stepLang_iff` and `mem_acceptLang_iff`.
- **`haltsWithin_of_codes`'s proof sketch** now names the `ExpBFS` lemma.
- **No import changes:** `BPLInPCount` already reaches `ExpBFS/Radius`, through
  `Randomized.Space`.
- **No other copy:** the library search, by `coreSum_eq_of_cfgWord_eq` uses and by the statement's
  shape, finds no further declaration copy. The same one-line argument appears inline in
  `Codec/Bridge` (lines 113 and 120) and in `Codec/Word`'s `decodeCfg_cfgCode`. Both files sit
  upstream of `Radius`, and `Word` is the home of `coreSum_eq_of_cfgWord_eq`, so neither can cite
  the lemma. They are not members.

## Brief for the auditor

1. **Completeness:** is any copy of the statement, or any use of the deleted name, left in the
   library?
2. **The removal:** is deleting the public duplicate right, given the disposition, rather than
   keeping it as an alias?
3. **Scope:** does the change touch anything beyond the five uses and the deletion?

## Repository-side attestations (verify or challenge)

- **Freeze** (`evidence/freeze/`):
  - `BPLInPCount` 12 → 11 public, with the duplicate removed and the three bodies above changed;
  - `SpaceAmplifyPolyCode` 18 → 18 public, with the two bodies above changed;
  - no statement changes.
- **Screen** (`evidence/screen/`): the two files and `ExpBFS/Radius`, at base and head. The base
  has 39 declarations and 4 pairs; the head has 38 and 2. The two pairs gone are the 100% copy
  in both directions. No pair is new.
- **Lint** (`evidence/lint/`):
  - the campaign lint on `Randomized`: 0 FAIL, 51 WARN over 65 files, as at the base;
  - the policy linter: the same single finding at base and head (`mem_stepLang_iff`, 21 lines
    with no sketch).
- **Replay** (`evidence/merged-tree/`): `replay-lce1` at `fdc0e425`, over the downstream closure
  of the two files, chained from the campaign's `oleans-lnth`: **7 modules, 0 failed,
  0 `sorry`**; static 0 mismatches.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/104-ce1-dedup/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `ce1-dedup-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
