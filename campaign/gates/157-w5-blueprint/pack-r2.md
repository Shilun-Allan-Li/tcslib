# Gate 157 round 2 · W5: the blueprint for chapters 3–4 (PR #361)

**A light audit, round 2.** Seyoon dispatches and merges. The PR changes no Lean.

- **Head:** branch `closeout/w5-blueprint`; the dispatch prompt gives the commit.
- **Round 1** audited `87c3f11dba4984fac510f9447a9875ca94c8db4f` and returned HOLD: one major
  (G157-01) and two minors (`findings.md`, verbatim). This round checks the resolutions in
  `resolutions.md`.
- `pack.md` is round 1's, with its orphan paragraph corrected to point here.

## What changed since round 1

- **Blueprint, two files** (`git diff 87c3f11d <head> -- blueprint`):
  - **NTimeDiagonalizer.tex:**
    - `dz_kit_exists`'s prose now gives the input calls' bound `A(g(n) + 1)` and the install
      calls' bound `A(|y| + 1)`, with the two output-length bounds (G157-01).
    - `exists_queryTM`'s title now reads "within a multiple of `g(n) + 1`".
    - `qy_kit_exists` now lists every call's bound in place of "each meeting its stated linear
      or polynomial time bound".
  - **Codec/Machine.tex:** the headings of `ScId`, `IcId` and `CpId` now match their bodies
    (G157-02).
- **Records:**
  - `resolutions.md`;
  - `evidence/ORPHANS-CLASSIFIED.json`, the 1,572 orphans by cause (G157-03);
  - `evidence/VALIDATE-r2.txt`, a rerun at the repaired head.

## Brief for the auditor

1. **G157-01.** Check `dz_kit_exists` and `exists_queryTM` against `NTimeDiagonalizer.lean`
   (`DzKit`'s fields `qcS`, `gcS`, `pcS`, `lcS`, `acS`, `qcL`, `acL`; `exists_queryTM`'s
   statement). Check also that no other entry in the chapter makes the same input-linear claim
   for a `g`-bounded call.
2. **G157-02.** Check the three headings.
3. **G157-03.** Check the corrected explanation against the pinned validator (blob `ee022d64`)
   and the classification. The 712 stale chapters 1–2 entries are outside W5's scope and are
   reported, not changed.

## Evidence

- **`VALIDATE-r2.txt`:** 0 dangling `\uses`, 0 duplicate bindings, 0 `\uses` cycles; 1,572
  orphans, none in the chapter scope.
- **`ORPHANS-CLASSIFIED.json`:**
  - **860** are declarations in modules no root import reaches, so they were never compiled and
    have no graph entry.
  - **712** are entries for declarations removed in chapters 1–2 areas: TuringMachine 583,
    CookLevin 64, ClassNP 62, and 3 elsewhere.
- Coverage, the work plan and the dependency graph are unchanged from round 1.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate157-w5-blueprint-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
