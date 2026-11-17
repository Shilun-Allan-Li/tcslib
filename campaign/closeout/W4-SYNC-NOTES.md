# W4 preparation: syncing `main` into the campaign (2026-11-17)

Stage 3's second half (`STAGES.md`). It runs after #350 (stage 2) merges, so that gate 154's
merged-tree replay stays the merge's build. D5 (Seyoon, 2026-11-16): as in #180, merge `main` into
the campaign first, replay, then one PR from the campaign to `main` that leaves `campaign/` and
`devtools/` off `main`.

## What `main` adds (measured at `origin/main` `a954201d`)

- **28 commits** since the merge-base `abd2bd3d`. They include #180's integration (`22b03750`,
  "the campaign's records stay off main"), #183/#194 (InformationTheory, LearningTheory/PAC), #200,
  #240 (the sharded theorem dataset), #295 (the blueprint reorganization) and #348 (workflow §4.1,
  the snapshot procedure).
- **Lean:** 44 files, all outside `Complexity`: BooleanAnalysis (34, Gaussian space and Borell),
  Cryptography/SecretSharing (2), InformationTheory (5 with the root), LearningTheory (3), and one
  line in `TCSlib.lean`. **No Lean file overlaps the campaign's changes.** `lean-toolchain`,
  `lake-manifest.json` and the lakefile are unchanged.
- **Blueprint:** about 40,000 files added and 2,000 modified under `blueprint/src` (the
  reorganized blueprint W5 builds on).
- **Deletions the campaign must not take:** `main` has no `campaign/` (8,000+ files) and
  `devtools/seyoon` (38 files), by design (#180).

## Trial merge (`git merge-tree`, campaign tip against `origin/main`)

47 conflicting paths:

- **`campaign/…` and `devtools/seyoon/…`:** modify/delete. Resolve by keeping the campaign's side
  for all of `campaign/` and `devtools/`, including files `main` deleted silently (restore the
  whole trees from the campaign parent after the merge, then check `git diff <campaign parent> --
  campaign devtools` is empty).
- **`AGENTS.md`:** both sides appended sections (campaign +9 lines, `main` +6). Keep both.
- **Blueprint, two chapters:** `ClassNP/Tautology.tex` and `CookLevin/Hardness.tex`. `main`
  re-headed every chapter (`\chapter` to `\section`, `Overview` to `subsection*`), and the campaign
  edited two lemma entries. Take `main`'s structure with the campaign's entries. W5 regenerates
  these chapters anyway.
- `.claude/CLAUDE.md` and `TCSlib.lean` auto-merge.

## Gate

A full replay of the merged tree's root closure from `oleans-c5c153` (or the stage 2 snapshot)
covers the 44 new or changed non-Complexity modules and everything importing `TCSlib.lean`. It
needs a records-only gate, or none (PLAN W4). The merge commit then becomes the snapshot base for W5.
