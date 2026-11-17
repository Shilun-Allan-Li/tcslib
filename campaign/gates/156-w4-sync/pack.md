# Gate 156 · W4: merge `main` into the chapters 3–4 campaign (PR #356)

**Records-only gate** (PLAN W4). Seyoon decides whether to dispatch an audit and merges.

- Merge commit `85b45d24ad149fe45772a9e456271f75eb45ee04` (branch `closeout/w4-sync`). Its parents
  are the campaign `14f7f7e7` (Lean `fe5fba6e`, #354) and `main` `b986b862` (#353).
- Plan: `campaign/closeout/W4-SYNC-NOTES.md`, as in #180. D5 (Seyoon, 2026-11-16): merge `main`
  into the campaign and replay; the campaign-to-`main` PR (W7) leaves `campaign/` and `devtools/`
  off `main`.

## What changes

- **Lean: 47 files from `main`, none in `TCSlib/Complexity`.**
  - 44 library files: BooleanAnalysis (Gaussian space, Borell), Cryptography/SecretSharing,
    InformationTheory and LearningTheory/PAC. 23 are new and 21 changed.
  - The root `TCSlib.lean`.
  - Two `webpage/Site` files, the documentation site (`import VersoBlog`), which is not a library
    module.
  - None of the 47 is changed by the campaign.
- **Other files from `main`:** the reorganized blueprint, the sharded dataset with its scripts and
  tests, `workflow.md` §4.1, the README and CI.
- **Conflicts (21 paths), resolved as the W4 notes planned:**
  - `campaign/` and `devtools/` (18 modify/delete paths): the campaign's trees, byte-identical to
    the campaign parent. `git diff 14f7f7e7 85b45d24 -- campaign devtools` is empty.
  - `AGENTS.md`: both appended blocks are kept. The campaign's block now states the 2026-11-17
    Lean parallelism rule, as `.claude/CLAUDE.md` does.
  - `blueprint/…/ClassNP/Tautology.tex` and `CookLevin/Hardness.tex`: `main`'s chapter structure
    with the campaign's entries, which match the campaign's Lean. The entry for
    `tautDualSegment_iff_segment` replaces `tautDual_segment_add`; the `clCount_*` entries, whose
    Lean the campaign removed, stay out. W5 regenerates both chapters.

## Evidence (`evidence/`)

- **`REPLAY.json`:** the merged-tree replay of the 44 library files' downstream closure on
  `oleans-cfe5fb` (the #354 merge's snapshot).
  - 134 modules: 134 passed, 0 failed.
  - Pool 3; peak memory 2.0 GB; 5 minutes.
  - **61 inherited admissions, all in BooleanAnalysis modules that come from `main` as they
    stand there** (`MODULE-RESULTS.json`). None is in `Complexity`.
- **`OBJECT-ACCOUNTING.json`:** 874 objects in and 898 out. 24 objects are added: main's 23 new
  modules, plus `BooleanAnalysis/GaussianSpace/Borell/Curvature`. Curvature existed before but
  nothing imported it, so the snapshot had no object for it. The other 44 changed objects are
  rebuilt modules. The driver (`driver.py.txt`) has two gate 156 changes: it accounts for such
  modules, and it seeds only `TCSlib/` files, so the site files are excluded.
- **Mathlib:** main's Borell files import `Mathlib.Analysis.Calculus.Deriv.Pi`, which the local
  cache lacked. It was fetched with the narrowed `lake exe cache get` for that one root
  (`fetch-roots.txt`, `cache-get.log`). The cache store was logged first (`cache-store.log`); the
  fetch downloaded 1 archive. `mathlib-roots.txt` lists the 80 Mathlib roots of the replayed
  modules.
- **No seals, controls, sweeps or copy screen.** No campaign proof changes.
