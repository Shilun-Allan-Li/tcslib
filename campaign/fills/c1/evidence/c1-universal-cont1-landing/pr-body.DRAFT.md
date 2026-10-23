UN continuation 1 (`Diagonalization/NTimeHierarchy.lean`): **the universal NDTM's setup machine,
and `Turing.exists_timed_universal_NDTM` proved from the interpreter core**. The target now depends
on exactly `Turing.exists_ndInterpreterCore`, which is sorried in `NDCodeSimulator`; #151 proves
it. Megafill A's item 2, delivered complete (`fill-c1-universal-cont1.zip`).

**Commits** (on ⟨BASE: the campaign branch after #153⟩):
- `9031f1cf`, the delivery squashed to the owned file. Author kept (`C1 fill agent`); the subject is
  public-facing. It is `git diff 6cfee544..d72ed65f -- <the file>` (blob `8514e6db`), so the
  delivered `evidence/` tree stays out of the library;
- `34568b28`, the review's landing edits (blob `958751e1`, as the review checked them): A1 (F1), the
  decider's docstring restored; A2–A4, the status text and the target's `**Implementation.**`
  paragraph; A5–A7, three proof sketches; B1–B3 (F2), the `simp only` repair; C (F6), the lint
  cleanup. **The user ruled (2026-10-22): all four groups.**
- `3ed7b854`, the re-point (**the user's ruling: an API PR first, then this landing re-points**,
  IR-1). The setup's last phase is `Turing.inputRewindTM`, run through `inputRewindTM_run`. The
  private `un_inRewTM`, `un_inRew_run` (with A7's sketch) and `un_mapState_comp` are removed, and
  `un_step'` collapses its tag through `Cfg.mapState_mapState`. No statement changes.

**Review** (sub-agent; `campaign/fills/c1/reviews/universal-cont1/REVIEW.md`; "complete; land with
edits"):

| Check | Result |
|---|---|
| Integrity | 21/21 sums; the bundle's sole prerequisite the base; 7 commits; patches = bundle = file |
| Scope | first edit = overlay; home and body only; one import; 13 `un_` privates; no new public declaration or constant; BF's docstring restored (F1) |
| Elaboration | base and tip: 0 errors, `ntime_hierarchy`'s warning only (after C) |
| Axioms | `sorryAx` only through `exists_ndInterpreterCore`; `un_setup` standard |
| Seal | 36 definitions + the simp erasure, 80 controls; sealed and unsealed routes identical after B1–B3 |
| Probe | 95/95 (base, tip, in-module) |
| v3 screen | 603 → 616 declarations, 450 → 454 pairs; 4 new, none ≥ 90%; two cross-file pairs (F3: resolved by the re-point) |
| Lint | 0 FAIL; sweep 75/75, 26 → 25 |

**The maintainer's checks on the re-pointed file** (before #153's snapshot existed: the new
module's text followed by this file, imports merged, against `oleans-lu2sc1`):
- elaboration: only `ntime_hierarchy`'s `sorry` warning;
- the review's seal S2 extended by `Turing.inputRewindTM` (37 definitions, the simp erasure, 41
  controls at the top and at the end): the body has 0 errors and all 82 controls fail; unsealed,
  the controls close;
- freeze against `34568b28`: 5 → 5 public, statements unchanged; 14 → 11 private (the three
  removed); bodies changed in `un_setup` and `un_step'` only;
- lint: `Diagonalization` 0 FAIL, 2 WARN (as at review); no line over 100 characters;
- v3 screen (the brief's 11 files plus `Build/InputRewind`): 617 declarations, 454 pairs. Against
  the review's head screen, 4 pairs are gone and 4 are new:
  - gone: F3's two cross-file pairs (`un_inRewTM` with `xr_inRewindTM`), `xr_E_initCfg` ←
    `un_mapState_comp`, and the in-file `un_setup` → `un_mapState_comp` (87%);
  - new: #153's three (gate 65);
  - new: `un_setup` → `Cfg.mapState_mapState` (88%). This is `hstart`'s field-by-field proof of the
    start configuration through seven nested relabelings, the review's 87% in-file pair now
    pointing at the API. ⟨DECISION⟩
⟨AFTER #153: re-check against its snapshot⟩

**Order.** After #149 and #153. The closure is `Diagonalization/NTimeHierarchy` and the
`Diagonalization` facade (2 modules), chained from #153's merged-tree snapshot. **Pending.**

**Gate:** a fill gate (number at dispatch). **Pending.**

🤖 Generated with [Claude Code](https://claude.com/claude-code)
