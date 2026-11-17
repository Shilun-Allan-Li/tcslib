# Gate 49 · resolutions, round 1 · CLEAR — Gate 49 (DW-11) closed

Codex: **CLEAR overall; #351 CLEAR; #352 CLEAR (with #365); #365 CLEAR**; 0 blockers, 0 majors, 4 minors (`findings-r1.md`).
BS-F01 and BS-F02 are regraded major *historically*, closed by LE-grp1 and repaired by #365 respectively.

| Finding | Grade | Resolution |
|---|---|---|
| G49-01 | minor (docs) | `Games/Relational.lean`'s module docstring and design r1 §2.2 overstate what the per-call hypothesis gives for an arbitrary relation (Codex's counterexample: it preserves equality of compatible test expectations, not a relation-supported coupling). **Scheduled in cleanup Stage 2's S2-A** (in-house; it touches `Games/`): reword the docstring; add a dated correction to design r1. Recorded in #351's description. |
| G49-02 | minor (docs) | `expect_sample_rel` gets `[BGZ09, §4.1, rule R-Rand]` with an adaptation note (finite sample types; expectation formulation). **Scheduled in S2-A** with G49-01. |
| G49-03 | minor (PR text) | **Fixed:** #351's and #352's descriptions now name Gate 49 (DW-11, superseding Q8), cite phase 2b as #352's merge-bound evidence (snapshot #3, 1422/1422; adopted as #4), and link the #365 repair. Commit messages unchanged. |
| G49-04 | minor (PR text) | **Fixed:** #365's description now calls it a proof/refactor change with one new public lemma and qualifies "proof-only" as applying to existing declarations. |

**Merge condition for #365:** its replay `olean-replay-grpfix` is built on `olean-replay-cs1-s6`, which became snapshot #7; if
#365 merges before any other Lean change, its merge's Lean equals tip × `5eaddd17` and the replay is adoptable as snapshot #8.
#365 is marked ready.
