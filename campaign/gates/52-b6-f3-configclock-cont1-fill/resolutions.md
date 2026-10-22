# B6 F3 continuation 1 (PR #134, a fill gate): resolutions (round 1; gate CLOSED)

**Gate:** the fill gate of PR #134 (`lean/b6-f3-cont1-partial` at `c2c53ee5`): six private
components of the configuration-clock runner `Turing.exists_configWindowRunnerTM` in
`SpaceComplexity/WindowClock.lean` (`cw_field_total`, `cw_record_clock`, `cw_leftTM`,
`cw_left_run`, `cw_copy_constant`, `cw_clear_patch`); the target stays `sorry` (a partial). Pack
`pack.md`; bundle SHA-256 `972806574c70a20165c9e02a9027752562191a685bf7eed1aa87e685e3c1d2a4`
(21 sections; folder `52-b6-f3-configclock-cont1-fill-gate/`). Replay passed (user, 2026-10-21):
2 of 2, static-equal (1).

**Round 1** (`findings.md`, verbatim; received 2026-10-21): **PASS, 0 blockers, 0 majors, 1 minor,
12 notes. The gate is closed.** The maintainer's review sub-agent verified every finding at
`c2c53ee5`: all true, at the auditor's severities (`evidence/round1-review/REVIEW.md`). The audit is
evidence-based: the auditor reproduced the source, patch and freeze checks and inspected the logs,
without rerunning Lean. The review re-elaborated the merged head against `oleans-l134` (the target's
warning only), re-ran the 17-definition seal (passes; the control fails as intended) and the axiom
prints (equal to the delivery review's).

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 8 | minor | Documentation synchronization: the Route A sketch's present-tense `copyTM`/`scanTM` construction (`W := c_M · L`) is not the field-cell construction being developed, and a blank-separated record is not one delimited word for those rows; the PR body still calls E2's ruling "pending". | **True; fixed** in `189b7115` (`evidence/round1-review/fix/minor8-plus-optional-wording.diff`), docstrings only: blob `3c49ffb4` → `b50cdbb1`, 452 → 458 lines. With it, `cw_left_run`'s docstring says the move *keeps* the native input position (it never moved it; "restores" was the review's optional wording fix). The Route A paragraph (lines 383–393) is frozen text, byte-identical to the base `dac6b3b0`; the fix is in the Implementation status paragraph this landing introduced. It states that the clock these lemmas prepare is Route A's over field cells (`W = c · F ≤ c · L`), copied one field at a time with the blank separators skipped, and that the sketch's whole-layout construction is an alternative, not implemented, that would also have to handle the separators (`joinFields` intercalates a blank; `copyTM`, `copyMapTM` and `scanTM` read one blank-delimited word). Checks (`evidence/round1-review/out/08-*`, on the same blob `b50cdbb1`): applies to `c2c53ee5`; elaborates against `oleans-l134` with exactly the head's one diagnostic, the target's sorry warning (line 420 → 426); comment-stripped code unchanged, so the freeze and the v3 screen (which strips comments) are unchanged; `SpaceComplexity` lint 0 FAIL, 81 WARN over 107 files; no line over 100; no campaign label. **The PR body is replaced:** E2 ruled B (user, 2026-10-18: `Turing.wordPatch_append`, PR #139, gate 56); the Route A sentence corrected (a valid width, not the construction in use); the claim that the status paragraph named `W = c · F` and `copyMapTM` is now true. **Deferred:** rewording the frozen Route A paragraph itself, with its labels ("S1b's plan, design §12.8a §4 step 5"; "proved today; the RD-3 gate's minor 3"), to the docstring-cleanup pass. |
| 4 | note | The constant copy is correct; the following skip also needs the writer's blank-suffix invariant (the delivery review's "the cell past the written run is blank" uses route context). | **True; carried** to continuation 2's brief (the per-field round assumes the clock blank from the write position on and re-establishes it at `p + |f|`). **Records:** the delivery review's sentence holds under the blank clock precondition and append-only writes, not from `cw_copy_constant` alone (counterexample `w = [e]`, destination cell 1 nonblank); the review is kept as written. |
| 5 | note | The clear is correct; first-return and intermediate head/output clauses must still come from the public row APIs. | **True; carried:** `cw_copy_constant` and `cw_clear_patch` export only their rows' endpoints; the seams' cuts and the head envelopes come from `copyMapTM_run_ofCfg`'s and `clearTM_run_ofCfg`'s further clauses (or the helpers are extended); at F2's endpoint `cw_clear_patch`'s hypothesis comes from the writer's blank exterior and `w'.length = w.length`. |
| 9 | note | The target remains a construction obligation: writer, embedding, dispatch, composed first-return/silence/space proofs and the common constant. | **True; carried:** one constant for time, heads and space; silence and space proved for the composite; at pre-ship, the published route to the writer's intermediate output clause is confirmed. The partial status stays until the target is proved. |
| 6 | note | E2 was real but no blocker; follow the recorded ruling; #139's theorem is not proved by this landing. | **True. No action here:** continuation 2's draft cites `wordPatch_append` (#139, gate 56); #134's PR body now records the ruling (minor 8). |
| 10 | note | The execution attestations are supported by the records; not a fresh replay by the auditor. | **True. No action:** recorded above as an evidence-based audit. |
| 1–3, 7, 11–13 | notes | Integrity and the freeze; the clock arithmetic and the per-machine pass count; the leaf; rule 10 and MIG-1; the screen and lint; the merged-tree replay; notation. | **True. No action.** Note 7: the frozen bridge's `unfold FinTM.configBound` predates rule 10 and is on gate 34's unfold-site scan. |

**Carried to F3 continuation 2's brief** (`evidence/round1-review/fix/cont2-draft-carryforwards.diff`):
the clock's blank suffix (note 4); cuts and envelopes, and the clear's hypothesis at F2's endpoint
(note 5); the Route A sketch's whole-layout writer is an alternative not in use, and region (c)
keeps a note of the construction used (minor 8); one constant, silence and space, and the pre-ship
check of the silence route (note 9); the frozen bridge's `unfold` is outside the seal (note 7);
the issue-time line numbers.

**Re-replay for the fix:** pending (`evidence/replay-l134b.sh`: the same 2 modules from `oleans-l132b`,
pin `WindowClock.lean:b50cdbb19b1ac9c6018c074d25a7358c8f95b826`). The PR body is replaced
(`evidence/round1-review/fix/pr-body-B-with-docstring-commit.md`, with `189b7115` filled in).
