# Gate 152 resolutions

Round 1 CLEAR: 0 blockers, 0 majors, 2 minors, 6 notes (`findings.md`, verbatim). The
dispatched pack and evidence are preserved; the errata below correct the live records.

- **G152-01 (minor), records erratum.** The base file has 9,031 lines, not 9,032; the maintainer's
  count included the trailing newline as a line. The net change is **−211** Lean lines
  (+218/−429). Corrected: the PR description, `duplication-ledger.md`, `R3-R6-MEASUREMENT.md` and
  `HANDOFF.md`.
- **G152-02 (minor), records erratum.**
  - The two new screen matches are proof-text similarities, not shape matches of statements.
    `us_start` proves an initial-configuration identity and does not call `phaseHostTM_run`; its
    match is the five configuration-field rewrite fragments. The `canonStageFrontSpec` match is
    the host call and field rewrites.
  - The legs' consumer is `canonStageFrontSpec`; `canonStage_run` does not exist. The pack's
    §Scope and the design note named it wrongly.
  - Corrected: `evidence/PAIR-DISPOSITIONS.corrected.json` (the dispatched
    `PAIR-DISPOSITIONS.json` is kept) and `campaign/closeout/CC7-1-DESIGN.md`.
- **G152-N5, the stop rule's convention.** It was applied as an average over the two prototype
  legs: leg 0 saved 33 lines and leg 1 saved 48, so (33 + 48) / 2 = 40.5. The earlier hand-written
  leg 1 checkpoint (81 → 34) met the threshold alone. Seyoon's ruling did not specify per-leg or
  average; recorded here.
- Notes N1–N4 and N6: no action.
- **Merge condition.** The gate's replay is the merged-tree replay. It ran against records tip
  `c9c51a73` (campaign Lean `fb6f2e31`), and the campaign's Lean has not changed since. Its output
  `oleans-cl152-cfb6f2` becomes the snapshot when #345 merges unchanged. **Clear to merge: #345.**
