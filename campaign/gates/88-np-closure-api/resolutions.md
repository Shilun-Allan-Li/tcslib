# `NP` is closed downward under `≤ₚ` (PR #177, an API gate): resolutions

**Gate, round 1:** the API gate of PR #177 (`lean/np-closure` at `ce00b6d3`). Pack `pack.md`; bundle
SHA-256 `4ccd459ec5da8f5ec44228cf7b230b473b151328763e5e1681e8a8919677632b` (37 sections), the Lean at
`ce00b6d3d7ca57501bf66eb949a05b90d90f0452`, the records at `c63f9dce`. **Staged (2026-10-27); dispatched
(user, 2026-11-03).** **Findings** (`findings.md`, verbatim, SHA-256
`802851d919dfc260a23f599a30624871cfbf1416826e2c5d6a125cc9941b7691`; received 2026-11-04): **PASS,
0 blockers, 0 majors, 2 minors, 10 notes.** The gate closes.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | The attached head lint logs are stale: taken at `bfc2a395`, before `prefixTM_copy`'s sketch (`ce00b6d3`). | **True; erratum.** Fresh logs at `ce00b6d3`, with the commit and exit statuses (`evidence/round1-lint/`): the policy linter 0 findings on `Reductions` (exit 0); `ClassNP` 0 FAIL, 16 WARN over 21 files (exit 0), the base's warnings, `Reductions` at 534 lines, 11 public and 16 private. The shipped pack is kept as dispatched. |
| 2 | minor | The public-constant census omits the compiler-generated `Complexity.mem_NP_of_polyTimeReducible._simp_1_1`: 14 → 16 non-private constants. | **True; recorded.** The non-private constants go 14 → 16: the theorem and its generated simplification auxiliary `_simp_1_1` (from the proof's `simp only`), which is not a source declaration and adds no axiom. Source declarations: 10 → 11 public, as stated. |
| 3 | note | Integrity and scope verified. | Agreed. |
| 4 | note | The statement is ordinary downward closure, with no missing hypothesis. | Agreed. |
| 5 | note | The verifier, the bound and both directions are correct. | Agreed. |
| 6 | note | Boundary cases and the oversized-certificate attack are handled. | Agreed. |
| 7 | note | Elaboration, axioms and the rule-10 seal reproduce. | Agreed. |
| 8 | note | The new screen pair is API reuse. | Agreed; the idiom disposition stands. |
| 9 | note | The home and the import cost are acceptable. | Agreed. |
| 10 | note | `prefixTM_copy`'s sketch is accurate. | Agreed. |
| 11 | note | No competing declaration; the 112-ref count lacks a ref manifest. | Agreed; future all-ref searches record each ref's name and object id. |
| 12 | note | The replay remains a merge condition; the overlap with #175 needs a merged-tree replay. | Agreed. #175 merged first (2026-11-03), so #177's merge needs the merged-tree replay `replay-lnpc2`, from `oleans-lscp3`, in place of `replay-lnpc`.

**The replay:** `replay-lnpc.sh` (`evidence/merged-tree/`), 86 modules from `oleans-lnfapi4`, pinning
`Reductions` `b5bfef1c`; precheck passed. **Not yet run.** Its closure overlaps #175's; whichever of
the two merges second takes a merged-tree replay of the overlap.

**The merged-tree replay:** `replay-lnpc2.sh` (`evidence/merged-tree/`): the campaign (after #179 and
#175) merged into #177 by `2c213708`; `Reductions`' downstream, now 127 modules, from `oleans-lscp3`,
pinning `Reductions` `b5bfef1c`; precheck passed. **Running (user, 2026-11-04).**

**Merge state. #177: not yet clear to merge** (2026-11-04): gate 88 passed; it waits for
`replay-lnpc2`.
