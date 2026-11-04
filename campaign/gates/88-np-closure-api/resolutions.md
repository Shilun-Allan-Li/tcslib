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
pinning `Reductions` `b5bfef1c`; precheck passed. **Running (user, 2026-11-04). Failed:** `ClassNP/TMSAT` (line 1089, unsolved goals)
and 7 modules behind it. `Reductions`' new import of `PClosure` brings `Mathlib.Tactic.Linarith`
(through `TuringMachine/CounterProgRun`) into `Reductions`' 85+ downstream modules; that activates
Mathlib's `@[simp] Nat.cast_min`, which rewrites the goal's `↑(min a b)` while the hypothesis `hw`
keeps it, so `TMSAT`'s unrestricted `simp [..., hw, ...]` no longer closes (the trap gate 82 hit
with #171). (The completed log: 127 modules, 33 failed, `TMSAT` and 32 that could not load its `.olean`; gate 88 round 2, minor 3.) **Ruled (user, 2026-11-04): the theorem moves to `PClosure`, and `TMSAT`'s step is
hardened in #177** (robust whatever the simp set). `Reductions` returns to the campaign's text; in
`PClosure`'s idiom the theorem is stated for preimages, `preimage_mem_NP` (beside
`preimage_mem_P`), so `PClosure` needs no import of `Reductions`. Gate 88 round 2 follows.

**Round 2** (`pack-r2.md`, at `a0d511ec`): `preimage_mem_NP` in `PClosure`, `TMSAT`'s step
hardened, `Reductions` the campaign's. Bundle SHA-256
`5ca648583c65e070d20f50b4df06d3e3b8e5c0fb52b454816fb10216816d816d` (46 sections), the records at
`34804ca4`. `replay-lnpc3` (66 modules from `oleans-lscp3`) written, precheck passed; **passed (user,
2026-11-04): 66 of 66 at `a0d511ec`, 0 failed, static-equal (0 sorries)**; snapshot `oleans-lnpc3`
(`evidence/round1-fix/merged-tree/replay-lnpc3.log`). **Staged
(2026-11-04); dispatched (user, 2026-11-04).** **Findings** (`findings-r2.md`, verbatim, SHA-256
`82b7d857f2fee138443920207ce73d15dad25e1e1bfe01565d583808ad732346`; received 2026-11-04): **PASS,
0 blockers, 0 majors, 3 minors, 10 notes.** The gate closes.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | The attached head lint logs predate the final proof sketch. | **True; erratum.** Fresh logs at `a0d511ec`, each with the commit and exit status (`evidence/round2-resolution/`): the policy linter 0 findings on `PClosure` (exit 0) and 9 on `TMSAT` (exit 1, the inherited ones); `ClassNP` 0 FAIL, 17 WARN over 21 files (exit 0), `TMSAT` at 1,736 lines, 6 public and 74 private. The dispatched pack is kept as dispatched. |
| 2 | minor | Round 2 omits the compiler-generated public-constant census (`workflow.md` §4). | **True; recorded.** An environment census (`evidence/round2-resolution/CensusPClosure.lean.txt`, `CensusTMSAT.lean.txt`, run against `oleans-lscp3` and `oleans-lnpc3`): `PClosure` 22 → 24 non-private constants, the new `Complexity.preimage_mem_NP` and its compiler auxiliary `Complexity.preimage_mem_NP._simp_1_1` (a generated simplification theorem); `TMSAT` 14 → 14, the same names. The source-declaration counts stand (16 → 17 and 6 → 6). No Lean change. |
| 3 | minor | The PR description and the resolutions undercount `replay-lnpc2`'s failures (7, not 32 behind `TMSAT`). | **True; fixed.** "7" was the interim count while that replay ran. The completed log: 127 modules, 33 failed, `TMSAT` itself and 32 that could not load its `.olean`. #177's description is corrected (2026-11-04); this file's round-1 narrative is annotated below. |
| 4 | note | Integrity and substantive scope are verified. | Agreed. |
| 5 | note | The statement is NP's closure under total polynomial-time preimages, with no missing hypothesis. | Agreed. |
| 6 | note | Both directions and the enlarged certificate bound are correct, adversarial instances included. | Agreed. |
| 7 | note | A rule-10 consumer starting from `L ≤ₚ L'` cannot unpack it sealed: `Reductions` has no `_iff` or witness lemma for `PolyTimeReducible`. | Agreed. Backlog: publish `polyTimeReducible_iff` in `Reductions` before a sealed consumer needs it. H states its padding reduction by its function and membership equivalence, so it cites `preimage_mem_NP` directly. |
| 8 | note | The move avoids round 1's import-environment expansion; importers of `PClosure` gain the theorem and its auxiliary. | Agreed, with that reading of "nothing else's environment changes". |
| 9 | note | `TMSAT`'s hardened step is correct and removes the `Nat.cast_min` hazard. | Agreed; the robustness claim is narrowed to that hazard, not every simp-set change. |
| 10 | note | Elaboration, axioms and the scoped rule-10 checks reproduce. | Agreed. |
| 11 | note | The new pair is API reuse; the all-ref search reproduces. | Agreed. |
| 12 | note | Leaving `TMSAT`'s inherited lint findings to the deferred cleanup is acceptable; two are parser false positives. | Agreed; the two false positives (lines inside a docstring that the linter reads as declarations) are added to the deferred cleanup's inventory. |
| 13 | note | The 66-module replay is an outstanding merge condition. | **Done.** `replay-lnpc3` passed (66 of 66 at `a0d511ec`, static-equal; above), before these findings arrived. |

**Merge state. #177: not yet clear to merge** (2026-11-04): it waits for gate 88's round 2 and
`replay-lnpc3` (`replay-lnpc2` failed and no longer applies).
`replay-lnpc3` has since passed (2026-11-04); #177 waits for gate 88's round 2 and, after #176's merge,
the overlap replay below.

**Ruled (user, 2026-11-04): #176 merges before #177.** Their downstream closures share
`NTimeHierarchy` and `Diagonalization`, so after #176 merges, #177 takes the campaign merged in and
a merged-tree replay of the overlap from `oleans-lnpc3`: `NTimeDiagonalizer` (#176's) and its 2
downstream modules.

**Re-ruled (user, 2026-11-04, after round 2 passed): #177 merges first.** `replay-leqc2` (#176 from
`oleans-lscp3`) had not run, so merging #177 first leaves one replay instead of two: #176 then takes
the campaign merged in and its 3 modules replayed from `oleans-lnpc3`. **#177: clear to merge** at
`a0d511ec61b2e40b2216e44c07278531fc33a2e6` (2026-11-04): the gate passed, `replay-lnpc3` passed at
that head, its base is the campaign branch, and the campaign has had no Lean change since
`oleans-lscp3`'s tree.
