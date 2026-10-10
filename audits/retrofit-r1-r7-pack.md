# External audit pack — chapter-1/2 retrofit, epoch R1 boundary, round 7

Round 6 (`audits/retrofit-r1-r6-pack.md`, findings verbatim in
`audits/retrofit-r1-r6-findings.md`) closed R5-1, R5-2 and R5-3. It
reproduced the screen byte for byte and accepted the member/fragment rule
as an inclusive accounting convention. It held the gate on one major,
**R6-1**: `f2_counter_count_space` reproduces 80.3% of the **private**
`counter_count`, a source the residual pass did not screen because it
compared helpers with public proofs only.

This round's repair is wider than R6-1. The residual pass was public-only,
and the direct pass was limited to two files. Both were scope limits of the
same kind, and fixing them one round at a time is what has kept this gate
open. The screen is therefore now **exhaustive over Catalog's non-members
and its five source files**. It finds R6-1 and 19 further cross-file
adaptations. The gate closes on zero blockers and majors.

## Disposition table (verify each)

| Round-6 finding | Disposition |
|---|---|
| R6-1 (major: `f2_counter_count_space`) | **Repaired, with the scope limit behind it removed.** `f2_counter_count_space` is counted (80.3% of `counter_count`; 52 lines). The script's **pass 3** screens **all 124 Catalog non-members** against **all 530 declarations, public and private, of Composition, Primitives, TimeConstructible, Loop and Wrappers**. The non-members are Catalog minus the post-R6-1 299-member union, defined by name in the script. Pass 3 uses an exact 25-gram prefilter, which loses nothing because every tile is at least 25 characters, and prints every pair sharing at least 60 characters (R6-5's suggestion). **Like-for-like verdicts**: a proof is compared with proofs and a term with terms. A proof that spells out a definition's term is printed as a restatement and not counted. This matters once, for `a2_loop_prepare`: its 99.3% match with the *definition* `loopReady` is a restatement, and its real counterpart is the *proof* `loopHost_prepare`, at 86.8%. Pass 1 now covers every public `X` of all five files that has a Catalog `X_spaceUsed`; that is 19 eligible pairs, and Loop's `exists_loopTM` is the one new member. **19 further members result:** 4 F2A, 13 A2 and 2 public rows, itemized in the ledger's Catalog row. They add **6 new source-side members**: Primitives `emitterP2_control`; Loop `emLoop_run_prefix`, `exists_loopFindTM`, `exists_loopCfgTM`, `exists_loopTM`; Wrappers `computesFunInTime_cond`. **Flagged:** five A2 members reproduce just over half of one 129-character Loop proof (`emLoop_run_prefix`). They are counted because the rule requires it, and marked low-coverage. |
| R6-2 — R6-7 (verified closures and the rule assessment) | Carried. R6-4's caution is adopted: the ledger no longer describes any residual helper as free of copied material on the strength of a public-source screen. The remaining 20 F2A non-members are described only as sharing no member-level material with the five source files at the stated thresholds. |

## The in-file convention (stated explicitly; judge it)

Pass 3b lists **in-file** near-duplicates among the non-members: 109 pairs
over 62 targets. Thirteen exceed 90%, led by Catalog's own §12 sibling
machine rows (`transferTM` against `copyTM` 99.8%, and the
clear/compare/increment rows). These are public constructions, audited as
designed at the §12 and F1 gates. The ledger's standing convention, carried
through rounds 1–6, counts in-file **exact** copies (the 13 H3 copies and
the `a2_mapSumEquiv`/`a2_map_sum` pair) and **notes in-file near-duplicates
without counting them**. Pass 3b's pairs are recorded under that
convention. None is an exact copy, and their disposition is the 12.2c
per-theme split. If you judge that in-file near-duplicates must be counted,
say so. That would be further accounting inside the acknowledged D-R2
family; no new approval is needed.

## The resulting census (verify)

| File | Members | Fraction | Lines |
|---|---:|---:|---:|
| `Build/Catalog.lean` | **318** = 299 + 19 | **75.2%** (strict **283**, unchanged) | **7,539** = 6,543 + 996 |
| `Build/Primitives.lean` | **157** | **57.7%** | **3,415** |
| `Build/Loop.lean` | **108** | **50.9%** | prior + 268 (12 + 82 + 76 + 98) |
| `Build/Wrappers.lean` | **18** | **62.1%** | **337** |
| `ClassP/TimeConstructible.lean` | 20 (unchanged; `counter_count` was already counted) | 95.2% | 355 |
| `TuringMachine/Composition.lean` | 5 (unchanged) | 26.3% | 97 |

Decompositions:

- F2A: `306 = 150 + 94 + 10 + 3 + 20 + 2 + 7 adaptations + 20 nonmembers`.
- A2: `45 = 2 internal copies + 1 Loop copy + 13 adaptations + 29 nonmembers`.
- Catalog: `318 = 286 F2A + 16 A2 + 7 earlier redirect + 9 public counterparts`.
- Strict: `318 − 34 strengthened counterparts or adaptations − 1 near-copy = 283`.

## Brief for the auditor

1. Run the attached screen (`--spans`) against the attached sources and
   compare the result with the attached `.out`. **Loop and Wrappers are now
   attached** because pass 3 screens them.
2. Verify pass 3's population: 124 non-members against 530 source
   declarations. Check the like-for-like rule, including the
   `a2_loop_prepare` case, and the 19 new member verdicts. Sample the
   fragment and restatement verdicts.
3. Verify the census arithmetic, the spans, and the acknowledgment label,
   which now reads 318.
4. Judge the in-file convention above.
5. Confirm that no recorded correspondence, agent-declared copy, or screen
   candidate is outside the ledger; if one is, name it.
6. Report in the standard table, with findings verbatim into
   `audits/retrofit-r1-r7-findings.md`. The gate closes on zero blockers and
   majors, retiring epoch R1 and arming 12.2c.

## Repository-side attestations

Documentation-only delta. The six screened sources are byte-identical to
their state at the round-6 bundle commit. Loop and Wrappers are newly
attached at that same state.
