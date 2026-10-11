# C1c fill report

**Complete: 10/10 targets and E1–E5.** No remaining private sorries, no proved-modulo dependencies, and no escalations. All seventeen required axiom prints exclude `sorryAx`. Only the three owned source files are changed.

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Campaign branch: `complexity/arora-barak-ch3-4`; local work branch: `fill/ch34-c1c`.
- Base: `29aa75bef39708af94cbd7fda4f0b84a4c488394`.
- Required ancestor: `44853c6f3177fed8f7f8d2288210593e9c094f7e`; `git merge-base --is-ancestor … HEAD` succeeded before edits.
- Delivery commit: `c8c3f5754564b11ef4df5af7b87b465ff6418e2f`. One local commit; no rebase, push, or PR.
- Binding brief: `briefs/ch34-c1-batchC.md` at the recorded base. The policy, workflow §4, plan §4e, both P3.1/P3.2 findings and resolutions, P3.2 pack item 6, and the pre-ship probe were read.

## Completed targets

Names below have namespace `Turing` except the two `Complexity` inclusions.

| Brief target | Declaration | Status |
|---|---|---|
| 1 | `OracleTM.toOracleNDTM_runWith` | Proved |
| 2 | `Complexity.P_subset_POracle` | Proved |
| 3 | `Complexity.POracle_subset_NPOracle` | Proved |
| 4 | `OracleTM.queriesWithin_length_le` | Proved |
| 5 | `OracleNDTM.length_le_of_mem_queriesAlong` | Proved |
| 6 | `OracleNDTM.runWith_eq_of_agree_length_lt` | Proved |
| 7 | `OracleNDTM.runWith_eq_of_agree_queriesAlong` | Proved |
| 8 | `OracleTM.runFrom_eq_of_agree_length_lt` | Proved |
| 9 | `OracleTM.runFrom_eq_of_agree_queriesWithin` | Proved |
| 10 | `OracleTM.length_le_of_mem_queriesWithin` | Proved |

## New declarations and proof routes

**Flagged new public surface:** exactly the prescribed E1–E5, immediately after target 1 in `OracleNondeterministic.lean`, with unchanged prescribed names and statements. Each has statement prose, a Proof sketch, and exactly one new module-docstring Main results bullet.

| Export | Declaration in `Turing.OracleNDTM` | Role |
|---|---|---|
| E1 | `fixChoice` | Deterministic oracle machine at a fixed choice bit |
| E2 | `stepWith_eq_fixChoice_step` | Reuses the single embedding-step comparison |
| E3 | `stepWith_eq_of_ne_qQuery` | E2 followed by deterministic oracle independence |
| E4 | `runWith_workTapes_invariant` | Initialized instance of the generalized branch invariant |
| E5 | `queryString_runWith_length_le` | E4 and the generalized blank-cell bound |

**Every new private declaration** is listed here; all are proved and have Proof sketches.

| File | Private declaration | Role |
|---|---|---|
| `OracleNondeterministic.lean` | `Turing.toOracleNDTM_stepWith` | The batch's only unfolding comparison of `stepWith` against `step`; halted/query/ordinary cases |
| `OracleNondeterministic.lean` | `Turing.runWith_headBlank` | Induction on the choice word from an arbitrary configuration and radius; cites the deterministic movement and write-locality lemmas through E2 |
| `OracleNondeterministic.lean` | `Turing.queryString_length_le_of_blank` | A blank query cell bounds extraction using `Nat.find_le` |
| `OracleAgreement.lean` | `Turing.OracleTM.step_eq_of_query_agree` | Core (i): query-answer agreement, with the public off-query lemma |
| `OracleAgreement.lean` | `Turing.OracleTM.runWith_take_eq_of_agree` | Core K: the single branch-prefix locality induction |
| `OracleAgreement.lean` | `Turing.OracleTM.runWith_take_replicate` | Core (iii): deterministic runs as prefixes of constant choice words, citing target 1 |
| `OracleAgreement.lean` | `Turing.OracleTM.runFrom_eq_of_query_agree` | Factors the constant-word specialization shared by targets 8 and 9; no second induction |
| `OracleAgreement.lean` | `Turing.OracleTM.length_le_of_mem_filtered_queries` | One filter-map membership argument for targets 5 and 10 |

Target 1 inducts on the choice word after the private step identity. E2 reuses that identity at `fixChoice`; no other per-step nondeterministic fact is re-proved by unfolding `stepWith`. E4's generalization advances the radius once and calls the induction hypothesis on the suffix. E5 uses the cell at the branch length as the blank witness.

The inclusions retain the exact multiplicative constant and exponent. Target 3 establishes one local equality for every branch of the input's budget, uses the replicated-false word for member acceptance, and excludes acceptance of a nonmember by its `[false]` output. There is no new declaration in `Classes.lean`.

K splits `take (s+1)` into `take s` and the next bit, uses `runWith_append`, identifies the prefix configurations, and transports core (i)'s conclusion by E2. The four locality targets all reuse K. The two deterministic targets share its constant-word specialization. The two membership bounds share a single index-extraction lemma. The query-count bound cites `List.length_filterMap_le` and `List.length_range`.

## Freeze and flagged documentation changes

- Imports: **none added or changed**, including Mathlib imports.
- All existing declaration signatures are preserved; no declarations were removed.
- All existing definitions and non-target proofs are unchanged. The four B1 statements, their proofs and docstrings form a byte-identical tail of `Classes.lean`.
- The diff is exactly the three owned sources: 305 insertions and 15 deletions.
- Flagged status changes: the embedding's module bullet changes “sorried” to “proved”; `OracleAgreement`'s Main results status becomes proved; `Classes`' Main results status records two proved inclusions and four remaining sorried B1 statements.
- Flagged sketch appendices: exactly one sentence on each of targets 8 and 9 records their shared branchwise induction along the constant choice word through target 1.
- Flagged module bullets: exactly one per export E1–E5, as listed above. Existing attribution text is unchanged.
- Machine construction: none. Out-of-scope sorries: untouched.

`evidence/freeze.log` records the executed checks; `evidence/check-freeze.py` reproduces them against a checkout at the delivery commit.

## Requested shared lemmas

1. Promote `queryString_length_le_of_blank` to `Oracle.lean`, preferably under `OracleTM`: for any configuration and natural cell index, a blank query-tape cell there bounds the extracted query length by that index. Re-derive the existing deterministic `queryString_length_le` from it. The local private proof is complete; `Oracle.lean` was not edited.
2. Optional: promote `step_eq_of_query_agree` to `Oracle.lean`. It packages agreement on the current query conditional on being in the query state, with deterministic off-query independence handling the other case.

Escalations: **none**. Proved-modulo set: **empty**.

## Verification

Lean 4.25.0; Mathlib revision `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. The cache was obtained with `lake exe cache get` for the closure's Mathlib roots. All source and axiom checks used `scripts/lean_check_tree.sh`; no direct `lake build` command was invoked.

Before changing the checkout, the complete 64-module order in `briefs/orders/ch34-c1c.txt` was bootstrapped: exit 0, zero errors, **35** sorry warnings. Each changed file was then checked with its later modules in order. The final combined sweep checked all eleven modules from `OracleNondeterministic` through the `Diagonalization` facade: exit 0, zero errors, **25** expected warnings. Exactly the ten targeted warning declarations disappeared; every other warning declaration is identical to the base, including downstream modules.

| Module | Base sorry warnings | Final sorry warnings |
|---|---:|---:|
| `OracleNondeterministic` | 1 | 0 |
| `ClassOracle/Classes` | 6 | 4 |
| `ClassOracle/SATOracle` | 3 | 3 |
| `ClassOracle` facade | 0 | 0 |
| `OracleAgreement` | 7 | 0 |
| `Diagonalization/EXPCOM` | 6 | 6 |
| `Diagonalization/Relativization` | 4 | 4 |
| `Diagonalization/NotTimeConstructible` | 1 | 1 |
| `NDCodes` | 1 | 1 |
| `Diagonalization/NTimeHierarchy` | 6 | 6 |
| `Diagonalization` facade | 0 | 0 |

The root `TCSlib` is excluded as instructed. Both lint commands exited 0:

```text
python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine
style_lint: 0 FAIL, 14 WARN over 46 files
python3 scripts/campaign_style_lint.py TCSlib/Complexity/ClassOracle
style_lint: 0 FAIL, 0 WARN over 2 files
```

The TuringMachine warnings concern existing large files; none concerns either modified oracle-machine file. `git diff --check` passes. The patch series was applied to an isolated index initialized at the base and reconstructed exactly the final Git tree `19bcf5c7e9d0c64396354be68f4ba974a2427071`. The incremental bundle verifies successfully and records the base as its prerequisite.

Environment note: this executor exposes different PID numbers through `getpid()` and procfs. The unmodified Lean binary initially failed to locate itself. `evidence/proc-exe-compat.c` supplies a narrow `readlink` compatibility shim mapping only `/proc/<this-process-pid>/exe` to `/proc/self/exe`; it changes neither Lean nor the checker script. Its source and the Lean binary/library hashes are included. On a normal Lean installation no shim is needed. The axiom probe was temporarily copied to the repository root for the check and then removed; it is archived only as evidence.

## Duplication disclosure

**new copies: none.** The required screen moves from **22 pairs / 2,562 reproduced characters** to **27 pairs / 3,048 characters**. All 22 old pairs remain unchanged. There are **zero new cross-file pairs**, including between owned files, and **zero new in-file pairs at or above 90%**. The five new directed in-file matches are fully disclosed below. These fractions are text-screen measurements, not counts of independent mathematical arguments.

| Target reproduces source, within one file | Shared fraction | Justification |
|---|---|---|
| `OracleAgreement.runWith_eq_of_agree_queriesAlong` → `runFrom_eq_of_agree_queriesWithin` | 88/135 = 65% | Both introduce membership with `mem_filterMap` at the queried index. They specialize different run interfaces and share the one underlying K induction. |
| `OracleNondeterministic.runWith_headBlank` → `OracleNDTM.stepWith_eq_of_ne_qQuery` | 79/137 = 58% | Repeated citations to E2. The invariant then cites head movement/write locality; E3 cites oracle independence. No per-step fact is re-derived. |
| `OracleAgreement.runWith_eq_of_agree_length_lt` → `runWith_eq_of_agree_queriesAlong` | 119/210 = 57% | The same K invocation and final `take_length` specialization, with different agreement premises. |
| `Classes.POracle_subset_NPOracle` → `P_subset_POracle` | 81/148 = 55% | Unpacking and repacking the same polynomial union and witnesses, for different embeddings. |
| `OracleAgreement.runWith_eq_of_agree_queriesAlong` → `runWith_eq_of_agree_length_lt` | 119/220 = 54% | Reverse direction of the K-wrapper text match above. |

The brief's permitted route adaptations are also disclosed below even though none reaches the screen's qualifying cross-file threshold. The generalized invariant and blank-cell bound were written directly from their routes, without transcribing their deterministic twins. The class proof follows the prescribed deterministic-to-nondeterministic argument at the exact input budget.

| Adapted target | Related source | Shared text / source body |
|---|---|---:|
| `Classes.POracle_subset_NPOracle` | `NTIME.toFinNDTM_haltsWithin_and_accepts_iff` | 184/587 = 31.35% |
| `OracleNondeterministic.OracleTM.toOracleNDTM_runWith` | `Nondeterministic.MultiTapeTM.toNDTM_runWith` | 51/129 = 39.53% |
| `OracleNondeterministic.toOracleNDTM_stepWith` | `Nondeterministic.MultiTapeTM.toNDTM_runWith` | 0/129 = 0% |
| `OracleNondeterministic.runWith_headBlank` | `Oracle.runFrom_workTapes_invariant` | 26/595 = 4.37% |
| `OracleNondeterministic.queryString_length_le_of_blank` | `Oracle.queryString_length_le` | 28/337 = 8.31% |

The screen command is exactly the brief's seven-file population, in the specified order. Both complete outputs follow.

### Before

```text
declarations screened: 55; copy pairs (target reproduces >= half of source): 22; reproduced text: 2,562 chars
   OracleNondeterministic.lean::AcceptsWithin  reproduces  NTIME.lean::AcceptsWithin: 109/109 = 100%
   OracleNondeterministic.lean::runWith_append  reproduces  Nondeterministic.lean::runWith_append: 100/100 = 100%
   Nondeterministic.lean::runWith_append  reproduces  OracleNondeterministic.lean::runWith_append: 100/100 = 100%
   NTIME.lean::AcceptsWithin  reproduces  OracleNondeterministic.lean::AcceptsWithin: 109/111 = 98%
   OracleNondeterministic.lean::stepWith  reproduces  Nondeterministic.lean::stepWith: 85/88 = 97%
   Oracle.lean::step  reproduces  Nondeterministic.lean::stepWith: 81/88 = 92%
   OracleNondeterministic.lean::HaltsWithin.mono  reproduces  Nondeterministic.lean::HaltsWithin.mono: 220/252 = 87%
   OracleNondeterministic.lean::runWith_of_halt  reproduces  Nondeterministic.lean::runWith_of_halt: 68/78 = 87%
   Nondeterministic.lean::runWith_of_halt  reproduces  OracleNondeterministic.lean::runWith_of_halt: 68/79 = 86%
   Nondeterministic.lean::HaltsWithin.mono  reproduces  OracleNondeterministic.lean::HaltsWithin.mono: 220/257 = 86%
   OracleNondeterministic.lean::OracleNDTM  reproduces  Oracle.lean::OracleTM: 141/175 = 81%
   OracleFinite.lean::FinOracleTM  reproduces  OracleNondeterministic.lean::FinOracleNDTM: 161/206 = 78%
   OracleNondeterministic.lean::FinOracleNDTM  reproduces  OracleFinite.lean::FinOracleTM: 161/219 = 74%
   Oracle.lean::OracleTM  reproduces  OracleNondeterministic.lean::OracleNDTM: 141/192 = 73%
   OracleNondeterministic.lean::stepWith  reproduces  Oracle.lean::step: 118/165 = 72%
   OracleNondeterministic.lean::AcceptsWithin.mono  reproduces  NTIME.lean::AcceptsWithin.mono: 143/207 = 69%
   Oracle.lean::step  reproduces  OracleNondeterministic.lean::stepWith: 118/175 = 67%
   NTIME.lean::DecidesInTime  reproduces  OracleNondeterministic.lean::DecidesInTime: 61/92 = 66%
   NTIME.lean::AcceptsWithin.mono  reproduces  OracleNondeterministic.lean::AcceptsWithin.mono: 143/220 = 65%
   OracleNondeterministic.lean::DecidesInTime  reproduces  NTIME.lean::DecidesInTime: 61/112 = 54%
   OracleNondeterministic.lean::FinOracleNDTM  reproduces  Nondeterministic.lean::FinNDTM: 77/150 = 51%
   OracleFinite.lean::FinOracleTM  reproduces  Nondeterministic.lean::FinNDTM: 77/150 = 51%
```

### After

```text
declarations screened: 76; copy pairs (target reproduces >= half of source): 27; reproduced text: 3,048 chars
   OracleNondeterministic.lean::AcceptsWithin  reproduces  NTIME.lean::AcceptsWithin: 109/109 = 100%
   OracleNondeterministic.lean::runWith_append  reproduces  Nondeterministic.lean::runWith_append: 100/100 = 100%
   Nondeterministic.lean::runWith_append  reproduces  OracleNondeterministic.lean::runWith_append: 100/100 = 100%
   NTIME.lean::AcceptsWithin  reproduces  OracleNondeterministic.lean::AcceptsWithin: 109/111 = 98%
   OracleNondeterministic.lean::stepWith  reproduces  Nondeterministic.lean::stepWith: 85/88 = 97%
   Oracle.lean::step  reproduces  Nondeterministic.lean::stepWith: 81/88 = 92%
   OracleNondeterministic.lean::HaltsWithin.mono  reproduces  Nondeterministic.lean::HaltsWithin.mono: 220/252 = 87%
   OracleNondeterministic.lean::runWith_of_halt  reproduces  Nondeterministic.lean::runWith_of_halt: 68/78 = 87%
   Nondeterministic.lean::runWith_of_halt  reproduces  OracleNondeterministic.lean::runWith_of_halt: 68/79 = 86%
   Nondeterministic.lean::HaltsWithin.mono  reproduces  OracleNondeterministic.lean::HaltsWithin.mono: 220/257 = 86%
   OracleNondeterministic.lean::OracleNDTM  reproduces  Oracle.lean::OracleTM: 141/175 = 81%
   OracleFinite.lean::FinOracleTM  reproduces  OracleNondeterministic.lean::FinOracleNDTM: 161/206 = 78%
   OracleNondeterministic.lean::FinOracleNDTM  reproduces  OracleFinite.lean::FinOracleTM: 161/219 = 74%
   Oracle.lean::OracleTM  reproduces  OracleNondeterministic.lean::OracleNDTM: 141/192 = 73%
   OracleNondeterministic.lean::stepWith  reproduces  Oracle.lean::step: 118/165 = 72%
   OracleNondeterministic.lean::AcceptsWithin.mono  reproduces  NTIME.lean::AcceptsWithin.mono: 143/207 = 69%
   Oracle.lean::step  reproduces  OracleNondeterministic.lean::stepWith: 118/175 = 67%
   NTIME.lean::DecidesInTime  reproduces  OracleNondeterministic.lean::DecidesInTime: 61/92 = 66%
   OracleAgreement.lean::runWith_eq_of_agree_queriesAlong  reproduces  OracleAgreement.lean::runFrom_eq_of_agree_queriesWithin: 88/135 = 65%
   NTIME.lean::AcceptsWithin.mono  reproduces  OracleNondeterministic.lean::AcceptsWithin.mono: 143/220 = 65%
   OracleNondeterministic.lean::runWith_headBlank  reproduces  OracleNondeterministic.lean::OracleNDTM.stepWith_eq_of_ne_qQuery: 79/137 = 58%
   OracleAgreement.lean::runWith_eq_of_agree_length_lt  reproduces  OracleAgreement.lean::runWith_eq_of_agree_queriesAlong: 119/210 = 57%
   Classes.lean::POracle_subset_NPOracle  reproduces  Classes.lean::P_subset_POracle: 81/148 = 55%
   OracleNondeterministic.lean::DecidesInTime  reproduces  NTIME.lean::DecidesInTime: 61/112 = 54%
   OracleAgreement.lean::runWith_eq_of_agree_queriesAlong  reproduces  OracleAgreement.lean::runWith_eq_of_agree_length_lt: 119/220 = 54%
   OracleNondeterministic.lean::FinOracleNDTM  reproduces  Nondeterministic.lean::FinNDTM: 77/150 = 51%
   OracleFinite.lean::FinOracleTM  reproduces  Nondeterministic.lean::FinNDTM: 77/150 = 51%
```

## Seventeen axiom prints

Every listed declaration uses at most `propext`, `Classical.choice`, and `Quot.sound`; `fixChoice` uses none.

```text
'Turing.OracleTM.toOracleNDTM_runWith' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.P_subset_POracle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.POracle_subset_NPOracle' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.OracleTM.queriesWithin_length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.OracleNDTM.length_le_of_mem_queriesAlong' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.OracleNDTM.runWith_eq_of_agree_length_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.OracleNDTM.runWith_eq_of_agree_queriesAlong' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.OracleTM.runFrom_eq_of_agree_length_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.OracleTM.runFrom_eq_of_agree_queriesWithin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.OracleTM.length_le_of_mem_queriesWithin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.OracleNDTM.fixChoice' does not depend on any axioms
'Turing.OracleNDTM.stepWith_eq_fixChoice_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.OracleNDTM.stepWith_eq_of_ne_qQuery' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.OracleNDTM.runWith_workTapes_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.OracleNDTM.queryString_runWith_length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.OracleTM.queriesWithin' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.OracleNDTM.queriesAlong' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Final sweep tail

The complete sweep, its exit status, and named warning-set comparison are included under `evidence/`.

```text
TCSlib/Complexity/Diagonalization/Relativization.lean:110:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/Relativization.lean:153:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/Relativization.lean:214:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/Relativization.lean:227:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/Diagonalization/NotTimeConstructible
TCSlib/Complexity/Diagonalization/NotTimeConstructible.lean:89:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine/NDCodes
TCSlib/Complexity/TuringMachine/NDCodes.lean:187:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/Diagonalization/NTimeHierarchy
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:121:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:146:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:191:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:287:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:301:8: warning: declaration uses 'sorry'
TCSlib/Complexity/Diagonalization/NTimeHierarchy.lean:326:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/Diagonalization
Final sweep exit: 0
```

## Archive contents

- `REPORT.md` and the three complete sources under their original `TCSlib/` paths.
- `patches/0001-Fill-C1c-oracle-embedding-class-inclusions-and-local.patch`, against the recorded base.
- `fill-ch34-c1c.bundle`, an incremental bundle requiring that base.
- `evidence/`: baseline and final sweeps, axiom probe/log, warning sets, both duplication outputs, adaptation measurements, lint logs, freeze/verification checks, patch/bundle checks, and environment provenance.
- `SHA256SUMS`, covering every other file in this archive.

The two verification scripts accept the checkout path as their first argument. No repository files outside the three owned sources are part of the commit.
