# C1d — complete delivery

**6/6 targets filled; R1–R6 complete.** Five targets are admission-free. The PSPACE collapse is proved **modulo `Complexity.P_subset_PSPACE`**, exactly as the brief sanctions. No new helper contains `sorry`; all eleven out-of-scope admissions in the owned files remain untouched.

Base: `29aa75bef39708af94cbd7fda4f0b84a4c488394`, freshly cloned from **`complexity/arora-barak-ch3-4`**, not main. Working branch: `fill/ch34-c1d`. Before editing, `git merge-base --is-ancestor 44853c6f3177fed8f7f8d2288210593e9c094f7e HEAD` returned 0. **No rebase, push, or PR.**

| Commit | Scope |
|---|---|
| `0d927925` | Targets 1–5, completed, verified and delivered as a ZIP checkpoint before starting R1. |
| `5f492937c7f901b55a4c8888a7985d09415e3641` | Target 6, completing R1–R6. |

The binding brief, policy, workflow §4, plan §4e, all three required resolution files, the quoted audit routes, and the pre-ship probe and output were read. The final diff touches **only the six owned files**. All existing non-target declarations and all six target signatures are byte-identical after comment stripping; there are no removals, existing-declaration reorderings, or new public declarations.

## Targets and proof citations

| Target | Result | Binding route and citations |
|---|---|---|
| `Complexity.QBF.decode_encode` | Proved | Quantifier cases; `Turing.pairDecode_pairEncode`, `List.map_map`, `Std.Sat.CNF.decode_serialize`, `List.map_id''`. |
| `Complexity.QBF.truth_exPrefix_iff_satisfiable` | Proved | Q1 forward induction without coverage; Q2 update agreement using `Function.update_self` and `Function.update_of_ne`; Q3 backward induction using `Complexity.eval_congr_of_lt_numVars`. Assembly starts from the false assignment at index zero. |
| `Complexity.Game.determined` | Proved | G1 fixed player-one terminal/OR/AND value; G2 history as iteration via `Function.iterate_succ_apply'`; G3 greedy strategies; **one G4 induction for both target bits**, peeling with `Function.iterate_succ_apply`; G5 cases on the root value. |
| `Complexity.PSPACE_eq_P_of_pspaceComplete_mem_P` | Proved modulo `P_subset_PSPACE` | `Set.Subset.antisymm`, `Complexity.mem_P_of_polyTimeReducible`, `Complexity.P_subset_PSPACE`. |
| `Complexity.LogspaceReducible.polyTimeReducible` | Proved | Unchanged reduction witness and membership equivalence, citing `Complexity.ImplicitlyLogspaceComputable.polyTimeComputable`. |
| `Complexity.exists_finOracleTM_enumeration` | Proved | R1 state transport via `Action.mapState`, `Cfg.mapState_apply`, equivalence injectivity and `apply_ite`; **one step proof**, then `Function.Semiconj.iterate_right`, and `Option.map_eq_none_iff`. R2 `Fintype.ofInjective`, constructor injectivity and function extensionality. R3 three-state default. R4 explicit-instance `Fintype.equivFin`, `Nat.unpair_pair`, `Fin.isLt`, `dif_pos` and `Equiv.symm_apply_apply`. R5 repetition coordinate. R6 `Nat.right_le_pair`, R4 completeness and R1 behavioral transfer. |

## Every new declaration

All 24 declarations below are **private**. None contains an admission.

| File | Declaration | Role |
|---|---|---|
| `Formulas/QBFEncoding` | `quantOfBit_quantBit` | Quantifier round trip. |
| `Formulas/QBF` | `satisfiable_of_exPrefix` | Q1: forward induction, with no coverage hypothesis. |
| `Formulas/QBF` | `update_prefix_agreement` | Q2: one update extends agreement below the prefix boundary. |
| `Formulas/QBF` | `exPrefix_of_satisfying` | Q3: backward induction, using coverage only at the matrix base case. |
| `ClassPSPACE/Games` | `positionValue` | G1: fixed player-one value. |
| `ClassPSPACE/Games` | `ply` | G2: one prescribed move. |
| `ClassPSPACE/Games` | `playOut_succ_ply` | Single definitional successor equation. |
| `ClassPSPACE/Games` | `playOut_eq_iterate` | G2: play history equals iteration from the empty history. |
| `ClassPSPACE/Games` | `firstGreedy` | G3: player-one choice from the true child's remaining value. |
| `ClassPSPACE/Games` | `secondGreedy` | G3: negation of the same look-ahead. |
| `ClassPSPACE/Games` | `winner_of_value` | G4: one induction along play, generic in the target bit. |
| `Diagonalization/Relativization` | `oracleRelabel` | R1: generic-alphabet state relabelling. |
| `Diagonalization/Relativization` | `oracleRelabel_wellFormed` | R1: preservation of distinguished-state inequalities. |
| `Diagonalization/Relativization` | `oracleRelabel_step` | R1: sole step commutation, including query and halted cases. |
| `Diagonalization/Relativization` | `oracleRelabel_runFrom` | R1: arbitrary-start run transport by semiconjugacy iteration. |
| `Diagonalization/Relativization` | `oracleRelabel_computesInTime` | R1: all-oracle, all-input/output/horizon verdict equivalence. |
| `Diagonalization/Relativization` | `CanonTab` | R2: well-formed canonical binary-table subtype. |
| `Diagonalization/Relativization` | `canonTabFintype` | R2: the sole named finiteness structure, via the field-tuple injection. |
| `Diagonalization/Relativization` | `oracleDefault` | R3: well-formed three-state fallback. |
| `Diagonalization/Relativization` | `oracleTableAt` | R4: rank lookup with overflow fallback at explicit coordinates. |
| `Diagonalization/Relativization` | `decodeOracleTable` | R4: the decoder using the prescribed three unpaired coordinates. |
| `Diagonalization/Relativization` | `decodeOracleTable_rank` | R4: completeness at each canonical table's rank. |
| `Diagonalization/Relativization` | `oracleEnumeration` | R5: family forgetting the repetition coordinate. |
| `Diagonalization/Relativization` | `oracleEnumeration_pair` | R5: repetition equation. |

R6 is the existing public target's proof body, not a new declaration. `oracleTableAt` factors the branch of the prescribed decoder so pairing simplification occurs before dependent table selection; it changes neither the coordinates nor the selected machine. Every table cardinality and rank explicitly receives `canonTabFintype`; no table cardinality is evaluated. `synthInstance.maxSize 1024` is scoped to that one declaration. There is no section-level `open Classical`.

## Imports, requested shared lemmas, and prose changes

**One sanctioned import:** `TCSlib.Complexity.SpaceComplexity.Inclusions` was added to `ClassPSPACE/TQBF.lean`. **No Mathlib imports** were added. TQBF's other four theorem bodies are unchanged.

**Requested shared lemmas:** the five-member R1 family (`oracleRelabel` through `oracleRelabel_computesInTime`) and R2's `CanonTab`/`canonTabFintype` finiteness API. Proposed home: **`TCSlib/Complexity/TuringMachine/Oracle.lean`**. They remain private here; promotion waits for a second consumer. No shared file was edited.

**Flagged status-only changes:**

- Pending tags removed from the five previously tagged filled-target docstrings; TQBF's collapse instead records its `P_subset_PSPACE` modulo dependency. The enumeration had no pending tag to remove.
- QBF, QBFEncoding and Games module headings no longer label their results sorried.
- TQBF and Logspace/Reductions headings now say four statements remain sorried; Relativization says three remain.

**Flagged sketch appendices, original sketches and citations preserved:**

- QBF: the forward induction returns its final total assignment without coverage or evaluation transport; the backward induction alone uses the coverage bound.
- Enumeration: all state counts are represented, with the prescribed fallback on invalid ranks; `oracleTableAt` exposes the coordinate arguments; all table ranks share one finiteness structure; runs use `Semiconj.iterate_right`, and recurrence uses `Nat.right_le_pair`.

**Escalations: none.** No statement, attribution, existing definition, other proof body, or out-of-scope admission was changed.

## Verification

Lean **4.25.0** and the unchanged mathlib pin **`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`** were used. Dependencies were obtained with `lake exe cache get`; **every proof check used the unchanged `scripts/lean_check_tree.sh`**. No direct `lake build` command was used.

The exact 106-module bootstrap order was completed before editing. Module 35, CodeParser, crashed once with a bus error and no fresh olean; the same source passed a fresh retry, and the order resumed at module 36. The original failure and successful retry logs are retained. The completed baseline contains **91 sorry warnings**, **17 in the owned files**. The launcher/process-path compatibility shim, dependency extraction settings, and temporary axiom-probe placement are documented in `evidence/environment.md`; the Lean compiler, kernel and dependency sources were not modified.

**Final replay:** six owned modules, followed by all six downstream modules in their prescribed dependency order, root `TCSlib` excluded. **Zero errors, fresh oleans throughout.** The six downstream modules are `ClassPSPACE`, `Diagonalization`, `Formulas`, `SpaceComplexity`, `Logspace/Path`, and `Logspace/ImmermanSzelepcsenyi`. Their identities were independently checked against the transitive import graph.

The final warning set is **exactly the baseline affected set minus the six targets**: **11 owned out-of-scope admissions plus 5 unchanged downstream admissions**. No new helper admission. The independent warning comparison, freeze check, exact duplication-pair comparison, and eight-print axiom check all pass.

### Retained owned admissions

| Module | Declarations |
|---|---|
| `ClassPSPACE/TQBF` | `exists_adjacency_codec_cnf`, `TQBF_mem_PSPACE`, `TQBF_PSPACEHard`, `TQBF_PSPACEComplete` |
| `Diagonalization/Relativization` | `unaryWitnessLang_mem_NPOracle`, `exists_oracle_ne`, `baker_gill_solovay` |
| `SpaceComplexity/Logspace/Reductions` | `ImplicitlyLogspaceComputable.comp`, `LogspaceReducible.trans`, `mem_LOGSPACE_of_logspaceReducible`, `NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE` |

### Final owned sweep tail

```text
TCSlib/Complexity/Diagonalization/Relativization.lean:407:8: warning: declaration uses 'sorry'
PASS TCSlib/Complexity/Diagonalization/Relativization
CHECK 6/6 TCSlib/Complexity/SpaceComplexity/Logspace/Reductions
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:89:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:99:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:119:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/Reductions.lean:143:8: warning: declaration uses 'sorry'
PASS TCSlib/Complexity/SpaceComplexity/Logspace/Reductions
PASS final-owned: 6 modules; elapsed 12.5s
```

### Final downstream sweep tail

```text
PASS TCSlib/Complexity/SpaceComplexity/Logspace/Path
CHECK 5/6 TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:80:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:93:8: warning: declaration uses 'sorry'
TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi.lean:112:8: warning: declaration uses 'sorry'
PASS TCSlib/Complexity/SpaceComplexity/Logspace/ImmermanSzelepcsenyi
CHECK 6/6 TCSlib/Complexity/SpaceComplexity
PASS TCSlib/Complexity/SpaceComplexity
PASS final-downstream: 6 modules; elapsed 7.1s
```

### Axiom prints and modulo diagnostics

```text
'Complexity.QBF.decode_encode' depends on axioms: [propext, Quot.sound]
'Complexity.QBF.truth_exPrefix_iff_satisfiable' depends on axioms: [propext, Quot.sound]
'Complexity.Game.determined' depends on axioms: [propext, Quot.sound]
'Complexity.PSPACE_eq_P_of_pspaceComplete_mem_P' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.LogspaceReducible.polyTimeReducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.exists_finOracleTM_enumeration' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.P_subset_PSPACE' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Complexity.mem_P_of_polyTimeReducible' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The **modulo set is exactly `{Complexity.P_subset_PSPACE}` for target 4**. Its diagnostic contains `sorryAx`; `mem_P_of_polyTimeReducible` stays within the standard triple. Every other target, including the enumeration, stays within `[propext, Classical.choice, Quot.sound]`.

### Lint

In order: Formulas, ClassPSPACE, SpaceComplexity/Logspace, Diagonalization.

```text
style_lint: 0 FAIL, 0 WARN over 5 files
style_lint: 0 FAIL, 0 WARN over 2 files
style_lint: 0 FAIL, 0 WARN over 4 files
style_lint: 0 FAIL, 0 WARN over 4 files
```

## Duplication governance

**new copies: none**. There are **zero new cross-file pairs and zero new in-file pairs**. Both runs have the same 18 pairs, the same fractions and 3,831 reproduced characters. The screened count changes from 136 to 158 as filled bodies and private helpers become eligible. All listed pairs are inherited and unchanged.

None of the three pre-named exceptions is triggered: no new R1-step/plain-step pairing, R1-transfer/`exists_codeTM` pairing, or collapse-corollary pairing. The R1 run lemma does not pair with `runFrom_comm_of_step`. There is no new in-file pair requiring justification or factoring. Each proof’s actual citations are listed in the target table and helper inventory above.

### Before

```text
declarations screened: 136; copy pairs (target reproduces >= half of source): 18; reproduced text: 3,831 chars
   Oracle.lean::step  reproduces  Deterministic.lean::step: 84/87 = 97%
   Deterministic.lean::step  reproduces  Deterministic.lean::outputSymbol: 76/86 = 88%
   Deterministic.lean::outputSymbol  reproduces  Deterministic.lean::step: 76/87 = 87%
   Encoding.lean::pairDiag_double  reproduces  Encoding.lean::pairDiag_copy: 398/475 = 84%
   CNFEncoding.lean::parseClauses_bounds  reproduces  CNFEncoding.lean::parseClause_bounds: 731/920 = 79%
   Oracle.lean::step  reproduces  Deterministic.lean::outputSymbol: 65/86 = 76%
   CNFEncoding.lean::parseClause_bounds  reproduces  CNFEncoding.lean::parseClauses_bounds: 731/992 = 74%
   CNFEncoding.lean::numVars_le_of_literal_bounds  reproduces  CNF.lean::foldr_max_le_of_forall: 97/133 = 73%
   Deterministic.lean::ComputesInTimeAndSpace  reproduces  Deterministic.lean::haltsAtStep: 64/93 = 69%
   CNFEncoding.lean::parseClauses  reproduces  CNFEncoding.lean::parseClause: 117/175 = 67%
   CNFEncoding.lean::parseClause  reproduces  CNFEncoding.lean::parseClauses: 117/189 = 62%
   Reductions.lean::prefixTM_copy  reproduces  Reductions.lean::prefixTM_emit: 180/327 = 55%
   CNFEncoding.lean::parseClauses_serialize  reproduces  CNFEncoding.lean::parseClause_serializeClause: 402/733 = 55%
   CNFEncoding.lean::parseClause_serializeClause  reproduces  CNFEncoding.lean::parseClauses_serialize: 402/747 = 54%
   Deterministic.lean::haltsAtStep  reproduces  Deterministic.lean::ComputesInTimeAndSpace: 64/119 = 54%
   Oracle.lean::runFrom_plainEmptyOracle  reproduces  Reductions.lean::acceptTM_loop: 73/137 = 53%
   Oracle.lean::runFrom_ofMultiTapeTM  reproduces  Reductions.lean::acceptTM_loop: 70/137 = 51%
   Deterministic.lean::step  reproduces  Oracle.lean::step: 84/165 = 51%
```

### After

```text
declarations screened: 158; copy pairs (target reproduces >= half of source): 18; reproduced text: 3,831 chars
   Oracle.lean::step  reproduces  Deterministic.lean::step: 84/87 = 97%
   Deterministic.lean::step  reproduces  Deterministic.lean::outputSymbol: 76/86 = 88%
   Deterministic.lean::outputSymbol  reproduces  Deterministic.lean::step: 76/87 = 87%
   Encoding.lean::pairDiag_double  reproduces  Encoding.lean::pairDiag_copy: 398/475 = 84%
   CNFEncoding.lean::parseClauses_bounds  reproduces  CNFEncoding.lean::parseClause_bounds: 731/920 = 79%
   Oracle.lean::step  reproduces  Deterministic.lean::outputSymbol: 65/86 = 76%
   CNFEncoding.lean::parseClause_bounds  reproduces  CNFEncoding.lean::parseClauses_bounds: 731/992 = 74%
   CNFEncoding.lean::numVars_le_of_literal_bounds  reproduces  CNF.lean::foldr_max_le_of_forall: 97/133 = 73%
   Deterministic.lean::ComputesInTimeAndSpace  reproduces  Deterministic.lean::haltsAtStep: 64/93 = 69%
   CNFEncoding.lean::parseClauses  reproduces  CNFEncoding.lean::parseClause: 117/175 = 67%
   CNFEncoding.lean::parseClause  reproduces  CNFEncoding.lean::parseClauses: 117/189 = 62%
   Reductions.lean::prefixTM_copy  reproduces  Reductions.lean::prefixTM_emit: 180/327 = 55%
   CNFEncoding.lean::parseClauses_serialize  reproduces  CNFEncoding.lean::parseClause_serializeClause: 402/733 = 55%
   CNFEncoding.lean::parseClause_serializeClause  reproduces  CNFEncoding.lean::parseClauses_serialize: 402/747 = 54%
   Deterministic.lean::haltsAtStep  reproduces  Deterministic.lean::ComputesInTimeAndSpace: 64/119 = 54%
   Oracle.lean::runFrom_plainEmptyOracle  reproduces  Reductions.lean::acceptTM_loop: 73/137 = 53%
   Oracle.lean::runFrom_ofMultiTapeTM  reproduces  Reductions.lean::acceptTM_loop: 70/137 = 51%
   Deterministic.lean::step  reproduces  Oracle.lean::step: 84/165 = 51%
```

## Archive and integration

The ZIP contains `REPORT.md`, all six full modified sources at their repository paths, **two format-patches against the recorded base**, `fill-ch34-c1d.bundle`, baseline/checkpoint/final verification logs and helpers, and `SHA256SUMS`. The bundle requires the base commit and is verified locally. All archive members are checked against `SHA256SUMS`. The working tree is clean.

Authoritative final evidence uses the `final-` prefix together with `copy-screen-after.log`; earlier `check-*` logs document intermediate attempts and are not final gate results. `checkpoint-*` files attest that targets 1–5 were complete before enumeration work. `baseline-initial-attempt.log` records the disclosed transient bootstrap crash; `baseline-sweep.log` combines all successful baseline module checks.
