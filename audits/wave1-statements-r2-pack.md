# External audit pack — wave-1 statements, round 2: the round-1 repairs

Round 1 (`audits/wave1-statements-findings.md`, attached verbatim) returned **FAIL: 0
blockers, 2 majors, 6 minors, 42 notes**. It found all 26 sorried statements true as stated,
adequate and non-vacuous. The dispositions are in `audits/wave1-statements-resolutions.md`,
attached. This round re-audits the **repairs** on PR #43 at head **`b47992fd`**. The round-1
pack (`audits/wave1-statements-pack.md`) and its question list still describe the statements
themselves, which are unchanged.

The gate closes on zero blockers and zero majors (`workflow.md` §4). The duplication rule
(`audits/TEMPLATE.md`, failure mode 5) is in force. Every attachment in the bundle is taken
from the head `b47992fd`.

## What changed since round 1 (verify)

| Finding | Change at `b47992fd` |
|---|---|
| **1** (packet readiness) | The branch merges the campaign tip `4aafe9e4`, which contains stream A (PR #42), so the attached `Build/Catalog.lean` is the proved Part 3. The **readiness walk** (`audits/logs/wave1-statements-r2-readiness.log`) takes every `Turing.`/`Complexity.` name cited in the five modules' docstrings, minus their own declarations: 95 names. It prints each one's `sorry` sources at the head. **88 are proved. 1 is sorried:** `expandTM_run_ofCfg` (R8.6). **6 are not constants in these modules' closure:** `counterLoopTMVia` (R8.0b) and five downstream consumer names, which the §12.10 probe imports and covers. **The remaining fill prerequisites are exactly R8.0b and R8.6**, in PR #38 (held for its own gate), plus the C continuation's `exists_recordStepTM` for the S1b/Savitch consumers, which the five modules do not cite. |
| **2** (duplication accounting) | **Factored, by user decision.** No statement changed. The details follow this table. |
| **3** | `exists_tableFindTM`'s sketch escapes before skipping an accepted final field. A sanity case for the last matching entry is in the §12.8b probe. Comment-only. |
| **4** | `exists_choiceTM`'s prose allows a discarded final query at exhaustion. Comment-only. |
| **5** | `exists_polyCanonizer`'s sketch adds the zero-guard case: a grammar-derived binary check, fail-fast, with early rejection yielding the fallback. Comment-only. |
| **6** | The screen population is listed exactly (`audits/logs/wave1-statements-r2-screen-population.txt`). It now includes `Build/Primitives`, `ClassP/DTIME`, the four `Universal*` files, `ClassNP/Nondeterminism` and `ChoiceWords`. All are attached. |
| **7** | `POracle_EXPCOM_subset_EXP'` is a probe-local derived inclusion; no campaign declaration of that name exists. The six `rfl` identities are B1, the summit, the three identities and Baker–Gill–Solovay. |
| **8** | Docstrings for `CodeSimulator`'s four private lemmas. Comment-only. |
| **Note 45** | User decisions recorded in the resolutions: the time-only scope, and W2-C public with one customer. |
| **Note 50** | Two sanity cases added to the §12.8b probe: the last matching entry and the empty-field append. The other four are fill obligations, listed in the resolutions. |

**The finding-2 factoring:**
- **A new module, `TuringMachine/ChoiceWords.lean`** (Mathlib-only imports, wired into the
  facade). It has five publics:
  - `append_split_unique`: split uniqueness when `n ↦ n + f n` is strictly increasing;
  - `certificateLength_strictMono`, `expCertificateLength_strictMono`: the NP and NEXP lengths;
  - `choiceBudget_le`;
  - `run_take_of_halted`: branch truncation for any run whose halted runs absorb choices.

  `CertShell.certificateShell_proj` and `OracleSim.mem_iff_exists_choiceOut` cite them.
  `ClassNP/Nondeterminism` deletes five privates (`certificate_split_strictMono`,
  `certificate_split_unique`, `choice_budget_le`, `e3_split_strictMono`, and the one-line
  wrapper `e3_split_unique`), re-points their call sites, and re-derives
  `acceptsWithin_iff_of_halts`.
- **`Oracle.lean`** gains two publics, `OracleTM.step_radius` (the one-step radius bound) and
  `OracleTM.runFrom_radius` (its iteration). From them are re-derived:
  - `Oracle.lean`'s private initialized invariant;
  - `OracleNondeterministic`'s private `runWith_headBlank`;
  - W2-0 (`OracleSim.queryString_runFrom_length_le_of_blank`).

## Brief for the auditor

1. **The factoring is sound and faithful.**
   - Confirm that the five `ChoiceWords` publics and the two `Oracle` publics are true as
     stated, at the right generality, and well homed. `ChoiceWords` is a Mathlib-only module,
     so that `ClassNP` and `Build/` both reach it without layering inversions.
   - Confirm that every re-derived body proves its unchanged statement by citation, with no
     new re-derivation of the shared argument.
   - Confirm that no statement changed in any edited file. The freeze log
     (`audits/logs/wave1-statements-r2-freeze.log`) is the maintainer's declaration-level
     check. `RecordTable` and `CodeSimulator` are comment-only (comment-stripped code
     identical).
2. **The edits to closed audited files are minimal.** `ClassNP/Nondeterminism.lean`
   (chapter 2), `TuringMachine/Oracle.lean` and `TuringMachine/OracleNondeterministic.lean`
   (B1 and P3.1) are changed only as listed.
   - Each carries a flagged maintainer note or a factoring appendix.
   - `Nondeterminism` gains exactly one import (`ChoiceWords`); the others gain none.
   - Report any other change.
3. **Readiness (finding 1).** Check the readiness walk against the attached sources. Confirm
   that the remaining prerequisites are exactly as stated above, and that no attached source
   still contradicts a readiness claim.
4. **Duplication.**
   - The broadened screen (`audits/logs/wave1-statements-r2-screen-{before,after}.txt`)
     compares the tip `4aafe9e4` with the head over the listed population. Its delta,
     exclusions and ledger entry are in `audits/duplication-ledger.md`, "Wave-1 statements".
   - Rule on the two residual classifications:
     - `Nondeterminism.a3n_unpad_EXP` → `ChoiceWords.expCertificateLength_strictMono`, 63%.
       This pre-existing in-file pair became cross-file through the move; it is one
       monotone-power inequality.
     - the writer residual `tableBitsK` against the frozen serializers, including the newly
       visible `UniversalInterpreter.universalRecords`, 56%.
   - Confirm that round 1's copy-side member (`certificateShell_proj`) is gone, and that the
     four old `Nondeterminism` split pairs disappeared.
   - Four pre-existing in-file pairs changed ratio, all inside one file. The largest are
     ch2's `choiceVerifier_append`/`e3_choice_append` twins, at 99%/93% before and 93%/95%
     after: both now carry the same shared-lemma call. They are uncounted under the in-file
     convention, and they predate this gate.
5. **The probes** (`audits/logs/wave1-statements-r2-probes.log`).
   - Check the two new §12.8b sanity cases.
   - In the §12.10 probe, the old negative controls `compareTM_run_ofCfg` and
     `exists_inputCallTM` now print `[]`, because both have been proved since round 1. The
     remaining control, `EXP_subset_POracle_EXPCOM`, still detects. Say whether the census
     needs another negative control.
6. **Docstrings.** Check the four comment-only repairs (findings 3, 4, 5, 8) and the new
   modules' and lemmas' docstrings.
7. Anything else, in the standard table.

## Repository-side attestations (verify or challenge)

* **Replay** (`audits/logs/wave1-statements-r2-replay.log`, both parts user-run).
  - **Part 1:** the downstream closure of every changed module, 20 modules. It started at
    `ba87f8d6`: 0 errors, 34 sorry warnings. They are the 26 statements plus `Classes` 1,
    `EXPCOM` 6 and `Relativization` 1, all pre-existing.
  - **Part 2:** a top-up of the 6 modules downstream of `ChoiceWords` and `Nondeterminism`,
    which changed after part 1 compiled them. It ran at `6060d609`: 0 errors, with sorry
    warnings `CertShell` 1 and `OracleSim` 2.
  - **Part 3:** a second top-up of `Nondeterminism` and the `ClassNP` facade, the only modules
    downstream of the last change (`b47992fd`, inlining the wrapper). 0 errors, 0 sorry
    warnings.
  - Every edited module checks with 0 errors. `Nondeterminism`, `Oracle`,
    `OracleNondeterministic` and `ChoiceWords` have no sorry warnings.
* **Axioms** (`audits/logs/wave1-statements-r2-axioms.log`). The publics of the five statement
  modules, `ChoiceWords`, `Oracle`, `OracleNondeterministic` and `Nondeterminism`: 137 prints.
  - `sorryAx` appears exactly at the 26 statements and four corollaries. The admission walk
    (`…-r2-admissions.log`) traces the corollaries to their roots.
  - Every other print is within `[propext, Classical.choice, Quot.sound]`, including all of
    the changed audited files' publics.
* **Probes:** all three at the head give 0 errors, with sorry warnings only on probe-local
  statements.
* **Lint** (`…-r2-stylelint.log`): 0 FAIL over `TuringMachine` (15 WARN, as at the tip) and
  over `ClassNP` (5 WARN, as at the tip).
* **Inputs.** Everything from round 1's bundle, re-taken at the head, plus:
  - `ChoiceWords`, `ClassNP/Nondeterminism`, `Build/Primitives`, `ClassP/DTIME` and the four
    `Universal*` files;
  - the round-1 findings and resolutions, the ledger, and the round-1 pack.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/wave1-statements-r2-findings.md`.
