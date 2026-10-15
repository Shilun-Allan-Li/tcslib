# W2 oracle simulation fill — partial delivery

**Status: 1/2 targets proved.** `Turing.FinOracleNDTM.exists_choiceTM` (W2-C) is proved without admissions. `Turing.FinOracleTM.exists_plain_simulation` (W2-S) retains its original, explicitly reported `sorry`. Four W2-S component lemmas are proved, but there is not yet an assembled plain simulation machine.

## Provenance and ownership

- Repository: `Shilun-Allan-Li/tcslib`.
- Campaign branch checked out: `complexity/arora-barak-ch3-4`.
- Base: `1e9361b5fe2022594f5b62d6d48b629d88214794`.
- Working branch: `fill/w2-oraclesim`; no rebase, push, or PR.
- Required ancestor: `78116c5d5db075c9ce46ecec0b56735d1c600bef`; `git merge-base --is-ancestor … HEAD` passed before source work.
- The three commits after the required ancestor contain briefs/audit documentation and their merge. No parallel batch's fill is incorporated in this base.
- Sole modified tracked file: `TCSlib/Complexity/TuringMachine/Build/OracleSim.lean`.
- Imports, all 13 existing public signatures, public declaration order and every other existing declaration body are unchanged. Only the W2-C body changes. No existing declaration is removed. See `evidence/freeze.json`.
- Final source: **842 lines; 13 public and 17 private declarations**.

## Target and admission ledger

| Target | Result | Remaining dependency |
|---|---|---|
| `FinOracleNDTM.exists_choiceTM` | Proved | None; no `sorryAx` |
| `FinOracleTM.exists_plain_simulation` | Unfilled | Original direct admission |

**No private helper remains `sorry`. No newly proved target is proved modulo an admitted helper.** The three existing deterministic corollaries still depend on the original W2-S admission. This delivery does not claim an oracle simulation through those corollaries.

The base's named 28-warning list is reproduced in `evidence/base-sorry-set.txt`. The final 55-module list contains exactly 27 warnings: the original list minus W2-C. Its 26 out-of-scope warnings are unchanged, including `exists_recordStepTM`, `exists_effectiveNDMachineCode`, `exists_inputLengthTM`, all 20 RecordTable targets, `FinTM.exists_certificateShell`, and the two CodeSimulator targets. See `evidence/sweep-summary.json` for the complete final names.

## W2-C construction and proof

The finite witness has state type `N.State ⊕ Fin 3` and one extra ordinary tape, inserted immediately before the query tape. `Fin.insertNth` supplies the layout; the old query tape becomes the new last tape. No oracle-level virtual-input host or branchwise oracle simulation is introduced.

A source ordinary step takes one host step and consumes one bit. A source query takes one oracle-answer step and one answer-pause step that consumes the ignored bit. The same action-transport lemma covers ordinary actions and the stationary pause. A halted source preserves its output; exhaustion in a live state appends `false`. Exhaustion at a query state submits the permitted discarded query and then appends `false`. The suffix induction yields a halted run of at most `2 * u.length + 2`; public halting absorption gives the observation at exactly that time.

The query-word preservation lemma only transports the query-tape function. Its local `DecidableEq Bool` matches the classical equality used in the polymorphic `queryString` definition, so the dependent least-blank expression has the same elaborated predicate. It adds no axiom.

## New private declarations

Every new declaration is listed below. All are admission-free.

| Declaration | Role |
|---|---|
| `oracleInstallCall` | Instantiate the public clean install call on the singleton oracle verdict, and normalize its entry/exit cut to include zero using R3′ when needed. |
| `oracleFrozenCall` | Apply Z1 at empty virtual input, preserving an arbitrary native input head and output prefix, with a first-exit cut. |
| `oracleQueryWindow` | Prove that temporarily blanking query cell `-1` supplies the framed copy window through the first nonnegative blank. |
| `oracleCost_sum` | Sum local administrative and actual-query charges into the requested quadratic-plus-exact-sum bound. |
| `oracleChoiceSlot` | The inserted ordinary choice-tape index. |
| `oracleChoiceAction` | Forward a source action and move the choice cursor one cell right. |
| `oracleChoiceMachine` | The concrete finite, well-formed deterministic oracle witness. |
| `oracleChoiceCfg` | Transport an arbitrary source configuration with a read-only choice tape and cursor. |
| `oracleChoiceAction_apply` | Shared action/configuration correspondence, permitting the answer-pause control. |
| `oracleChoiceCfg_query` | Query extraction is unchanged by inserting the choice tape. |
| `oracleChoice_step` | One-step correspondence away from the query state. |
| `oracleChoice_pause` | The answer pause consumes a bit without changing the source's data. |
| `oracleChoice_queryStep` | Two host steps implement one source query step, using the public query-step and fixed-choice bridges. |
| `oracleChoice_blank` | The actual blank-choice row applies `answerAction false`. |
| `oracleChoice_exhaust` | The zero-, one-, or two-step exhaustion tail, including a halted source and a source in its query state. |
| `oracleChoice_run` | Choice-suffix induction with the bounded-time output contract. |
| `oracleChoice_initial` | Identify the specified preloaded start with the transported source initial configuration. |

## Flagged prose and imports

- The module's **Main results** W2-C tag changes from “statement” to “proved.”
- The module's **Status** paragraph records the 1/2 partial and the still-admitted deterministic corollaries.
- The W2-S docstring keeps its original sketch and adds a **Fill appendix (partial)** naming the proved components and the unfilled dispatcher.
- The W2-C docstring keeps its original sketch and adds a **Fill appendix** describing the generalized suffix invariant and final halting absorption.
- No import was added, removed or changed. No attribution was changed.

## Duplication

Canonical **before** output (exit 0):

```text
declarations screened: 1331; copy pairs (target reproduces >= half of source): 1717; reproduced text: 574,720 chars
```

Canonical **after** output (exit 0):

```text
declarations screened: 1348; copy pairs (target reproduces >= half of source): 1719; reproduced text: 575,010 chars
```

Delta: **17 declarations, 2 directed in-file pairs, 290 reproduced characters**. All baseline pairs persist unchanged; no other pair is added. The baseline has zero pairs involving OracleSim. See `evidence/screen-delta.json`.

Full canonical before/after outputs are included in `evidence/screen-before.txt` and `evidence/screen-after.txt`; the prescribed population and command are in `evidence/screen.sh`. A supplemental owned-side run retains the canonical extraction and tiling functions but filters comparisons to pairs involving OracleSim (`evidence/screen-owned.txt`).

New in-file pairs:

| Target reproduces source | Matched text | Ruling |
|---|---:|---|
| `oracleChoiceAction_apply` → `oracleChoice_initial` | 145/241 = 60% | Shared `Cfg.ext`/`Fin.succAboveCases` boilerplate for two different facts: one action versus initial preload. No repeated machine trace; below 90%. |
| `oracleChoice_initial` → `oracleChoiceAction_apply` | 145/260 = 56% | The reverse directed match of the same pair. |

**new copies: none**. There are no new cross-file pairs with an owned-file declaration on either side. No new in-file pair reaches 90%.

Promotion candidates: the first-exit normalization in `oracleInstallCall` belongs naturally beside the clean-call interface. `exists_inputCallTM` already performs an analogous local normalization, but exposes only a native-input call. The present lemma is independently written, specializes the oracle verdict and empty virtual input, and cites the public install and release contracts; neither a clean-call trace nor its cleanup is copied. A shared general first-cut interface would let the maintainer unify this glue at integration. The query-tape extensionality argument inside `oracleChoiceCfg_query` could likewise be promoted to a small oracle-model congruence lemma if another caller needs it. No public addition is made here. Escalations: none.

## Verification

All Lean invocations used `scripts/lean_check_tree.sh`; **no `lake build` was run**. The runtime is Lean 4.25.0; the reused mathlib dependency cache's Git revision was checked against `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. The container required a local launcher shim to identify the already installed Lean executable. Its source and launcher are included under `evidence/runtime/`; it overrides only the current process’s executable-path `readlink` lookup and delegates all other calls. A normal Lean installation does not need this workaround. Early launcher/cache-start failures were followed by the successful fresh sweep reported here; no compiler source, repository check script, or dependency source was edited.

- Required 55-module dependency-ordered sweep: **exit 0; zero errors; 27 sorry warnings**. Every module has a fresh nonempty olean. Full output: `final-sweep.log`; source and olean hashes: `evidence/sweep-hashes.json`.
- Owned-file independent check: **exit 0; zero errors; exactly one sorry warning**, at `FinOracleTM.exists_plain_simulation`.
- Pre-ship `S1210StatementsProbe.lean.txt`: **exit 0; zero errors**. Its existing probe-local `exists_EXPCOM_decider` warning remains. The named reuse census still prints empty sorry-source lists; the completed W2-C row no longer occurs among consumer admission sources. The 18 additional probe dependency modules were checked separately and are not counted in the 55-module warning ledger.
- Axiom prints: `axioms.log` includes both public targets and all 17 private additions. W2-C and every new helper use only the allowed axioms. W2-S retains `sorryAx` through its original direct admission.
- Style: `style_lint: 0 FAIL, 7 WARN over 20 files`.
- `git diff --check`: passed. Signature/body/import drift check: passed within the reported edit scope.

Final sweep tail:

```text
TCSlib/Complexity/TuringMachine/CodeSimulator.lean:205:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/CodeSimulator.lean:239:8: warning: declaration uses 'sorry'

Owned-file independent recheck (exit 0):
TCSlib/Complexity/TuringMachine/Build/OracleSim.lean:361:8: warning: declaration uses 'sorry'

SUMMARY: 55 modules; zero errors; 27 sorry warnings = 26 untouched + W2-S.
```

Public-target axiom prints:

```text
'Turing.FinOracleTM.exists_plain_simulation' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinOracleNDTM.exists_choiceTM' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Permanent execution sanity case (note 50)

`evidence/OracleSimSanity.lean` imports the delivered module, opens the private **actual constructed machine**, and specializes it to a concrete zero-ordinary-tape source with `q₀ = qQuery`. Its ordinary transitions emit `true`, so accidentally executing one on the empty word would be detected.

The test proves by reduction of the actual transition table, for **every oracle**, that two host steps on the empty choice word leave the host halted with output `[false]`, and leave every other field unchanged. It does not invoke `exists_choiceTM`. The checked empty-oracle and universal-oracle instances are printed. `exhaustion-sanity.log` records the successful check and its admission-free axiom print.

## Continuation frontier for W2-S

This is a ground-rule-9 partial. There is no counterexample or statement escalation. The unfilled part is the machine construction and its simulation invariant, not an arithmetic or interface assertion hidden in a private admission.

1. Instantiate `oracleInstallCall D O τ hD` once. Its source input is `[]`, its entry differs from its exit, and its cut includes zero. `oracleFrozenCall` transports its returned seam through the **existing** Z1 host while freezing arbitrary native input position/output. Relocate this bank with R1; do not repeat the install cleanup or Z1 trace.
2. Build the source/shadow transport on the source's first `M.k + 1` tapes. The shadow origin marker and side bookkeeping must mirror the query head. Derive the off-query segment using `runFrom_eq_plainEmptyOracle` and Z5 as the binding brief requires.
3. Assemble the nine R2 query phases from the original sketch. In particular, store and restore the original query cell `-1`; never assume that cell was blank. Once it is temporarily blanked, use `oracleQueryWindow` to supply `copyTM_run_ofCfg`'s exact window premise. The copy source head must first be at zero. The call's argument bank must be clean on every re-entry.
4. Read and clear the installed singleton verdict; restore cell `-1`, side scratch and the bookmark; restore the original query-head displacement. Establish the full configuration seam into `M.qYes`/`M.qNo`, with source output forwarded and dispatch/call silent.
5. Use the **public** query-radius/length rows to bound each local cost by a fixed administrative coefficient times `r + 1`, plus that coefficient times the actual decider charge. `oracleCost_sum` then supplies the final bound without monotonicity of `τ`. Finish the global simulation/first-halt argument and replace the one original W2-S `sorry`.

Do not reopen the W2-C proof to implement the deterministic simulation. No work in this partial depends on the parallel InputLength, RecordTable, CertShell, CodeSimulator, NDCodes, CfgRecord or Logspace fills.

## Archive and integration

The archive contains this report, the full owned source at its repository-relative path, a format-patch series against the recorded base, an incremental Git bundle with that base as prerequisite, the final sweep and axiom logs, the probe/sanity sources and logs, the two full text screens, freeze evidence, and `SHA256SUMS`. Apply the patch series from the recorded campaign base using `git am -3`; verify `SHA256SUMS` first. Nothing was pushed and no PR was opened. The patch was also applied to an isolated Git index initialized at the base: its resulting tree exactly equals the delivery commit tree (`evidence/patch-apply-check.log`).

Delivery commit: `5526e4d8ac428cf138cfa6410ddc69c22fbc46c5`. The bundle branch is `fill/w2-oraclesim`; its sole prerequisite is `1e9361b5fe2022594f5b62d6d48b629d88214794`. `patches/series` gives the application order. `evidence/bundle-verify.log` records successful bundle verification.

To reproduce the additional Lean evidence after applying the patch, copy `evidence/OracleSimFinalAxioms.lean`, `evidence/OracleSimSanity.lean` and `evidence/S1210StatementsProbe.lean` to `.lake/`, check the 55-module order and then `evidence/probe-extra-order.txt` with `scripts/lean_check_tree.sh`, and use that same script on each `.lake/` evidence module (without its `.lean` suffix). For the supplemental text screen, copy `evidence/screen-owned.py` to `.lake/` and run `bash evidence/screen-owned.sh` from the repository root. The canonical screens use the unmodified repository script.
