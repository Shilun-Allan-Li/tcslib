# W2-S oracle simulation — continuation, partial delivery

**Status: 0/1 continuation targets completed.** `Turing.FinOracleTM.exists_plain_simulation` retains its original direct `sorry`. This delivery adds 50 private declarations, all admission-free: the relocated frozen call, source/shadow transport, off-query transfer, complete local query preparation and restoration, and a candidate finite phase-host machine. The complete service seam, global simulation and final time bound remain open. The frozen W2-C target remains proved.

This is the brief's ground-rule-9 partial. There is no counterexample, interface obstruction, new private admission, or newly proved target dependent on an admitted helper.

## Repository and frozen scope

- Repository cloned: `https://github.com/Shilun-Allan-Li/tcslib`.
- Campaign branch checked out first: `complexity/arora-barak-ch3-4`.
- Base: `ae9e0af5b7e5b6fdd1330920cb408923562391c7`.
- Required ancestor: `820d23121a5847808d079f26bfe7efe0aee36ca3`; the required ancestor check passed before Lean edits and is reproduced in `evidence/freeze.json`.
- Working branch: `fill/w2-oraclesim-cont`. No rebase, push, or PR.
- Delivery commit: `4737c0c185cdaa2cd0116f6e35b56307837d4571`.
- The previous delivery report and its “Continuation frontier for W2-S” were read before writing Lean, together with the original brief, design §12.10, binding source sketch, policy and workflow.
- The commits between the required ancestor and this base only add the continuation brief and its merge. No parallel batch changes are included; the 17-entry sorry baseline is unchanged.
- Only tracked modification: `TCSlib/Complexity/TuringMachine/Build/OracleSim.lean`.
- **All 30 existing declarations have identical code after removing comments and whitespace.** All 13 public signatures and their order, all 17 inherited private declarations, W2-C's proof, all four inherited W2-S helpers, imports and attributions are unchanged. The original W2-S body is also unchanged. Mechanical evidence: `evidence/freeze.json` and its verifier.
- Final owned source: **1,747 lines; 13 public and 67 private declarations** (50 private additions). Generated inductive support declarations are not included in the source-declaration census.

## Admission ledger

| Item | Result |
|---|---|
| W2-S `FinOracleTM.exists_plain_simulation` | Original direct admission remains; not claimed proved. |
| Frozen W2-C `FinOracleNDTM.exists_choiceTM` | Unchanged, admission-free. |
| All 50 new private declarations | Admission-free; axiom census included. |
| Three existing deterministic corollaries | Still depend on the original W2-S admission, as at the base. |
| Out-of-scope declarations | All 16 baseline admissions unchanged. |

No private helper remains `sorry`; therefore there is no private admitted proof sketch to inventory. The original W2-S docstring retains its literal “Proof sketch” and both flagged partial appendices describe the remaining gap.

## Construction and proved boundary

For a source with `m` ordinary tapes and a clean call with `c > 0` tapes, the candidate has `(m + 2) + (1 + c) + 1` tapes. Source tapes occupy `0` through `m`; the shadow is at `m + 1`; the empty virtual-input buffer is at `m + 2`; the clean-call argument starts at `m + 3`; the final tape is scratch. Whole-bank placement uses R1.

The shadow holds a true origin marker, and its head mirrors the source query head. A Boolean in finite control records the head's side, allowing either value at zero. `oracleShadow_run` uses `Function.Iterate.rec` and the two projection semiconjugacies. `oracleOffQuery` then cites R1, Z5 (`runFrom_mapState_of_agreeOn`) and `OracleTM.runFrom_eq_plainEmptyOracle`; it does not repeat their traces.

The local dispatch machine touches only query, shadow, scratch and argument. It bookmarks the original position with false. For a nonzero position it saves the side at scratch cell zero and walks to the true origin; for position zero the saved side is blank. It saves the original query cell `-1` at scratch cell one and blanks that query cell. `oraclePrepare` proves the full local configuration seam and the earlier-control guard in at most `natAbs p + 3` steps (two steps at zero).

After a clean call has supplied a singleton verdict, `oracleRestore` proves exact restoration of the query tape, origin shadow, original head displacement, blank scratch and blank argument. It preserves an arbitrary native input position and output prefix and takes `natAbs p + 3` local steps. `oracleRestore_cut` proves no early answer/redirect. The origin and bookmark searches share `oracleWalk_run`; both final bookmark writes share `oracleMarker_step`, which cites the public writing row. No assumption is made that query cell `-1` was originally blank.

`oracleRelocatedCall` composes the inherited empty-input Z1 result with R1. `oracleCopy_intoBlank` specializes the public copy contract without re-proving the copy trace. `oracleHost` is a finite definition using the public phase host, with the service phase an R2 seam between public copy and the relocated Z1 call. **It has not yet been proved to satisfy the W2-S contract.** In particular, the local four-tape seams are not yet connected by a proved complete host query seam.

## Every new private declaration

| Declaration | Role |
|---|---|
| `oracleRelocatedCall` | Relocate the inherited frozen Z1 call by R1, retaining the full return configuration and first-exit cut. |
| `oracleOrigin` | The shadow tape with its single true origin marker. |
| `oracleSide` | The head-side invariant; either side bit is permitted at zero. |
| `oracleSide_move` | Preserve the side invariant under one unit head move. |
| `oracleShadowAction` | Extend a source action with the read-only shadow head and side control. |
| `oracleShadowTM` | The source table with that shadow extension. |
| `oracleShadowCfg` | Transport all source fields and append the origin shadow. |
| `oracleShadowAction_apply` | The action-level source/shadow configuration equation. |
| `oracleShadow_step` | One-step preservation of the side and shadow invariants, including halting. |
| `oracleShadow_run` | Lift the invariant through the library iterate recursor and projection semiconjugacies. |
| `oracleOffQuery` | Transfer an off-query segment using R1, Z5, and the public plain-empty-oracle bridge. |
| `oracleBankCfg_eq` | Identify a relocated configuration from its selected fields and ambient frame using public R1 projections. |
| `oracleCopy_intoBlank` | Specialize the public copy contract to a blank destination at zero, obtaining an exact buffer and the inherited first-exit cut. |
| `oracleHostTapes` | The total tape count for source, shadow, virtual input, clean call and scratch. |
| `oracleSourceBank` | R1 embedding of the source and shadow prefix. |
| `oracleCallBank` | R1 embedding of the virtual-input buffer and clean-call bank. |
| `oracleSlots` | The query, shadow, scratch and argument slots used by local dispatch. |
| `oracleSlots_injective` | Show that the four local slots are distinct when the call has an argument tape. |
| `OracleDispatch` | Finite local control for initialization and query administration. |
| `oracleDispatchAction` | Silent local actions with stationary native input. |
| `oracleDispatchTM` | The four-tape bookmark, walk, save, read, restore and return table. |
| `oracleWalkCfg` | A local configuration with the two walking heads at the same coordinate. |
| `oracleWalk_run` | One shared two-head walking trace for both origin and bookmark searches. |
| `oracleBookmark_ne_origin` | A non-origin cell of the bookmarked shadow cannot read the true origin marker. |
| `oracleLocalCfg` | The clean four-tape local dispatch frame. |
| `oracleReadyCfg` | The service seam: blanked negative query cell, saved side and symbol, bookmark, and supplied argument buffer. |
| `oracleBackCfg` | The restored source and blank service scratch, with only the bookmark remaining. |
| `oracleMarkedCfg` | The nonzero bookmark seam with the saved side and scratch head on cell one. |
| `oraclePrepare_zero` | Two-step preparation when the original query head is at zero. |
| `oracleRestore_cell` | Read and clear the verdict, restore arbitrary query cell -1, and clear both scratch cells in two steps. |
| `oracleMarker_step` | Shared bookmark restoration via the public one-tape writing row. |
| `oracleRestore_zero` | Three-step full restoration for an original head at zero. |
| `oracleMark_step` | One-step nonzero bookmarking and side storage. |
| `oraclePrepare_tail` | The two origin/save steps after the inward walk reaches zero. |
| `oracleDepart_step` | The first outward move selected by the saved nonzero side. |
| `oracleOrigin_run` | All prefixes of the inward origin search, via the shared walk. |
| `oracleSide_distance` | Recover signed displacement from its side and natural absolute value. |
| `oraclePrepare` | Complete preparation in at most absolute displacement plus three steps, with no early service anchor. |
| `oracleBack_run` | All prefixes of the outward bookmark search, via the same shared walk. |
| `oracleErase_step` | Erase a nonzero bookmark using the shared public-writing specialization. |
| `oracleRestore_three` | The shared three-step seam into the nonzero outward walk. |
| `oracleRestore` | Full local tape/head restoration in absolute displacement plus three steps, allowing side normalization at zero. |
| `oracleDispatchInternal` | Controls that do not trigger a phase-host redirect. |
| `oracleRestore_cut` | No restoration prefix reaches a redirect before the answer anchor. |
| `OraclePhase` | The source, dispatch and service phase families. |
| `oraclePhaseState` | The state alphabet assigned to each phase. |
| `oraclePhaseFintype` | Finiteness of every phase state alphabet. |
| `oraclePhases` | R1 source and dispatch placements plus the R2 public-copy/relocated-call service. |
| `oracleRedirect` | Finite handovers between source queries, administration, service and source answers. |
| `oracleHost` | The candidate finite plain machine, using the existing public phase host. |

## Flagged prose, imports and promotion candidates

- The module's **Status** paragraph adds a flagged “Continuation status (partial)” and describes the new proved boundary. Its existing claims about W2-C and the corollaries remain accurate.
- The W2-S docstring retains the original sketch and prior partial appendix and adds **“Fill appendix (continuation, partial)”**. It names the new components and explicitly leaves the original admission open.
- No target tag is changed to “proved”; no Main results tag, import or attribution changes.
- Shared-lemma promotion candidates: `oracleBankCfg_eq` is generic R1 seam identification from selected projections and the ambient frame; `oracleCopy_intoBlank` is a reusable blank-destination specialization of the public copy contract. They remain private under ownership rule 1. No shared lemma is required to make the present components check.
- Escalations: **none**. The remaining gap is proof work, not an unprovable statement or incompatible cited interface.
- The size lint warning for OracleSim is covered by this brief's explicit no-size-cap decision and single-file ownership. No split or public API change is made.

## Duplication governance

Canonical **before** output (exit 0):

```text
declarations screened: 1416; copy pairs (target reproduces >= half of source): 1735; reproduced text: 580,484 chars
```

Canonical **after** output (exit 0):

```text
declarations screened: 1458; copy pairs (target reproduces >= half of source): 1746; reproduced text: 581,698 chars
```

All baseline pairs persist unchanged. The delta is 42 screened declarations, 11 directed in-file pairs and 1,214 reproduced characters; short declarations below the screen's extraction threshold are not counted. See `evidence/screen-delta.json`.

The inherited W2-C pairs are unchanged: `oracleChoiceAction_apply` → `oracleChoice_initial` is 145/241 = 60%, and the reverse is 145/260 = 56%.

Every new directed in-file pair:

| Target reproduces source | Match | Justification |
|---|---:|---|
| `oracleRestore_cell` → `oraclePrepare_zero` | 112/140 = 80% | Shared two-step reduction and public four-field extensionality normalization; the tape transformations are opposite and proved separately. |
| `oracleMarkedCfg` → `oracleLocalCfg` | 149/187 = 80% | Common configuration fields; marked scratch/head state differs from the clean frame. No second trace. |
| `oracleRestore_cell` → `oraclePrepare_tail` | 101/138 = 73% | Same shared finite-cell normalization for different two-row equations. |
| `oraclePrepare_zero` → `oraclePrepare_tail` | 101/138 = 73% | Origin and nonzero preparation endpoints differ; the finite-cell setup is factored into one local simp section. |
| `oracleRestore_zero` → `oracleRestore_three` | 74/102 = 73% | Each extends the shared two-step `oracleRestore_cell` seam by a distinct third row. |
| `oraclePrepare_tail` → `oraclePrepare_zero` | 101/140 = 72% | Reverse directed match of the two preparation equations. |
| `oraclePrepare` → `oracleErase_step` | 143/216 = 66% | Dispatch-table simplification for a prelude control cut versus a bookmark write; the actual write proof is already shared. |
| `oracleMarkedCfg` → `oracleBackCfg` | 91/161 = 57% | Both retain a bookmark but have different scratch contents and moving-head positions. |
| `oracleShadowAction` → frozen `oracleChoiceAction` | 60/114 = 53% | Common forwarding of action fields; shadow/side transport and choice-slot insertion are different transforms. |
| `oracleBack_run` → `oracleMarker_step` | 199/381 = 52% | Configuration extensionality and finite-index normalization; a walking-frame equality and a single write are different facts. |
| `oracleLocalCfg` → `oracleBackCfg` | 83/161 = 52% | Clean and bookmarked frames intentionally share untouched fields. |

**new copies: none.** No new cross-file pair has an owned declaration on either side, and no new in-file pair reaches 90%. Development-time matches at or above 90% were removed by factoring the finite-cell simplification setup through public `Cfg.ext_iff`, `funext_iff` and `Fin.forall_fin_succ`. The source/shadow proof uses the library iterate recursor; the two walks share one trace; the two marker writes share the public one-tape specialization. Full canonical before/after output and the prescribed population command are included. The supplemental owned-side script changes only the pair-selection filter and retains canonical extraction and tiling.

## Environment and verification

All Lean checks use **`scripts/lean_check_tree.sh`**. **No `lake build` was run.** Lean is 4.25.0. `lake exe cache get` was attempted and failed to detect the local Lake configuration; the pinned existing mathlib cache was reused read-only after verifying its Git revision as `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.

The host's Lean launcher could not resolve its executable path, so the runtime-only shim in `evidence/runtime/` supplies that path for the current process's `/proc/<pid>/exe` lookup and delegates all other `readlink` calls. It changes no compiler, dependency or repository check source. Scratch disk exhaustion was handled by moving this task's clone and evidence to task-owned shared-memory directories; no other task's files were changed. The shim is included for reproducibility; a normal Lean installation does not require it.

The initial dependency bootstrap checked modules 1–67 and 69–85; the owned module was filled and checked incrementally. The final uninterrupted sweep below checks all 85 modules from the required order with fresh oleans, and supersedes transient development failures. The named baseline is in `evidence/base-sorry-set.txt`.

- Required **85-module final sweep: exit 0; zero errors; exactly 17 sorry warnings** — the original W2-S admission and the 16 untouched out-of-scope admissions. Every olean was freshly produced. `final-sweep.log`, `evidence/sweep-summary.json` and `evidence/sorry-ledger.json` record the complete module/hash/name ledger.
- Owned module: exit 0, zero errors, exactly one sorry warning at `FinOracleTM.exists_plain_simulation`; all new private declarations are admission-free.
- Re-run statement probe: exit 0, zero errors, all 25 cited reuse rows print `[]`. Its one pre-existing probe-local `exists_EXPCOM_decider` admission remains. The single extra dependency, `ClassNP.ExpPoly`, was checked separately.
- Final axiom census: the two public targets plus all 67 private declarations, **69 prints**. Only the unfilled public W2-S target has `sorryAx`; all other entries use a subset of `[propext, Classical.choice, Quot.sound]`. See `axioms.log` and `evidence/axiom-summary.json`.
- Execution sanity: exit 0, zero errors, no admissions.
- Style: `style_lint: 0 FAIL, 9 WARN over 20 files`; all nine warnings concern file size.
- `git diff --check`, freeze verification, isolated-index patch replay and bundle verification: passed.

Final sweep tail:

```text
Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
[83/85] EXIT 0
[84/85] TCSlib/Complexity/TuringMachine/Robustness/Bidirectional | start 2026-10-12T06:55:16.583957+00:00
[84/85] EXIT 0
[85/85] TCSlib/Complexity/TuringMachine | start 2026-10-12T06:55:19.346936+00:00
[85/85] EXIT 0
SUMMARY: 85 modules; zero errors; 17 sorry warnings.
```

Public-target axiom prints:

```text
'Turing.FinOracleTM.exists_plain_simulation' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Turing.FinOracleNDTM.exists_choiceTM' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Permanent W2-C execution sanity (note 50)

`evidence/OracleSimSanity.lean` opens the **actual frozen private choice machine**, with a concrete zero-ordinary-tape source having `q₀ = qQuery`. Its ordinary transition would emit true, making an accidental source transition observable. Reduction of the actual query and blank-choice rows proves, for every oracle and native input, that an empty choice word leaves the full configuration halted with output `[false]` after exactly two steps, with the other fields unchanged. The file also checks empty-oracle and universal-oracle instances. It invokes neither `exists_choiceTM` nor the inherited exhaustion lemma. Its axiom print contains only the three allowed axioms.

## Continuation frontier for W2-S

Resume from the proved components above; do not reopen W2-C or the four inherited helpers.

1. Instantiate `oracleInstallCall D O τ hD` once and specialize the candidate `oracleHost` to its `C`, entry and exit. The existing `oracleRelocatedCall` supplies the Z1/R1 return and complete earlier-exit cut; no new clean-call or virtual-input trace is needed.
2. Define the stable full-host configuration relating the first source bank to the source run, with origin shadow, clean call/virtual-input bank and blank scratch. Prove the two initialization handovers from the requested `prefixWords` preload. `oracleBankCfg_eq` is intended to identify the local R1 views from their selected fields and ambient frame.
3. Connect `oraclePrepare` through the dispatch R1 embedding and phase-host guard. Apply frozen `oracleQueryWindow` at the left-blanked source tape, then `oracleCopy_intoBlank`; identify the result with the input seam for `oracleRelocatedCall`. Compose the service through public `seamCompTM_run_ofCfg` and its first-return contract. Account for the public host's redirect steps explicitly.
4. Connect the singleton-verdict return to `oracleRestore` and `oracleRestore_cut`. Prove the complete full-host configuration seam into the source yes/no state using `OracleTM.step_of_qQuery`, including all ambient tapes, heads, native input and accumulated output. The local restoration proof already handles both signs, zero, and an arbitrary old cell `-1`.
5. Establish the candidate host's nonquery-table agreement required by `oracleOffQuery` and use that theorem for off-query segments. Prove the global simulation invariant by alternating those segments and the complete query seam.
6. Use the **existing public** query radius and length rows at source time `r`. Bound the preparation, copy, call, restoration and redirect costs by a fixed multiple of `r + 1` plus the actual `τ |z|` charge. Apply frozen `oracleCost_sum`, absorb initialization overhead, and use public `exists_first_halt` to finish the original preloaded W2-S statement. No monotonicity assumption on `τ` may be introduced.

These are outstanding obligations, not proved claims. There is no new private `sorry` that hides any of them.

## Archive and integration

The archive contains this report, the full owned source at its repository-relative path, a `git format-patch` series against the recorded base, an incremental Git bundle, the complete final sweep and axiom logs, the statement and sanity probes, lint/freeze/screen evidence, runtime workaround source, and `SHA256SUMS`.

Verify `SHA256SUMS`, then apply `patches/series` with `git am -3` from the recorded base. The bundle contains branch `fill/w2-oraclesim-cont`, with the base as its prerequisite. Patch replay in an isolated Git index must produce exactly the delivery commit tree; the result and bundle verification are included under `evidence/`.

To reproduce Lean evidence after applying the patch, run the 85-module `evidence/final-order.txt` through `scripts/lean_check_tree.sh`; then check the one extra module in `evidence/probe-extra-order.txt`. Copy the three evidence `.lean` files to `.lake/` and check each through the same script, passing its path without `.lean`. The canonical duplication command is `evidence/screen.sh`; run it from the repository root. The runtime helper paths in the environment log belong to this task's host and need adjusting only if that host-specific workaround is required.
