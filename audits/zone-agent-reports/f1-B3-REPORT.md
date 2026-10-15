# ZF-B3: checked preparation and a uniform-simulator frontier

**0/1 new targets completed.** `Turing.exists_uniformMachineCode2` remains at its original admission. This is a partial delivery under the B3 report's “1/1, or a frontier” provision. The inherited effective theorem remains proved. The new material isolates decoder-size bounds, exact bounded-acceptance semantics, a real finite-machine deadline test, and a conditional assembly lemma. It does **not** construct the required uniform finite interpreter.

The route still requires a binary guard before state expansion, two physical tapes for the source work tapes, a binary countdown, and one joint polynomial for both verdicts. None of these requirements was weakened. The arbitrary-time canonizer supplies only the inherited effective fields.

## Revision and ownership

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Requested branch: `complexity/arora-barak-ch3-4`; working branch: `fill/zone-f1-B3`.
- Recorded base: `9878115aeb969c311cb9deb4a936933b15e0480f`.
- B3 issue commit: `2623e2eb0c37436f2db611a75c1f90d9dc54203e`.
- The base follows the issue commit only by the B3 brief addition. The owned source is byte-identical at both commits, SHA-256 `d9b848ca40242b08368e43ca2fb183910f5b0c09a708b39f3aa49d0040ce6f45`.
- Delivery commit: `7ecc7e272621c3a35b3f7a835bbaf4b2f88ed189`.
- Only tracked modification: `TCSlib/Complexity/TuringMachine/Codes2Tape.lean`. No rebase, push, PR, shared-module edit, or NDCodes edit.

Read the B3, B2 and B briefs, B2 report and continuation, the B report, A2's canonical-configuration finding, inherited zone audit reports and resolutions, and the repository's agent, policy, and workflow instructions.

**Flagged imports:** exactly `TCSlib.Complexity.TuringMachine.Build.VirtualInput` and `TCSlib.Complexity.TuringMachine.Build.Catalog`. Both are sanctioned by B3. No other imports changed.

**Flagged documentation:** one new private-helper section, headed `Uniform-simulator preparation (ZF-B3)`, with docstrings for its new declarations. No received docstring was altered. Removing this section and the two import lines reproduces the entire received file byte-for-byte. This proves the freeze for all nine public declarations, all 24 inherited privates, the effective proof, and the original uniform target. There are no declaration removals.

## New private ledger

All 16 additions are specific preparation for this target; none is a local copy of a declaration from another module. The deadline test cites the public finite-machine contracts; it does not reconstruct their controllers or proofs. The output-summary and clock lemmas are semantic specifications, not claims about a physical simulator's time.

| New private | Role and limitation |
|---|---|
| `zfB3_decode_length` | Serialization of the decoded machine has length at most `max α.length 354`; cites the frozen scanner/canonizer facts. No time claim. |
| `zfB3_decode_states` | Bounds `351 * ((zfBDecode α).numStates + 1)` by the same size bound, citing the two-tape table lemma and public pairing length. |
| `zfB3_guard_failure` | A failed guard selects the fallback in the existing pure parser before its state/table readers are evaluated. Does not implement binary comparison. |
| `zfB3Output` | Three finite classes: empty, exactly `[true]`, and all other outputs. |
| `zfB3Emit` | Updates the summary for one optional emission. |
| `zfB3Output_append` | Proves exact append-update semantics, including a halting transition's emission. |
| `zfB3Output_true` | Identifies the accepting class with exact singleton output. |
| `zfB3Emit_other` | Proves that the other-output class is absorbing. |
| `zfB3Clock` | Semantic countdown over source transitions with final state/output inspection. |
| `zfB3Clock_correct` | Identifies the countdown with the public exact-deadline run, including padded early halts. |
| `zfB3Answer` | Specializes the countdown to the concrete decoder and initial configuration. |
| `zfB3Answer_correct` | Equivalence with the frozen bounded-acceptance proposition. |
| `zfB3Answer_zero` | Proves zero rejection by citing public `FinTM.not_computesInTime_zero`. |
| `zfB3Answer_malformed` | Proves malformed-code rejection for every deadline using the silent fallback and absorbing halt. |
| `zfB3_deadline_test` | A finite machine extracts the nested deadline twice and compares with empty, in a uniform linear joint budget. Its positive result is only a continuation flag. |
| `zfB3_uniform_of_simulator` | Given a concrete machine computing the exact answer in `C * (α.length + x.length + t + 1)^e`, constructs the frozen record with degree/coefficient `C + e + 1` and the prescribed concrete canonizer. Its machine hypothesis is still unfulfilled. |

**Duplication ledger line:** `Codes2Tape.lean`: received **9 public + 24 private = 33** explicit declarations; new **0 public + 16 private**, no removals; delivered **9 public + 40 private = 49**. New copies: **0**. Inherited copied/adapted format-specific material: **23/49 = 46.94%**, of which strict normalized twins: **3/49 = 6.12%**. These are cumulative declaration fractions, not a claim of zero historical duplication. The 23-instance debt remains exactly as acknowledged under the B2 brief and 12.2c tasklist item 8; no new approval or generalization is sought.

The following retained inventory is inherited from the B2 report, not a fresh claim that the two formats are interchangeable. Since every received byte is frozen, its counterpart/proof-share accounting remains unchanged. “Share” is the B2 report's normalized body-line LCS divided by the counterpart's body lines; it is not semantic equality.

| Retained private | Role | One-tape counterpart | Inherited share |
|---|---|---|---|
| `zfBReadAction` | Read seven fields for two tapes | `codeReadAction` | 6/7 |
| `zfBFallback` | Silent one-state fallback | `codeFallback` | 1/1 |
| `zfBFallback_serialize_length` | 354-bit regression | None | New in B |
| `zfBParse` | Guarded complete parser | `codeParse` | 8/11 |
| `zfBDecode` | Total decoder | `codeDecode` | 1/1 |
| `zfBReadAction_append` | Action prefix inverse | `codeReadAction_append` | 7/11 |
| `zfBAction_length` | 13-bit action lower bound | `codeAction_length` | 14/15 |
| `zfBTable_length` | 351-per-state lower bound | `codeTable_length` | 11/16 |
| `zfBReadTable_append` | Table recovery | `codeReadTable_append` | 2/3 |
| `zfBParse_serialize_pad` | Padded parser round-trip | `codeParse_serialize_pad` | 22/27 |
| `zfBDecode_serialize_pad` | Padded decoder round-trip | `codeDecode_serialize_pad` | 2/2 |
| `zfBReadAction_sound` | Consumed action prefix | `codeReadAction_sound` | 6/10 |
| `zfBSkipAction` | Erased action reader | `codeSkipAction` | 6/6 |
| `zfBEraseAction` | Reader erasure equation | `codeEraseAction` | 11/11 |
| `zfBParseFull` | Preserve padding suffix | `codeParseFull` | 8/11 |
| `zfBScan` | Erased full parser | `codeScan` | 6/8 |
| `zfBParse_full` | First projection | `codeParse_full` | 11/11 |
| `zfBScan_full` | Second projection | `codeScan_full` | 15/18 |
| `zfBParseFull_sound` | Serialization prefix | `codeParseFull_sound` | 24/27 |
| `zfBCanonical` | Prefix or fallback | `codeCanonical` | 1/1 |
| `zfBCanonical_eq` | Concrete reserialization equation | `codeCanonical_eq` | 10/10 |
| `zfBPrimSkipAction` | Primitive-recursive action scan | `codePrimSkipAction` | 11/12 |
| `zfBPrimScan` | Primitive-recursive full scan | `codePrimScan` | 18/20 |
| `zfBPrimCanonical` | Primitive-recursive canonizer | `codePrimCanonical` | 2/3 |

The first 21 counterparts are in `CodeParser.lean`; the last three are in `MathlibBridge.lean`. `check_freeze.py` reproduces the byte freeze and declaration counts; the new-copy assessment also involved source review and searches, not only name matching.

## Requested shared lemmas

Request a public fixed-width binary decrement routine with an arbitrary-configuration run contract, preserving the other tapes and their displaced heads. Promote/generalize the existing decrement machinery; do not duplicate it in this file. Its origins and the exact requested semantic, frame, no-early-return, duration, and through-run head-bound clauses are in `CONTINUATION.md`.

The requested counter has a little-endian buffered word at its current head, blank delimiters, arbitrary frame outside that interval, and arbitrary native input position/output prefix. It decrements in place, returns success or underflow, restores the counter head, and costs at most `2 * word.length + 2`. Width zero underflows in two steps. This contract is additional to the five commissioned transfer/copy/clear/increment contracts.

At this base those five `_ofCfg` contracts are still admitted. Their axiom prints are recorded for evidence. None is used by a new helper. No canonical catalog run theorem is applied to a framed or displaced configuration; the deadline test uses whole-machine `ComputesInTime` contracts on their actual initial configurations.

This is a shared-interface request under the no-copy rule, not a claim that the theorem is false or that one shared result alone completes it. There is no longer an import-scope obstruction.

## Frontier

The missing work is the actual fixed finite interpreter, with a proved per-input cost ledger: binary guard and exact validation, lookup/application on two physical source tapes, buffered virtual input, binary content-dependent countdown, final transition inspection, and a single coefficient/exponent for both answers. The public loop hosts currently take a horizon indexed by input **length** and canonical `stateWord` seams. They do not directly supply the needed content-dependent deadline and persistent arbitrary source bank. Neither a family of machines indexed by decoded code nor an exponential bound in deadline-bit length proves this target.

`CONTINUATION.md` gives the implementation order and precise use of the completed pieces. The target proof itself remains byte-identical. There is no new admitted helper and no attempt to hide the missing construction behind a definition or theorem hypothesis.

## Verification

- Fresh required sweep: **81/81** module checks exit 0, no error diagnostics, and a fresh olean for each module. The complete, untruncated output is in `sweep.log`.
- Direct owned-module check: **zero errors, one sorry warning**, solely at the unchanged uniform target. The batch's zero-sorry gate is **not met**.
- TuringMachine facade: exit 0, zero errors, checked last; Codes2Tape was checked separately immediately before it.
- All **16 new helpers** have axiom sets contained in `[propext, Classical.choice, Quot.sound]`; none contains `sorryAx`. The audit resolves the actual private names from the compiled environment and fails on any unexpected axiom.
- Lint: `style_lint: 0 FAIL, 12 WARN over 45 files`.
- Source freeze and ownership: pass. `git diff --check`: pass. Bundle verification and reverse patch applicability: pass.

Required headline axiom prints:

```text
'Turing.exists_effectiveMachineCode2' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.exists_uniformMachineCode2' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

The inherited effective theorem satisfies the ceiling. The uniform theorem does not, because it remains admitted. The five imported framed catalog statements also print `sorryAx`; they were not used by any new helper. The ND existence theorem was neither invoked nor edited.

Final owned-module sweep output:

```text
CHECK TCSlib/Complexity/TuringMachine/Codes2Tape
TCSlib/Complexity/TuringMachine/Codes2Tape.lean:859:8: warning: declaration uses 'sorry'
EXIT TCSlib/Complexity/TuringMachine/Codes2Tape 0
```

Final sweep tail:

```text
CHECK TCSlib/Complexity/ClassNP/ExpPoly
EXIT TCSlib/Complexity/ClassNP/ExpPoly 0
CHECK TCSlib/Complexity/ClassNP
EXIT TCSlib/Complexity/ClassNP 0
CHECK TCSlib/Complexity/TuringMachine/Build/VirtualInput
EXIT TCSlib/Complexity/TuringMachine/Build/VirtualInput 0
CHECK TCSlib/Complexity/TuringMachine/Build/Zone
TCSlib/Complexity/TuringMachine/Build/Zone.lean:1109:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Zone.lean:1145:8: warning: declaration uses 'sorry'
EXIT TCSlib/Complexity/TuringMachine/Build/Zone 0
CHECK TCSlib/Complexity/TuringMachine/Codes2Tape
TCSlib/Complexity/TuringMachine/Codes2Tape.lean:859:8: warning: declaration uses 'sorry'
EXIT TCSlib/Complexity/TuringMachine/Codes2Tape 0
CHECK TCSlib/Complexity/TuringMachine
EXIT TCSlib/Complexity/TuringMachine 0
SWEEP_DONE
```

The required sweep emits the following **12 admission warnings**, all present at the recorded base apart from source-line shifts caused by the inserted section:

| File | Declaration | Warning line |
|---|---|---:|
| `TCSlib/Complexity/TuringMachine/CounterProgRun.lean` | `sim_run_of_regs_le` | 343 |
| `TCSlib/Complexity/TuringMachine/Build/Catalog.lean` | `transferTM_run_ofCfg` | 1341 |
| `TCSlib/Complexity/TuringMachine/Build/Catalog.lean` | `copyTM_run_ofCfg` | 1373 |
| `TCSlib/Complexity/TuringMachine/Build/Catalog.lean` | `clearTM_run_ofCfg` | 1404 |
| `TCSlib/Complexity/TuringMachine/Build/Catalog.lean` | `incrementTM_run_succ_ofCfg` | 1437 |
| `TCSlib/Complexity/TuringMachine/Build/Catalog.lean` | `incrementTM_run_overflow_ofCfg` | 1470 |
| `TCSlib/Complexity/TuringMachine/NDCodes.lean` | `exists_effectiveNDMachineCode` | 187 |
| `TCSlib/Complexity/Formulas/QBF.lean` | `truth_exPrefix_iff_satisfiable` | 119 |
| `TCSlib/Complexity/Formulas/QBFEncoding.lean` | `decode_encode` | 88 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `exists_zoneShiftInTM` | 1109 |
| `TCSlib/Complexity/TuringMachine/Build/Zone.lean` | `exists_zoneShiftOutTM` | 1145 |
| `TCSlib/Complexity/TuringMachine/Codes2Tape.lean` | `exists_uniformMachineCode2` | 859 |

The two one-work-tape space theorems that were admitted in the B2 report are already proved at this checkout and do not appear in this list.

All Lean proof checks were invoked through the unchanged `scripts/lean_check_tree.sh`, including the imported private-helper axiom audit. It deletes each stale olean and requires a fresh output and no errors. Lint and source-freeze scripts perform no Lean compilation.

**Setup caveat concerning the build prohibition:** the standard cache setup command `lake exe cache get` automatically attempted a nested `lake -v build proofwidgets:release`, which failed. No explicit project `lake build` command was issued and no theorem verification used Lake, but the automatic dependency-release build attempt means this session cannot be described as having had no `lake build` invocation at all. That setup path was abandoned. The replacement called the public cache download/unpack API through the required checker, without editing dependencies. `ENVIRONMENT.md` and the setup logs record this deviation and the container's application-path workaround.

## Packet and application

The flat ZIP contains this report, continuation, complete owned source, ordered format patch, incremental git bundle, sweep/axiom/lint/freeze/bundle logs, reproducible helper audit and freeze scripts, the module order, declaration ledger, environment/setup evidence, and `SHA256SUMS`.

Verify checksums, then apply the format patch with `git am -3` on the recorded base. The incremental bundle also requires that base. The full source is supplied for review; the patch is the integration artifact. This partial packet does not close the batch's zero-sorry gate.

Notation: `α` is the code word, `x` the payload, `t` the numeric deadline, `C` a uniform time coefficient, and `e` a uniform time exponent.
