# Epoch 4, Batch A5 — Cook–Levin closure

## Result and branch

All five targets pass the completion gate. The four previously open targets are closed with no new admissions, and every declaration in `Hardness.lean`, including generated kernel declarations, is free of `sorryAx`.

| Order | Target | Result |
|---|---|---|
| 1 | `NPHard.polyTimeReducible` | Inherited proof unchanged; empty admission roots. |
| 2 | `SAT_NPHard` | Closed through `clA5Reduction`: genuine native serialization, then pure equisatisfiability. |
| 3 | `SAT_NPComplete` | Closed using `SAT_mem_NP` and target 2. |
| 4 | `SAT3_NPHard` | Closed by target 1 through the proved `SAT_reducible_SAT3`. |
| 5 | `SAT3_NPComplete` | Closed using `SAT3_mem_NP` and target 4. |

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Requested source branch: `complexity/arora-barak-ch1`; observed tip `5dc0881add4e75ce454d734026bee4ade910530f` contains the committed A5 brief.
- Required, object-verified base: `06ee5ee1f5c67c06a0c86db3217fa3efd272d048`. The work branch was created at this exact required base after reading the brief from the requested source branch. The brief was retained separately for the delivery.
- Sole work branch: `fill/ch2-e4-A5`. Neither the source branch nor its remote-tracking ref was changed. No push or PR.
- Output-identity checkpoint commit: `8bbb94dab127c98a5a2bbe58f12ba7f628af9edc`. It was checked as the complete owned module before any pure correctness code was added.
- Final commit: `8f079a1de165fa07af8f0cbe89c10815edfa5d05`; tree: `6faa0b3aeff0ce65bb451e6009885c7ae5cdcdec`.
- Only changed repository path: `TCSlib/Complexity/CookLevin/Hardness.lean`.

Final source: **9937 lines, 528786 bytes**, with **163 new private source declarations** and **618 total**. SHA-256: `e3d6b63f2852c7fe8a049dbc7bbb87273cd39150fd0c14580ef70b06fdefc951`.

All **455 inherited private declarations are untouched**: the name-level diff is empty. The freeze audit checks their declaration bytes, all original public signatures, all existing docstrings, and the inherited target-1 proof. Removing the new block and restoring only the four permitted target proof bodies reconstructs the baseline byte for byte. No imports, other modules, statements, certificate parameters, templates, or producer formats were altered.

## Discharged continuation frontier

The A4 REPORT's continuation frontier was followed in order. The inherited s1–s5 producer is consumed as one completed native machine; its implementation and contracts remain frozen.

| Binding obligation | Discharging declarations and behavior |
|---|---|
| Final install of the completed producer | `clA5Packed_install` explicitly consumes `clPackedRecords_machine`; `clA5Clean_install` captures its output and installs the complete protected word. `clA5Cursor_install` adds the unary emission cursor before the unchanged packed producer word. The instance remains inside the inherited header. |
| Genuine native startup | `clA5Copy_clean`, `clA5Host_clean`, and `clA5Startup` start from the real `initCfg x`, copy the real input, install the completed producer, initialize cursor zero, and establish the entire canonical `Cfg.ofWords` seam, with empty physical output and all administrative heads and buffers restored. |
| s6: protected stored-table readers | `clA5Field_native` implements variable field access by charged sequential pair-tail scans. `clA5Count_exact`, `clA5InputPos_exact`, and `clA5Visit_exact` recover the actual inclusive trajectory and greatest-earlier visit data. `clA5Compare_compute` uses the inherited native comparator. `clA5Decode_native` converts binary counts to unary only within an explicit native unary bound; malformed binary requests cannot introduce an exponential clock. |
| s6: fixed templates and exact ordering | `clA5Template_native` and `clA5Group_native` serialize the protected finite templates with their actual unary addresses. `clA5GroupAt_exact` identifies exactly the six-family list lookup; `clA5Work_get` preserves time-then-tape order. `clA5Fragment_exact` and `clA5Emit_exact` identify each emitted chunk, including all markers and the sole final formula terminator. |
| Positive first returns and restoration | `clA5Round` composes the real emission and cursor-update clean calls, including dispatch time, and proves a positive first return and the full configuration seam. `clA5Next_pack` advances to `min (i+1) (R+1)`; the one-past-last state stays fixed and `clA5Emit_exact` is silent there. The same positive-round proof applies to empty fragments and the saturated state. |
| Fuel and common budget | `clA5Fuel` constructs a native binary evaluator for the last-round index. `clA5Pack_bound`, `clA5Poly_add`, and `clA5Poly_call` supply the common budget in `clA5Output_of_nativeChunk`, covering startup, fuel, and each whole round. |
| Physical output identity | `clA5OutputIdentity` discharges the previously conditional assembly lemma using the actual native chunk selector. It instantiates `clEmitter_of_body` and explicitly uses `clTableau_chunks` to obtain polynomial-time computation of exactly `serialize (clTableau …)`, from genuine native input. This theorem was checked and committed before semantics. |
| Pure equisatisfiability | `clA5Certificate` recovers the exact-length certificate from the pinning units. `clA5Reconstruct` is the strong induction on time proving equality of every raw block with an encoded genuine snapshot. `clA5Sound`, `clA5Complete`, and `clA5Equisat` establish both directions. |
| Acceptance and reduction | `clA5Run_output` identifies the actual output with snapshot emissions. `clA5NoFalse` and `clA5Decider_accept` use the total decider's exact singleton output at the horizon. `clA5Reduction` consumes the frozen NP verifier normalization and the exact serialization identity, then applies `decode_serialize`. |

The emitted families retain the original member counts

`n, 1, T, T+1, k(T+1), T`.

Thus `R = n + (k+3)T + k + 1` is the **last index**, and there are **R+1 members**. Empty template groups still occupy their rounds. The final chunk alone appends `[false]`; a final empty fragment therefore still supplies the formula terminator. Startup never forwards the reference decider's verdict.

## Runtime ledger: P, T, and producer cost are distinct

Let `m(n) = n + C(n+1)^e` and `T(n) = c(A(m(n)+1)^d + 1)^2`, exactly the inherited `clProducerHorizon`. The completed producer has its own polynomial runtime and output-length ledger; those constants are obtained from `clPackedRecords_machine` and are not substituted for the body budget.

`clA5Output_of_nativeChunk` constructs the following **one common body budget**, with all constants supplied by proved native machines:

```text
start(n) = 2n + 3
         + aS(n+1)^dS
         + aJ(aH(n+1)^dH + 1)^dJ
round(n) = 1 + aE(W(n)+1)^dE + aI(W(n)+1)^dI
P(n)     = start(n) + round(n) + aF(n+1)^dF
```

Here `W` is a proved polynomial bound for every packed cursor word through `R+1`. `aS,dS` pay the complete producer installation; `aJ,dJ` pay cursor installation; `aE,dE` pay the native selected-fragment computation and clean emission; `aI,dI` pay the complete cursor-update installation; and `aF,dF` pay the actual fuel evaluator. The explicit `1` pays whole-round dispatch. The copy and all clean bridge overheads are included. `clA5Poly_add` and `clA5Poly_call` prove `PolyBound P`.

The inherited emitter closes the total library cost `cLoop * (P(n)+1) * (R(n)+2)` using `clLoop_polyBound`. **P is neither T nor the producer ledger.** The unbounded native selector is itself polynomial on malformed inputs: sequential access is driven by actual unary words, and binary decoding is bounded by the stored unary horizon. The five-phase host is locally harvested from the native clean-host construction in `ClassNP/SAT.lean`; no foreign private declaration names occur in the source.

## Bitwise correctness and acceptance

`clA5Group_eval` exposes the exact raw source/target block windows and input bit. The initial family fixes the whole initial block; state, input, and work families fix literal product-code slices. `clA5Reconstruct` uses `snapshotAt_zero`, `snapshotAt_state_succ`, `snapshotAt_inputSymbol`, and `snapshotAt_workSymbol`; the latter two consume the proved oblivious schedule API. The work case uses `clPrev_spec` to obtain strict `s < t` before invoking the strong induction hypothesis.

`clBlock_state`, `clBlock_input`, `clBlock_work`, and `clBlock_ext` establish equality of **raw bit vectors**. Only after a source raw block is proved to equal an encoded genuine snapshot is `clBlockDecode_encode` used. Decoded equality is never substituted for bitwise equality. The inherited snapshot API retains the distinction between erasing (`some none`) and preserving (outer `none`), including writes on halting transitions.

The acceptance family forbids false emission at every `t < T`. The exact chronological output equation, together with `ComputesInTime` at the horizon, yields the actual singleton indicator output. This rules out `[false]` and forces `[true]`; silence does not supply acceptance. No output-prefix fallback or altered SAT decoder is used.

## Verification

| Gate | Final result |
|---|---|
| Fresh ordered sweep | **57/57**, exit 0, zero `error:` lines, 57 fresh nonempty oleans. |
| Admission diagnostics | Exactly one: untouched out-of-scope `TAUTOLOGY_coNPComplete`. None in `Hardness.lean`. |
| Whole-module kernel closure | **PASS** over all **1550** owned checked kernel declarations, including generated declarations. All **618** source privates (455 inherited, 163 new) and every other owned declaration are admission-free. |
| Public target roots | **All five empty**, with axioms at most `propext`, `Classical.choice`, `Quot.sound`. `SAT_reducible_SAT3` separately checked clean. |
| Physical output and reduction roots | `clA5OutputIdentity` and `clA5Reduction` both have empty admission roots; their complete dependency closures are checked. |
| Public surface | Exactly the five original public declarations. All added source and generated kernel declarations are private. |
| Freeze/ownership | Exact baseline reconstruction apart from the four authorized target proof replacements; empty inherited-name diff; sole changed path `Hardness.lean`; clean committed working tree. |
| Style | 0 FAIL, one recorded size-exception WARN. |
| Delivery | Ordered patch replay reproduces the committed tree; incremental bundle verifies; flat archive and every manifest checksum pass. |

The kernel traversal inspects checked declaration types and opaque values, follows inductive constructors, rejects missing checked declarations, and checks allowed axioms. Every owned declaration is required to have empty admission roots: there is no open-target allowlist. This is a pass of the five-target completion gate.

Final sweep tail:

```text

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
CHECK 51/57 TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP/Tautology.lean:1271:8: warning: declaration uses 'sorry'
CHECK 52/57 TCSlib/Complexity/TuringMachine
CHECK 53/57 TCSlib/Complexity/ClassP
CHECK 54/57 TCSlib/Complexity/Uncomputability
CHECK 55/57 TCSlib/Complexity/Formulas
CHECK 56/57 TCSlib/Complexity/CookLevin
CHECK 57/57 TCSlib/Complexity/ClassNP
FULL_SWEEP_COMPLETE 57/57 2026-10-06T09:36:46.479426+00:00
```

Final kernel traversal result:

```text
CLOSURE_AUDIT_PASS: 618 source private declarations; 1550 owned kernel declarations including generated declarations; every owned declaration admission-free; all five public targets have empty admission roots and axioms at most propext/Classical.choice/Quot.sound; SAT_reducible_SAT3 clean; five-target completion gate passes.
```


The runtime is the stock pinned Lean **4.25.0**, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`, with mathlib at `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. Eleven materialized dependency repositories match their manifest revisions and have no tracked modifications. `lake exe cache get` was invoked exactly once; it completed successfully, with no downloads and 7,506 cache files unpacked. `lake build` was never invoked.

The local process-executable-path compatibility shim is included as `proc_exe.c`. It redirects only the current process's numeric `/proc/<pid>/exe` lookup to `/proc/self/exe`; the compiler, kernel, source, and dependency pins are unchanged. `environment.json`, `dependency-pins.json`, `lean-version.log`, and `cache-get.log` record the environment.

The original bootstrap compiled the 49 prerequisites before an intermediate owned-module error; that historical log is retained. The corrected complete output-identity module and all later modules then completed the bootstrap. The final full sweep uses a separate initially empty output directory. Kernel audits run against those final fresh oleans, not the predecessor cache used by the scratch-only rapid iteration harness.

The first post-closure kernel traversal already found no admissions. Its companion public-surface check caught two autogenerated imported helpers (`Turing.Action.mapState.eq_1` and `Turing.pairDecode.induct`). Two local proof bodies were corrected using direct `delta` unfolding and ordinary strong induction on word length. This changed no statement or machine behavior. The full fresh sweep and both kernel audits were then rerun; the final public surface contains only the five permitted declarations.

## Scope, requests, and delivery

- Requested shared lemmas or escalations: **none**.
- Remaining work in this batch: **none**. The next campaign construction admission is the untouched out-of-scope `TAUTOLOGY_coNPComplete` in `Tautology.lean` (4B).
- The recorded single-file size exception carries forward: exclusive ownership and the absolute freeze of the inherited layers require the additions to stay in `Hardness.lean`; splitting would violate the binding scope. The style check has zero failures and only this size warning.
- The ZIP is flat, with `SHA256SUMS` at its root. It includes this REPORT, the full final source, both ordered format-patches, an incremental git bundle requiring the exact base, final sweep and axiom logs, public-surface/freeze evidence, environment evidence, and rerun scripts. Every manifest entry is verified after ZIP creation.
- Applying the ordered patches to the required base reproduces the final committed tree. Bundle verification and isolated-index patch replay do not change any branch.

## New private declarations

All names are private in `Complexity`; the machine-readable inventory is also included.

```text
clA5_call_first_halt
clA5PadAction
clA5PadTM
clA5PadCfg
clA5Pad_apply
clA5Pad_run
clA5Pad_seam
clA5StopTM
clA5StopCfg
clA5Stop_step
clA5_live_prefix
clA5Stop_clean
CLA5HostState
clA5HostNext
clA5HostEntry
clA5HostRet
clA5HostTM
clA5Host_seam
clA5Host_call
clA5_guard_add
CLA5Clean
clA5Clean_stop
clA5_bridge_bound
clA5Clean_install
clA5Clean_emit
clA5Host_clean
clA5Copy_clean
clA5Packed_install
clA5Pack
clA5Cursor_install
clA5Modules
clA5Modules_bound
clA5Startup
clA5_pt_const
clA5_pt_cond
clA5_pt_and
clA5MapWord
clA5MapTM
clA5MapCfg
clA5Map_run
clA5Map_poly
clA5_pt_unaryLength
clA5_pt_tail
clA5_pt_head
clA5_pt_eq
clA5Iter_native
clA5Iter_shrinking
clA5Drop_native
clA5Pair_sizes
clA5Field_native
clA5Times_native
clA5Le_native
clA5Template_native
clA5Address_native
clA5Group_native
clA5StoredHeader
clA5Instance
clA5StoredRound
clA5Stored_exact
clA5StoredRound_native
clA5Next
clA5Next_native
clA5Next_pack
clA5Fuel
clA5Round
clA5Poly_add
clA5Poly_call
clA5Pack_bound
clA5Output_of_nativeChunk
clA5CompareTM
clA5Compare_compute
clA5EqNum_native
clA5DecodeState
clA5DecodeStep
clA5DecodeStep_native
clA5DecodeStep_state
clA5DecodeState_zero
clA5Decode_orbit
clA5Decode_size
clA5Decode_native
clA5Tail_add
clA5Tail_fields
clA5Field_fields
clA5Tail_rows
clA5Field_rows
clA5Visits_rows
clA5InputSize
clA5Horizon
clA5Trajectory
clA5Visits
clA5Data_exact
clA5Sizes_native
clA5SmallNum
clA5SmallNum_native
clA5Count
clA5Count_native
clA5Count_exact
clA5Add_native
clA5Sub_native
clA5InputPos
clA5InputPos_native
clA5InputPos_exact
clA5Visit
clA5Visit_native
clA5Visit_exact
clA5InputFragment
clA5InputFragment_native
clA5InputFragment_exact
clA5WorkFragment
clA5WorkFragment_native
clA5WorkFragment_exact
clA5Div_native
clA5Mod_native
clA5Select_native
clA5Work_get
clA5GroupAt
clA5GroupAt_exact
clA5IfLt_native
clA5IfZero_native
clA5GetBit_native
clA5Pin_native
clA5Cursor
clA5Cursor_native
clA5InitialIndex
clA5StateIndex
clA5InputIndex
clA5WorkIndex
clA5AcceptIndex
clA5Indices_native
clA5WorkChoice
clA5WorkChoice_native
clA5Fragment
clA5Fragment_native
clA5Fragment_exact
clA5Eq_native
clA5Emit
clA5Emit_native
clA5Emit_exact
clA5OutputIdentity
clA5Block
clA5Meaning
clA5Group_eval
clA5Flatten_eval
clA5Tableau_eval
clA5InputBit
clA5Input_meaning
clA5Initial_meaning
clA5Work_meaning
clA5Reconstruct
clA5ReadInput
clA5ReadInput_get
clA5Certificate
clA5Run_output
clA5NoFalse
clA5Decider_accept
clA5Width_pos
clA5TraceAssignment
clA5Trace_input
clA5Trace_block
clA5Sound
clA5Complete
clA5Equisat
clA5Reduction
```
