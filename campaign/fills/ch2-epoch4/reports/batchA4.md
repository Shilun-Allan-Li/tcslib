# Chapter 2, epoch 4, batch A4 — complete producer checkpoint

**The complete packed-record producer is proved, with a total native polynomial runtime ledger. No additional public target is closed.** This delivery reaches the brief's minimum boundary at the end of continuation step 1. It is a verified checkpoint, not completion of `SAT_NPHard` or the five-target gate.

`clPackedRecords_native` and `clPackedRecords_machine` produce the entire exact packed result from the original native input: the inherited arithmetic header, inclusive chronological movement-count trajectory, and inclusive time-ordered/work-tape-ordered greatest-strictly-earlier visit table. They have no unproved producer, startup, row-search, cleanup or final-buffer hypothesis. The total ledger covers native argument construction, all actual recording and queries, every outer iteration, capture/rewind, cleanup, packing and physical output.

The four original assigned admissions remain untouched. There are no new admissions and no sanctioned admitted dependencies. All 279 inherited private declarations, all original public declarations and every inherited docstring remain byte-for-byte unchanged.

## Provenance and ownership

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Exact source branch: `complexity/arora-barak-ch1`; never `main`.
- Observed source tip carrying the binding A4 brief: `6c947082cde1b37a6a99e439807435d1a55d13ac`.
- Required base, object-verified and used exactly: `1a98019701ce8eb052908dba1fd0131756e5a939`.
- Working branch: `fill/ch2-e4-A4`, created from the source branch and set to the required base; only that new local branch was changed.
- Delivery commit: `1c09fa9780c2fa0ed79caa23feb29aace95dec43`.
- Delivery tree: `6cab7b44b76e914d94e30f1f0a31141d45d8ac6b`.
- Sole changed repository path: `TCSlib/Complexity/CookLevin/Hardness.lean`.
- No push, PR, changes to another branch, or delegation.

The committed A4 brief was read first from the specified source branch, followed by the binding briefs/reports in their prescribed order, particularly A3's stored-format contract, ledgers and continuation frontier. The repository policy/workflow, phase-4 findings/resolutions and emitter bridge resolutions were consumed. The source tip differs from the required base only in campaign documentation; the required-base implementation is the one extended here. The external prior-art Cook–Levin proof was not retrieved, imported, cited or transcribed.

## Targets in order

| Target | Status |
|---|---|
| `NPHard.polyTimeReducible` | Already proved; unchanged; clean admission roots. |
| `SAT_NPHard` | Original admission unchanged. Step 1 is complete; the continuation starts at step 2. |
| `SAT_NPComplete` | Original admission unchanged; deferred until target 2 closes. |
| `SAT3_NPHard` | Original admission unchanged; the proved `SAT_reducible_SAT3` dependency is checked clean. |
| `SAT3_NPComplete` | Original admission unchanged; deferred in order. |

The only out-of-scope source admission is `TAUTOLOGY_coNPComplete`; it is untouched. The open owned targets are unfinished assigned work, not admitted dependencies used by completed helpers.

## Complete stored result and implementation

`clPackedRecords M C e c A d x` is exactly

```text
pairEncode (clPrepHeader C e c A d x)
  (pairEncode (clRecords M (replicate m false) (T+1))
    (clVisitRows M C e x (T+1)))
```

Here `m = |x| + C*(|x|+1)^e` and `T = c*(A*(m+1)^d+1)^2`, exactly as in the inherited header. The full original header is retained unchanged. The trajectory is the inherited actual recorder's word, never a reconstructed substitute. Its `l=2*(k+1)` canonical binary fields, positive/negative ordering, shifted input coordinate, clamping and effects-first/frozen-halt behavior are unchanged.

The last-visit table contains rows for times `0..T` in increasing order. A row contains one self-delimited field for each work tape in `Fin k` order. Its payload is `clVisitCode (prevVisit M m t τ)`: absence is `[]`; a present predecessor `s` is `pairEncode [] s.bits`. Thus absence differs from predecessor zero, whose payload is the nonempty `01` separator. `clVisitRow_exact`, `clLastCode_prev`, `clLastCode_zero` and `clLastCode_halted` give the exact public schedule interpretation, empty time-zero case and immediately preceding frozen-visit case.

The native search loads exactly the first `t` chronological candidate rows, with the current row retained beyond that strict prefix. It compares signed positions by the inherited native cross-sum comparator. It records one actual comparison flag per earlier row; the audited native last-true scanner and binary length computation return the greatest marked source time. This is an explicit scan, not indexed access or raw binary-word equality.

Every reader restart has an explicit wipe: `clWipe*` erases the entire old target, and `clFresh*` invokes the inherited reader on the resulting empty target. The row loader specifies its complete frame and advances a real stream cursor. The actual native query constructor obtains its trajectory and target fields by consuming the banked recorder. Fixed-tape native composition builds a full last-visit row. This construction may recompute an inclusive reference run for a query or field; every such run is charged to the native polynomial composition. No uncharged lookup or recorder reuse is assumed.

`clVisitStep_native` retains the instance, appends that time's entire visit row, and advances the unary query time. The audited install-call bridge gives a positive clean first return for the whole step, with all scratch blank and every head restored. `clRepeatTM` executes exactly `T+1` such calls under a real unary clock, including the time-zero row and final row. Its fresh begin phase executes the first source transition before checking return, so it does not assume the bridge's entry and exit states are distinct. `clRepeat_complete`, `clRepeatOutput_compute` and `clVisitRows_native` establish the native outer loop, full endpoint and physical output. Native pairing then returns the entire packed result.

## Six-row boundary mapping

| Stage | A4 discharge and remaining boundary |
|---|---|
| s1 — exact arithmetic | `clHeaderLayout_native/exact` consumes the inherited sealed header, initializes the literal recorder argument, and preserves the instance and exact values. The entire header is retained in `clPackedRecords`. Zero coefficients, zero degrees and a zero horizon are covered. **Step-1 gap closed.** Final emitter installation remains step 2. |
| s2 — reference simulation | `clRecord_complete` reaches the unchanged recorder from native encoded input, with all retained fields/buffer heads specified. `clRecords_native` composes this with the actual header producer from the original input. The exact `clRec_complete/prepared` results are consumed; the source tracker is not replaced. **Step-1 native preparation gap closed.** |
| s3 — output and halting | Reference verdicts remain suppressed by the inherited recorder. Native preparation and query machines have exact empty-output endpoints; replay returns only the specified stored words. Native composition captures all intermediate outputs. `clPackedRecords_machine` gives the entire physical answer, with no reference verdict prefix. **Whole-producer isolation and output closed.** |
| s4 — inclusive trajectory | The actual inherited rows `0..T`, including initial and final rows, are returned natively from the original instance and included unchanged in the complete packed result. Target counts also come from actual recorder outputs. **Step-1 integration gap closed.** |
| s5 — greatest earlier visits | Actual sequential row loading, cross-sum comparisons, strict prefix, greatest match conversion, time-zero/frozen cases, scratch wipes, clean whole-row calls and the real unary outer loop are assembled. The full inclusive last-visit table and total producer ledger are proved. **Step-1 gap closed; no producer-internal boundary remains.** |
| s6 — serialization | The 77 pure-layer declarations, protected templates, exact `clChunk` order, `clTableau_chunks` and `clEmitter_of_body` remain unchanged. **Open:** final packed-state installation/startup, ordered emitter body, bounded cursor, all positive returns including saturated silence, fuel and common polynomial `P`; then actual output identity. |

**Packed-records install:** the completed producer is now available. No step-2 install-call instantiation with the final packed result is claimed. The new clean calls are internal row/row-step calls, not a substitution of a bare header or verdict for the final producer.

**Genuine emitter startup:** still open. The completed producer itself is proved from native input; this does not establish the later body machine's full canonical `Cfg.ofWords` seam with its bounded emission cursor and all administrative tapes/heads.

**Common `P` versus horizon `T`:** the producer has its own total polynomial bound. No common emitter budget `P` has been supplied or identified with `T`. `P` must still cover the final body's startup, fuel and every complete emission round.

**Output identity before semantics:** the new output identity is for packed preparation records only. The required `output = serialize (clTableau …)` is still open. It must precede the pure certificate-pinning recovery and strong equisatisfiability induction using the snapshot APIs and bitwise product slices, followed by acceptance from the exact singleton decider output at the horizon.

## Runtime ledger

All bounds below are native execution bounds, not inferred from formula output size.

| Component | Proved ledger |
|---|---|
| Explicit target wipe | `2*oldLength+2`, with exact full erasure and head reset. |
| Fresh sequential field read | `2*oldLength+3*newLength+6`; inherits the reader only after its overwrite precondition is discharged by actual erasure. |
| Complete row load | At most `l*(2U+3W+7)` for old widths `U` and new widths `W`, including dispatches. |
| Native input copy | `2*|arg|+2`, with input and target heads restored. |
| Native field preparation | At most `2*|arg|+3+l*(3W+7)` from genuine native input. |
| Retained inclusive recorder | At most `2*|arg|+4+(recorder.k+4)*(3W+7)+(4l+7)*(T+1)^2`. |
| Recorder plus physical output | At most `2*|arg|+8+(recorder.k+4)*(3W+7)+(8l+7)*(T+1)^2`; `clRecordOutput_quadratic` bounds this in the actual argument length. |
| Strict-prefix matching | At most `N*(l*(5W+7)+2W+5)+1`; includes candidate resets, sequential loads, comparisons, clock tests and flag writes. |
| Native query flags | At most `2*|arg|+9+(l+5)*(3U+7)+N*(l*(5W+7)+2W+7)`, including parsing and physical replay. |
| Full greatest-earlier query | Twice the preceding bound, plus the native last-marker conversion `c*(N+1)^e`, plus 2 for actual buffered composition. `clQuery_budget` gives one monomial after bounding all fields/clock by argument length. |
| Per-image native composition | Actual complete runs compose within `2a+b+2`; `clNative_image` proves the polynomial envelope including complete intermediate-word length. |
| Clean whole-row/row-step call | Positive first return within a monomial in its real argument length; full scratch and all heads restored by the audited bridge. |
| Actual unary outer loop | Exactly `N` calls; at most `N*(B+2)+1`, with every call bounded by `B`, two dispatches per call and a final blank-clock completion. |
| Native outer loop and physical output | At most `2L+9+(call.k+1)*(3L+7)+N*(a*(W+1)^d+2)+W`, including true native input preparation and replay. |
| Orbit state size | `W=(8+8k)*(L+1)^2`, since original input and unary clock both occur in the encoded argument of length `L`. |
| Complete outer-loop envelope | `clRepeat_budget`: coefficient `13+7*(call.k+1)+a*(K+1)^d+K`, exponent `2d+3`, where `K=8+8k`. |
| Entire packed producer | `clPackedRecords_machine`: one finite native machine and constants `a,r`, with exact full output in `a*(|x|+1)^r`; complete answer length is bounded by that same runtime. |

All fixed-machine/parameter constants are independent of the input. The zero-work-tape case is covered: visit rows are empty, but the outer calls still have positive duration and the exact inclusive clock is consumed.

## Continuation frontier

The brief's minimum complete-producer boundary is now banked. Continue at step 2:

1. Instantiate the final install bridge with `clPackedRecords_machine`, retain the instance already in the header, add the bounded emission cursor, and prove the entire final body's canonical `Cfg.ofWords` seam from native `initCfg`.
2. Build the ordered emission controller over the protected finite tables with exact `clChunk` order, complete scratch restoration, positive first returns, a positive silent saturated round, cursor updates and fuel. Establish one common polynomial `P` distinct from `T`.
3. Apply `clEmitter_of_body` and `clTableau_chunks` for exact serialized-tableau output before proving equisatisfiability. Recover the certificate from pinning units and carry the specified strong snapshot induction with bitwise raw-block equality. Use the total decider's exact singleton output at the horizon.
4. Close `SAT_NPHard` and the remaining corollaries in their prescribed order, with clean kernel roots.

No statement obstruction was found. **Requested shared lemmas: none. Escalations: none.**

## Freeze, style and verification

Final source: **7446 lines, 394693 bytes**, with **176 new private declarations**. SHA-256: `05fa3ec9f64fb1d9fb14ae32755dc4d1ea978c9984625a14b561ded1b7ce4f79`. The diff contains additions only.

`verify-freeze.py` removes exactly the new contiguous block and reconstructs the required-base source byte-for-byte. Its name-level comparison covers all 279 inherited private declarations and yields an empty diff. Every original public statement/proof and inherited docstring remains unchanged. Kernel public-surface verification also covers generated declarations.

The explicit erasure identity is locally harvested from the committed clean-call implementation in `Build/Loop.lean`; the existing A3 relocation infrastructure is consumed directly. No foreign private declaration is referenced. All other new native controllers and their full-configuration proofs are local to the owned file. The inherited file-size exception continues because exclusive ownership precludes splitting these helpers into another file. Nontrivial new proofs have adjacent English explanations/sketches.

| Gate | Final result |
|---|---|
| Fresh ordered sweep | **57/57**, exit 0, zero `error:` lines, 57 fresh nonempty oleans. |
| Admission diagnostics | Exactly five: four untouched owned targets and out-of-scope `TAUTOLOGY_coNPComplete`. |
| Whole-module kernel closure | **PASS** over all **1191** owned checked kernel declarations, including generated declarations. All **455** source privates (279 inherited, 176 new) are admission-free with axioms at most `propext`, `Classical.choice`, `Quot.sound`. |
| Completed producer roots | `clPackedRecords_native` and `clPackedRecords_machine` have empty admission roots; their entire dependency closures are checked. |
| Public targets | Target 1 clean; the four original open targets have exactly their original admission roots. `SAT_reducible_SAT3` separately checked clean. |
| Public surface | Exactly the five original public declarations. All additions, including generated declarations, are private. |
| Freeze/ownership | Byte-for-byte baseline reconstruction, empty inherited-name diff, sole changed path `Hardness.lean`, clean committed working tree. |
| Style | 0 FAIL, one inherited/recorded size exception. |
| Delivery | Patch replay reproduces the committed tree, incremental bundle verifies, flat archive and all manifest checksums pass. |

The traversal reads checked kernel types and opaque values, follows inductive constructors, rejects missing checked declarations, and checks permitted axioms. The four expected open targets are explicit; this is not a pass of the five-target completion gate.

The initial bootstrap compiled all 49 prerequisites before the in-progress owned module. Its failed iteration is retained as `bootstrap.log`; the corrected owned module and downstream bootstrap completion are retained separately. The final sweep used an independent, initially empty output tree and checked the final source plus all later modules. Both kernel audits were rerun against those final fresh oleans.

Final sweep tail:

```text
TCSlib/Complexity/CookLevin/Hardness.lean:7437:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:7443:8: warning: declaration uses 'sorry'
CHECK 51/57 TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP/Tautology.lean:1271:8: warning: declaration uses 'sorry'
CHECK 52/57 TCSlib/Complexity/TuringMachine
CHECK 53/57 TCSlib/Complexity/ClassP
CHECK 54/57 TCSlib/Complexity/Uncomputability
CHECK 55/57 TCSlib/Complexity/Formulas
CHECK 56/57 TCSlib/Complexity/CookLevin
CHECK 57/57 TCSlib/Complexity/ClassNP
FULL_SWEEP_COMPLETE 57/57 2026-10-06T07:59:20.803790+00:00
```

Final kernel traversal result:

```text
CHECKPOINT_AUDIT_PASS: 455 source private declarations; 1191 owned kernel declarations including generated declarations; all inherited and new helpers admission-free; all five public targets unchanged, with exactly the four original later targets open; SAT_reducible_SAT3 clean. This is not the five-target completion gate.
```


## New private declaration inventory

All names are private in `Complexity`:

```text
clFirst
clMap_run
clErase_last
clWipeTM
clWipeCfg
clWipe_forward
clWipe_backward
clWipe_run
clWipe_idle
clWipe_first
clFreshTM
clFresh_run
clFresh_idle
clFresh_first
clLoadIndex
clLoadSelect
clLoad_inverse
clLoadTM
clLoadCfg
clLoad_frame
clLoad_field
clLoadWords
clLoadWords_step
clLoad_split
clLoad_prefix
clLoad_complete
clLoad_idle
clLoad_first
clInputTM
clInputCfg
clInput_forward
clInput_backward
clInput_run
clInput_idle
clInput_first
clPrepareIndex
clPrepareSelect
clPrepareTM
clPrepare_start
clPrepare_complete
clPrepare_idle
clPrepare_first
clNative_fields
clHeaderTail
clHeaderField
clHeaderTail_native
clHeaderField_native
clRecWords
clHeaderKeep
clHeaderLayout
clHeaderLayout_native
clHeaderLayout_exact
clRecordArgument_native
clRecordSelect
clRecordIndex
clRecord_inverse
clRecordTM
clRecordCfg
clRecord_prepare_frame
clRecord_complete
clMatchWords
clMatchLoadIndex
clMatchLoadSelect
clMatchLoad_inverse
clMatchCmpIndex
clMatchCmpSelect
clMatchCmp_inverse
clMatchState
clMatchTM
clMatchCfg
clMatch_tick
clMatch_stop
clMatch_load_frame
clMatch_load
clMatch_cmp_frame
clMatch_commit
clMatch_compare
clRows
clRows_add
clRows_split
clRows_records
clMatchFlag
clMatch_round
clPriorRow
clMatch_prefix
clMatch_complete
clMatchFlag_schedule
clVisitCode
clLastCode
clLastCode_native
clLastMarker_step
clLastIndex
clLastIndex_marker
clLastIndex_max
clLastCode_prev
clLastCode_zero
clLastCode_previous
clLastCode_halted
clReplayTM
clReplayCfg
clReplay_back
clReplay_forward
clReplay_run
clCompute_comp
clOneSelect
clOutputTM
clOutput_compute
clPreparedTM
clPreparedCfg
clPrepared_run
clPrepared_idle
clQueryWords
clQuery_initial
clMatch_return
clQueryFlagsTM
clQueryFlags_compute
clQueryCode_machine
clFields_width
clRecord_idle
clRecordOutputTM
clRecord_replay_budget
clRecord_size_budget
clCount_size_budget
clRecordOutput_compute
clRecordOutput_quadratic
clNative_image
clRecords_native
clRecordedHeader_native
clReplay_from
clOutputAt_compute
clCountOutputTM
clCountOutput_quadratic
clRecordWords_native
clTrajectory_native
clFinalCount_native
clQuery_budget
clSearchTarget
clSearchArg
clSearchArg_native
clSearch_native
clPrev_native
clVisitRow
clVisitRow_native
clVisitRow_exact
clNative_cleanCall
clVisitRow_cleanCall
clVisitState
clVisitStep
clVisitStep_native
clVisitRows
clVisitStep_state
clVisitStep_orbit
clVisitStep_cleanCall
clRepeatTM
clRepeatCfg
clRepeat_frame
clRepeat_call
clRepeat_round
clRepeat_complete
clRepeatWords
clRepeat_initial
clRepeatOutputTM
clRepeatOutput_compute
clFields_size
clVisitCode_size
clVisitRow_size
clVisitRows_size
clVisitState_size
clRepeat_budget
clRepeatArgument_native
clProducerHorizon
clProducerClock_native
clVisitRows_native
clPackedRecords
clPackedRecords_native
clPackedRecords_machine
```

## Delivery and reproduction

The flat `fill-ch2-e4-A4.zip` contains this report, the full modified `Hardness.lean`, the format-patch series, an incremental git bundle, final fresh sweep and kernel/axiom-print logs, public-surface/freeze checks, private inventory, pinned environment records, reproduction scripts and root `SHA256SUMS`.

Verify extracted contents with `sha256sum -c SHA256SUMS`. The full source maps to the sole owned repository path above. Apply the patch on a maintainer-chosen branch at the exact recorded base; the bundle requires that base. `RUN_CHECKS.sh` accepts the repository path and a new absolute verification directory and reruns the direct ordered sweep, kernel traversal, public-surface audit and freeze check.

`lake exe cache get` was run exactly once, successfully; no `lake build` ran. All materialized dependency checkouts match their manifest pins and have no tracked modifications. Unmaterialized documentation packages are explicitly recorded separately. The stock pinned Lean 4.25.0 compiler/kernel is unchanged. The included process-path compatibility shim maps only the current process's numeric executable-path lookup to `/proc/self/exe`; ordinary runtimes need no shim.

**Notation:** `x` is the original/native instance; `M` the fixed source machine; `k=M.k`; `l=2*(k+1)` the trajectory field count; `m` the exact reference input length; `T` the source horizon; `N` a strict-prefix query count or the explicitly stated outer-call count (`T+1`); `L` an actual encoded argument length; `W,U` word-width/whole-state bounds where stated; `s,t` source times where stated; `τ` a work-tape index. Constants in component bounds are local to their row. The future emitter's common budget is `P`, distinct from `T` and from the completed producer ledger.
