# Batch P3 — partial checkpoint

**Target 14 is proved. Target 15 remains open.** The P3 admission-free closure gate is not met. This is the continuation delivery allowed by the brief, with 4 of the 8 target points completed; the additional target-15 component proofs are not counted as a completed contract.

## Repository and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required and actual base: `b2f464197cfd071ff46b3f89aa611285d3983908`.
- Checkpoint commit: `aa1bad68313cb2bcdb0e8c6245c2b31ae3616063`.
- Working branch throughout: `complexity/arora-barak-ch1`, as explicitly requested. No other branch was created or modified; nothing was pushed and no PR was opened.
- The P3 brief was read at the branch's documentation commit `b8d569d27e6658cc38edb79f4135ee8f480cee70`; the clean checkout was then pinned to its required integrated source base.
- Only tracked source change: `TCSlib/Complexity/TuringMachine/Build/Primitives.lean`.
- Final source size: **3684 lines**, versus 2,504 at the base. The brief's existing size exception and exclusive-file ownership require keeping these private helpers in this file. No code was moved elsewhere.
- Added precise import: `TCSlib.Complexity.TuringMachine.Build.Loop`, for the proved conditional loop instance.

## Target disposition

| Target | Disposition |
|---|---|
| 1–13 | Previously proved; all existing declarations unchanged |
| 14, `computesFunInTime_pairMapSnd` | Filled, standard axioms only |
| 15, `computesFunInTime_splitSolve` | Original admitted proof body unchanged; concrete combined body and its `hround` proof remain missing |

### Target 14: construction, phase seams, and bound

`pairMapTM` captures the proved `catalogPayload_computes` source on the original physical input. `mapStart` reaches a silent validator with the capture head at zero and the native input at its origin. `mapValidate` either halts malformed inputs with empty output or reaches the second input-rewind seam. `catalogRewind` restores the native input again; `mapPrefix_replay` emits the exact encoded first component and separator; `mapPayload_replay` and `mapPayload_finish` emit the saved transformed suffix and halt.

The source bank remains intact throughout. Validation finishes before the first physical emission. The capture correspondence includes a source emission on its halting transition. The least source halt supplies the required liveness guard.

For a source time bound `T`, `pairMap_computes` proves `4*(T n+n+3)`. Its replay bound uses `MultiTapeTM.output_length_le`. Substituting the existing actual-payload bound gives

```text
4*(6*(n+1) + Tg n + 1 + n + 3)
= 28*n + 4*Tg n + 40
≤ 40*(n+1+Tg n).
```

Thus the public coefficient is 40. There is no evaluation of `Tg` at an inflated composition bound.

### Target 15: hypothesis map and exact remaining gap

| Loop obligation | Current evidence |
|---|---|
| `hF` | `splitSolve_of_body` obtains `computesFunInTime_lengthBits` and enlarges the common coefficient |
| `hInv0` | Discharged inside `splitSolve_of_body` for the empty initial candidate |
| `hInvStep` | `splitStep_inv`, for the original length-only invariant and arbitrary bits |
| `hstart` | Still an explicit hypothesis of `splitSolve_of_body`; no combined body witness is delivered |
| `hround` evaluation | `splitPrepare_run` / `splitPrepare_first`, `splitCount_run` / `splitCount_firstHalt`, `splitCount_accept`, and `splitPoly_loop_end` are proved components |
| `hround` rejection and stall | `splitRestore_run` restores the exact state-word seam; `splitRestore_first` proves positive duration and first return for that standalone component, including preservation of past-end candidate bits |
| `hround` acceptance | Missing native-prefix/suffix output controller and its proof |
| Complete anchor discipline and common body bound | Missing for the combined controller; standalone first-return facts are not claimed as a full discharge |
| Orbit, least search, failure, and payload bridges | `splitStep_orbit`, `splitFind_eq`, `splitFind_none`, `splitLoop_result` |
| Final exponent arithmetic | `splitLoop_bound`, used in `splitSolve_of_body` |

`P3-continuation.md` describes the proved configurations and the unfilled phase connections. No new helper is admitted. The sole remaining original admission is deliberately visible, and no axiom traversal expectation pretends it has been discharged.

## Freeze and verification

- Comment-stripped comparison preserves all **98** pre-existing declarations: target 14's signature is unchanged; every other existing declaration is unchanged in full. Existing declaration order is unchanged.
- All **15 public signatures and public docstrings** are unchanged. The new module-level implementation note is append-only.
- All **55** new declarations are private. The complete list is below.
- Fresh **57/57 module sweep**, required order, zero errors, exit zero; fresh output tree recorded in `environment.json`. No `lake build` was run.
- `lake exe cache get` was invoked once and completed successfully. Initial bootstrap overlapped cache population and was restarted; the delivered full fresh sweep is the verification gate.
- Pinned Lean 4.25.0, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`; mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- All 23 contract axiom prints are included. Fourteen completed primitive contracts and all eight wrapper/loop contracts have at most the standard triple. Target 15 still prints `sorryAx`.
- Kernel-environment traversal checks all 55 new private declarations and all contracts. A shared traversal over all **984 Build declarations** finds exactly `[Turing.FinTM.computesFunInTime_splitSolve]`.
- Final sweep admission warnings: **29 = 1 unfinished Build target + 28 unchanged out-of-scope campaign admissions**.
- Style lint on all four Build files: **0 FAIL, 2 WARN**. The warnings are the inherited Loop size and the owned Primitives size; the required owned-file constraint and existing size exception are recorded above.
- `git diff --check` passes; tracked diff touches only the owned file.
- Format-patch replay on a clean checkout of the exact base succeeds and reproduces the full source byte-for-byte; the incremental bundle verifies against the same base.

Final sweep tail:

```text
MODULE 52/57 TCSlib/Complexity/TuringMachine
MODULE 53/57 TCSlib/Complexity/ClassP
MODULE 54/57 TCSlib/Complexity/Uncomputability
MODULE 55/57 TCSlib/Complexity/Formulas
MODULE 56/57 TCSlib/Complexity/CookLevin
MODULE 57/57 TCSlib/Complexity/ClassNP
SWEEP_PASS modules=57 elapsed_seconds=159.8
```

The axiom program is a **partial-checkpoint** gate. Its target-15 expected root must become empty after the actual body proof is completed. Therefore neither the requested zero-`sorry` owned-file condition nor the zero-`sorryAx` Build closure condition is asserted here.

## New private declarations

- `mapAction`
- `pairMapTM`
- `mapCfg`
- `mapAction_apply`
- `mapBuffer_rewind`
- `mapStart`
- `mapCfg_read`
- `mapParse_first`
- `mapParse_block`
- `mapValidate`
- `mapPrefix_replay`
- `mapPayload_replay`
- `mapPayload_finish`
- `catalogPair_length`
- `pairMap_computes`
- `splitStep`
- `splitAccept`
- `splitStep_inv`
- `splitStep_orbit`
- `catalogFind_congr`
- `splitFind_eq`
- `splitFind_none`
- `splitLoop_result`
- `splitLoop_bound`
- `splitPos`
- `splitPos_read`
- `splitPos_succ`
- `splitScratch`
- `splitScratch_erase`
- `splitRestoreTM`
- `splitRestoreScan`
- `splitRestore_scan`
- `splitRestoreClean`
- `splitRestore_append`
- `splitRestore_rewind`
- `splitRestore_run`
- `splitCountAction`
- `splitCountCfg`
- `splitCount_over`
- `splitCount_apply`
- `splitCount_run`
- `splitPoly_loop_end`
- `catalogFirstEntry`
- `splitRestore_first`
- `splitCount_accept`
- `splitCount_firstHalt`
- `splitPrepareTM`
- `splitPrepareScan`
- `splitPrepare_scan`
- `splitPrepareReady`
- `splitPrepare_extra`
- `splitPrepare_rewind`
- `splitPrepare_run`
- `splitPrepare_first`
- `splitSolve_of_body`

## Requests and escalations

Requested shared lemmas: **none**. Statement or realizability escalations: **none**. No frozen statement was changed. The unfilled body is a proof/construction frontier, not a claimed counterexample.

## Archive and reproduction

The archive is flat: every member is at the ZIP root, including `SHA256SUMS`. `Primitives.lean` is the complete modified source; its repository destination is the owned path above. Apply the included format-patch on the exact base, or use the bundle's branch endpoint. Both delivery forms preserve the one source commit.

The full sweep is reproduced with the pinned compiler on `PATH`, the pinned mathlib cache populated, and a fresh `TCSLIB_OLEANS` directory:

```bash
python3 /path/to/extracted/sweep.py
python3 /path/to/extracted/run_axioms.py --repo . --oleans "$TCSLIB_OLEANS"
```

Run those commands from the repository root. `PrimitiveAxioms.lean` must sit beside `run_axioms.py`, as it does in this flat archive. `freeze.py` records this checkpoint's exact comparisons; its output and JSON inventory are supplied. The small `proc_self_compat.c` workaround used here only maps the current process's `/proc/<pid>/exe` readlink to `/proc/self/exe`; it changes no Lean proof or kernel behavior and is normally unnecessary on a standard host.

Notation: `n` is physical input length; `T` is a source time bound; `Tg` is the given monotone payload time bound. Other identifiers are source declarations or the brief's named hypotheses.
