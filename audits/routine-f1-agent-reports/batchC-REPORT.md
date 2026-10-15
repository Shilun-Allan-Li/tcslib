# §12 Epoch F1, Batch C — complete delivery

**13/13 assigned theorems proved.** Exactly 19 F2 statements remain sorried and byte-identical. No partial frontier and no new admitted helpers.

Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
Source branch: `complexity/arora-barak-ch3-4`.
Working branch: `fill/s12-f1-C`.
Base: `42d524b665f1fc856fe6f60a27a7d7ecced91b71`.
Delivery commit: `4daaf8767c1b275cdf6a19dbec4ecee6dd513d83`.
Source SHA-256: `9d896306befa195f88dc2900c62cda20090ae787b527872c49da49d5239e57aa`.

Only `TCSlib/Complexity/TuringMachine/Build/Catalog.lean` changed. No push, PR, rebase, or `lake build` was performed. The brief used was the self-contained repository copy `briefs/routine-f1-batchC.md`; the three audit reports, resolutions, policy, and workflow were read. Original definitions, signatures, docstrings, imports, and option headers are preserved; no docstring appendices were added.

## Filled declarations

1. `Turing.transferTM_run`
2. `Turing.transferTM_spaceUsedByTape`
3. `Turing.copyTM_run`
4. `Turing.copyTM_spaceUsedByTape`
5. `Turing.clearTM_run`
6. `Turing.clearTM_spaceUsedByTape`
7. `Turing.compareTM_run`
8. `Turing.compareTM_spaceUsedByTape`
9. `Turing.incrementTM_run_succ`
10. `Turing.incrementTM_run_overflow`
11. `Turing.incrementTM_spaceUsedByTape`
12. `Turing.capture_visitedByTapeHead`
13. `Turing.FinTM.redirectTM_spaceUsedByTape`

## Exact movement ledger

| Routine/case | Forward | Turn | Return | Right-entry | Exact first exit used by the proof | Public bound | Final touched interval |
|---|---:|---:|---:|---:|---|---|---|
| transfer | L | 1 | L | 1 | 2L+2 | 3L+3 (slack) | integers [−1,L], L+2 cells, both tapes |
| copy | L | 1 | L | 1 | 2L+2 | 3L+3 (slack) | integers [−1,L], L+2 cells, both tapes |
| clear | L | 1 | L | 1 | 2L+2 | 2L+2 | integers [−1,L], L+2 cells |
| compare | d | 1 | d | 1 | 2d+2 | 2 min(lengths)+2 | integers [−1,d], d+2 cells |
| increment, success | p | 1 | p | 1 | 2p+2 ≤ 2L | 2L+2 (slack) | integers [−1,p], p+2 cells |
| increment, overflow | L | 1 | L | 1 | 2L+2 | 2L+2 | integers [−1,L], L+2 cells |

Each private routine trace is a full configuration equality at every natural time. The forward configurations visit every nonnegative cell up to the scan depth; the zero-index return configuration visits −1; all intermediate positions lie between these extremes; the completed configuration is stationary at zero. Thus the exact intervals in the table follow directly from those proved traces. The formal public space proofs apply interval containment and `Int.card_Icc`, or the stationary-singleton lemma. The public run proofs choose the displayed exact time and prove exclusion of every requested exit before it.

Empty transfer/copy/clear and width-zero overflow have the trace 0, −1, 0 and return in two steps. A successful increment of `[false]` also returns in two steps without visiting cell 1. Comparison uses a disjunction for physical tape selection and therefore handles self-comparison with one movement per step; the stopping lemma also covers both proper-prefix orientations, equal words, and immediate mismatch.

W1 applies `capture_run` separately at each prefix of the supplied horizon. Output-prefix monotonicity places the capture head between its initial and final recorded lengths, giving exactly the requested output-growth bound; the terminal halting emission is included. W2 uses all-time trajectory agreement, including a source halt followed by either redirected halt or its stationary live loop. No output or termination hypothesis was introduced.

## New private declarations

- `catalogCfg`: Canonical input/output fields, specified words, and explicit work-head positions.
- `catalogTrace`: Forward phase, return phase, and stationary completed configuration as a function of time.
- `catalog_trace_run`: Induction turning the five local transition obligations into the complete all-time trace.
- `catalog_space_bound`: Visited-image containment in the integer interval from −1 to the scan depth, then cardinality.
- `catalog_space_one`: A stationary head visits exactly one cell.
- `catalog_erase_take`: Erasing the last cell of a stored prefix shortens that prefix by one.
- `catalog_write_take`: Writing the next source bit extends the destination prefix by one.
- `catalogClearF`: Clear forward configuration: intact word and advancing head.
- `catalogClearR`: Clear return configuration: unerased prefix and returning head.
- `catalog_clear_trace`: Clear phase invariant and exact all-time configuration trace.
- `catalogCopyF`: Shared transfer/copy forward configuration: intact source and copied destination prefix.
- `catalogCopyR`: Copy return configuration: both complete words and returning heads.
- `catalogTransferR`: Transfer return configuration: unerased source prefix, complete destination, returning heads.
- `catalog_copy_forward`: The common forward transition copies the next bit.
- `catalog_copy_trace`: Copy phase invariant and exact all-time configuration trace.
- `catalog_transfer_trace`: Transfer phase invariant and exact all-time configuration trace.
- `catalog_compare_stop`: Existence of the first differing or terminating position, common nonblank prefix, and correct verdict.
- `catalogCompareF`: Read-only comparison scan with one move per selected physical tape.
- `catalogCompareR`: Read-only comparison return carrying its verdict.
- `catalog_compare_trace`: Comparison phase invariant and exact all-time configuration trace.
- `catalog_increment_split`: Decomposition into leading true bits and either a first false with its tail or no suffix.
- `catalog_increment_value`: The value of incFixed on that decomposition, including overflow.
- `catalog_write_middle`: Changing the bit immediately after a prefix preserves all other cells.
- `catalogIncF`: Increment carry configuration: reset prefix, remaining true prefix, untouched stopping suffix.
- `catalogIncR`: Increment return configuration: complete updated/wrapped word and verdict.
- `catalog_increment_trace`: Increment phase invariant and exact all-time configuration trace.
- `catalog_redirectState`: Local copy of Wrappers.redirectState, translating live/halted source control and last-emission register.
- `catalog_redirectAction`: Local copy of Wrappers.redirectAction, retaining tape actions while suppressing output.
- `catalog_redirectCfg`: Local copy of Wrappers.redirectCfg, preserving source tapes and heads.
- `catalog_redirect_loop`: Local copy of Wrappers.redirect_loop, proving the live loop is stationary.
- `catalog_redirect_apply`: Local copy of Wrappers.redirect_apply, transporting a complete source action.
- `catalog_redirect_step`: Local copy of Wrappers.redirect_step, including both post-halt cases.
- `catalog_redirect_run`: Local copy of Wrappers.redirect_run, all-time initialized configuration correspondence.

The seven `catalog_redirect*` declarations are local copies of the already-proved private correspondence in `Build/Wrappers.lean`, with their names consistently prefixed. No foreign private declaration is referenced. All helpers are in the owned module; there are no new public declarations.

## Frozen F2 inventory

All nineteen declarations below retain their original statement, docstring, and `by sorry` body byte-for-byte. Their line offsets necessarily change when proofs are inserted; their order and contents do not.

- `Turing.FinTM.computesFunInTime_id_spaceUsed`
- `Turing.FinTM.computesFunInTime_const_spaceUsed`
- `Turing.FinTM.computesFunInTime_prepend_spaceUsed`
- `Turing.FinTM.computesFunInTime_lengthBits_spaceUsed`
- `Turing.FinTM.computesFunInTime_polyUnary_spaceUsed`
- `Turing.FinTM.computesFunInTime_polyBits_spaceUsed`
- `Turing.FinTM.computesFunInTime_pairEncodeFixed_spaceUsed`
- `Turing.FinTM.computesFunInTime_pairFst_spaceUsed`
- `Turing.FinTM.computesFunInTime_pairSnd_spaceUsed`
- `Turing.FinTM.computesFunInTime_pairValid_spaceUsed`
- `Turing.FinTM.computesFunInTime_pairConcat_spaceUsed`
- `Turing.FinTM.computesFunInTime_pairDup_spaceUsed`
- `Turing.FinTM.computesFunInTime_pairLenCheck_spaceUsed`
- `Turing.FinTM.computesFunInTime_stripLast_spaceUsed`
- `Turing.FinTM.computesFunInTime_incFixed_spaceUsed`
- `Turing.FinTM.computesFunInTime_pairMapSnd_spaceUsed`
- `Turing.FinTM.computesFunInTime_splitSolve_spaceUsed`
- `Turing.FinTM.computesFunInTime_cond_spaceUsed`
- `Turing.FinTM.exists_loopTM_spaceUsed`

`evidence/freeze.json` records the inventory and source hash. The comparison checked all 32 original theorem signatures and docstrings, all original definitions, the nineteen complete F2 declarations, and the one-file change scope. `git diff --check` passed. Replaying the format-patch on the exact base produced the identical Git tree; see `evidence/patch-replay.log`. The bundle was verified and declares the recorded base as its prerequisite.

## Verification

Pinned Lean: 4.25.0, compiler commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
Pinned mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.

- `final-sweep.log`: fresh owned-module check, exit 0, zero `error:` diagnostics, exactly **19** `declaration uses 'sorry'` warnings; then the requested TuringMachine facade check, exit 0 and zero errors.
- `axioms.log`: all thirteen requested axiom prints, each exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or other axiom.
- `evidence/bootstrap.log`: the prescribed module-order bootstrap, completed through all 65 entries (exit 0 after the documented prerequisite recoveries). Its initial Oracle attempt lacked a mathlib cache object; after targeted cache recovery, the sweep resumed at Oracle. This historical setup error is retained in the raw log. A later Formulas facade attempt required its newer QBF imports; those unchanged modules were checked and the sweep resumed at Formulas. These two recovered setup diagnostics are retained in the raw log. The final owned-module/facade gate is recorded separately above.
- The current facade additionally imports `Build/Embed`, `Build/Seam`, and `NDCodes`; the Formulas facade additionally imports `QBF` and `QBFEncoding`. These five modules are absent from the 65-entry bootstrap list. They were checked as unchanged prerequisites; `evidence/facade-dependencies.log` retains their expected out-of-scope admissions.
- Non-sorry simplifier/unused-tactic lint warnings are present; none is an elaboration error. No warning suppression was added.

Environment setup required `TAR_OPTIONS=--no-same-owner` for archive extraction. In this runtime, `/proc/self/exe` works but the numeric virtual-PID executable path does not. `environment/self_exe.c` normalizes only the executing process's own numeric executable lookup to `/proc/self/exe`; it leaves all other filesystem calls alone. The stock Lean executable, kernel, and libraries are unchanged. It was built with `cc -shared -fPIC environment/self_exe.c -o self_exe.so -ldl` and supplied using `LD_PRELOAD` for the checks. Ordinary Linux environments need no such compatibility helper. The cache download's shared temporary-file cleanup also failed once; an isolated targeted cache successfully supplied all required mathlib dependencies before checks.

The owned file is 1,851 lines. The existing §12 per-theme split deferral and this batch’s one-file ownership require the phase helpers to remain here; no other file was split or changed.

**Final sweep log tail:**

```text
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1757:8: warning: declaration uses 'sorry'
TCSlib/Complexity/TuringMachine/Build/Catalog.lean:1802:8: warning: declaration uses 'sorry'
EXIT 0; ERROR_DIAGNOSTICS 0; SORRY_WARNINGS 19
FRESH_OLEAN .lake/tcslib-check-oleans/TCSlib/Complexity/TuringMachine/Build/Catalog.olean 3362832 bytes
RUN bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine
EXIT 0; ERROR_DIAGNOSTICS 0; SORRY_WARNINGS 0
FRESH_OLEAN .lake/tcslib-check-oleans/TCSlib/Complexity/TuringMachine.olean 45168 bytes
PASS: Catalog 19 expected F2 sorry warnings; facade clean.
```

## Requested shared lemmas

A public initialized head-trajectory correspondence for `redirectTM` would let later consumers avoid the seven local copies:

```lean
((redirectTM M haltOn).tm.runFrom ((redirectTM M haltOn).tm.initCfg x) t).workTapePos
  = (M.tm.runFrom (M.tm.initCfg x) t).workTapePos
```

The local `catalog_redirect_run` proves a stronger full-configuration correspondence and supplies this equality by projection. No shared-file change is needed for this delivery.

**Escalations: none.** All assigned statements are proved as frozen.

**Notation:** L is the touched word's length; d is comparison's first differing or terminating-blank position; p is the first false position in a successful increment. These are the brief's ledger variables.
