# fill-ram-tmproc — final delivery

**Complete:** `Light.exists_tmProc` is proved, with its formal statement byte-identical to the
base. There are no admissions in the owned file, and no admitted dependency is reachable from
the target or any private proof. All required checks pass. No frontier or exception stop remains.

## Provenance and scope

- Immutable base: `0de483083650950569a96b0a3da4fb3f2103e997` (`ram/tmproc-statement`, PR #382), fetched read-only from origin.
- Local proof branch: `codex/fill-ram-tmproc`; delivered source commit: `f0db9abbc1ec30096a3bcb1c606e769e5675ebef`. The proof
  branch was never rebased or pushed. No PR was opened.
- Input and delivery branch: `exchange/pass-shelat-ch5-8` of `Shilun-Allan-Li/tcslib`.
  Output folder: `arora-barak-ch3-4/inbox/fill-ram-tmproc/`.
- Handoff README and bundle verified against `SHA256SUMS`. Bundle SHA256:
  `1c4387c89fa8ec76770c2200050077eea0598c6a1e765ac0d266c0092d90ee57`;
  README SHA256: `3fd0930595bdc517899be7b9cbfc459510b37f739f1b5ecaf6f29ca531782d83`.
  Campaign-text snapshot: `3fc27517af938fec0b3e0f53f85766a5e81f82e6`.
- The first two bundle sections, COMMON's tier 2 addendum and missing-readers rule, the job brief,
  policy, workflow, and environment addendum were read and followed.
- The only source changes are the owned file plus 28 exact readers in their three definition homes,
  under the explicit missing-readers exception. No existing declaration statement is changed.
  Reader proofs are exactly `rfl` or `Iff.rfl`, and have no simp attributes. Eleven unused readers
  from earlier checkpoints were removed before this final check.
- The fresh source worktree had unrelated blueprint case-collision differences on this
  case-insensitive macOS filesystem. They were not edited, staged, committed, or packaged.

## Construction and proof

Route: **code branches**. The singleton program is `[tmBody M]`, procedure number zero, and
requires no extra call depth (`k = 0`). It makes no procedure calls. A finite code branch for
each live state and scanned input/work-symbol tuple invokes the corresponding fixed action.
The transition table is compiled into code; no table is initialized in memory.

`tmStateCode` maps halt to zero and a live state to one plus its index in a fixed finite
enumeration. `tmSym` maps blank/false/true to 0/1/2. `tmCell` injectively codes signed tape
positions, and `tmAddr sc tapes j z = sc + tmCell z * tapes + j` interleaves all work tapes.
At round `i`, the verified `pass` zeros the next two cell-code rows before they become reachable.
This initializes cells lazily, without supplying the runtime deadline to the program.

The proof proceeds through exact primitive assignment/store rules, safe input reading and
clamped motion, work-head location, static tape banks, and optional output emission. Frozen old
heads and scans make tape actions independent and implement simultaneous TM updates, including
optional writes. `tmActionBody_runs` proves a complete fixed action, `tmTail_runs` proves row
selection equals `MultiTapeTM.step`, and `tmRound_ends` joins it with scratch initialization.
`TMRunInv` couples each round to the initialized machine run, including its frame, tape cells,
output segment, and `SameOutside2` promise. The promise and region separation recover the
original input after every round.

`tmSetup_runs` establishes the initial frame. `tmFirstHalt` provides a first halt `u ≤ t` with
live earlier states. `tmLoop_ends` applies `Ends.whileConst`, using output-prefix monotonicity
and the head envelope, and `tmBody_ends` copies the final output length into local zero.
`tmBits_read` recovers the specified bit values; `tmMeets_behind` establishes arbitrary placement.

The explicit machine-dependent constant is:

- `setup = (tmSetup M).blockCost`;
- `step = 4 + (26 * M.k + 18 + (tmTail M).blockCost)`;
- `states = (Finset.univ.toList : List M.State).length + 1`;
- `A = setup + step + states + 2 * M.k + 10`.

With `N = A * (t + x.length + 1)`, the proof bounds the executed rounds, initialized scratch
rings, head/cell codes, input end position, finite constants, and total time by `N`. The given
memory bound and `space ≤ word` then establish every required word/address safety condition.
The return and output promises use precisely the frozen target statement.

The owned file contains 2172 lines, exceeding the brief's approximate 1,500-line threshold.
As instructed, helpers remain private in that file; the maintainer can split it at landing.

## Verification

All Lean checks ran through `scripts/lean_check_tree.sh` via the serialized wrapper, using the
pinned Lean 4.25.0 toolchain and this fill's private olean tree. Final exit codes:

| Check | Exit | Result |
|---|---:|---|
| Owned file | 0 | zero errors and no admission warnings |
| 28 positive reader controls | 0 | every pure restatement closes by reflexivity |
| Sealed owned-file replay | 0 | 29 imported definitions irreducible; their simp definitions removed |
| 28 negative reader controls in seal | 0 | reflexivity fails and the published reader succeeds |
| Axiom audit | 0 | target and all 310 private theorem constants use only standard axioms |
| Dependency walks | 0 | target and every private theorem have an empty admitted-dependency walk |
| Light facade closure | 0 | all 50 listed modules rechecked serially after reader trimming |
| Mathlib cache-root probe | 0 | pinned cache usable |
| Statement freeze | 0 | exact headline signature matches base |
| Pure-reader/base-statement audit | 0 | base content unchanged outside allowed additions |
| Long-proof sketch audit | 0 | every proof over 20 lines has a proof sketch |
| `git diff --check` | 0 | all four controlled source paths |
| Patch replay and zip checksums | 0 | exact base replay and all archived member hashes verified |

There are 60 explicit private theorem proofs. The dynamic probe also checks all
generated private theorem constants, including equation proofs and auxiliaries. The headline
axioms are at most `propext`, `Classical.choice`, and `Quot.sound`; `sorryAx` is absent.
Its dependency walk is exactly `[]`. The final probe rejects any other axiom for both private
proofs and the headline. The exact source, probes, runtime commands, full logs, and SHA256SUMS
are included. There are no additional targets or allowed admitted dependencies.

## Every private declaration

| Declaration | Status | Role |
|---|---|---|
| `tmCell` | definition / notation | A signed work-tape position has an even code on the nonnegative side and an odd code on its negative side. This is the direct-address layout used for the work tapes. |
| `tmCell_injective` | proved theorem | Distinct signed positions have distinct cell codes. |
| `tmCell_le` | proved theorem | Positions within radius `n` use cell codes at most `2 * n + 1`. |
| `tmCell_lt_iff` | proved theorem | The first `2 * i` cell codes are exactly the signed positions of absolute value below `i`. |
| `tmAddr` | definition / notation | Tape `j` uses the corresponding residue class in an interleaved scratch array. |
| `tmIndex_injective` | proved theorem | Quotient and remainder uniquely identify a bank number and its finite index. |
| `tmLocal_ne` | proved theorem | Two static local-bank indices differ if their banks or finite indices differ. |
| `tmAddr_injective` | proved theorem | The interleaved address identifies both the tape and its signed position. |
| `tmAddr_lt` | proved theorem | A cell in radius `n` lies in the first `tapes * (2 * n + 2)` scratch cells. |
| `tmHead_abs_le` | proved theorem | Before step `i`, every work head is within radius `i` of the origin. |
| `tmTape_blank` | proved theorem | At time `i`, cells at distance at least `i` are still blank. A simulator may initialize these cells as it expands its scratch region, without a time bound supplied to the program. |
| `tmFirstHalt` | proved theorem | A completed computation has a positive first halting time no greater than its deadline, with the prescribed output and live states at every earlier time. |
| `tmMeets_behind` | proved theorem | Relocating a procedure and appending other procedures preserves its specification. |
| `tmSet_runs` | proved theorem | A safe assignment with a known expression value has the displayed exact local update. |
| `tmStore_runs` | proved theorem | A safe store with a known in-range natural address and value has the displayed exact memory update and preserves the local variables. |
| `tmMatches` | definition / notation | The listed locals have the listed natural values. |
| `tmSelect` | definition / notation | Test a fixed finite list of local values, choosing `yes` only when all agree. |
| `tmSelect_runs` | proved theorem | Finite branch selection preserves any common postcondition of its two alternatives. |
| `tmDispatch` | definition / notation | A finite table compiled as code branches, with no transition table stored in memory. |
| `tmDispatch_runs` | proved theorem | A compiled finite table executes the selected row whenever that row occurs in the table. |
| `tmSym` | definition / notation | Blank, false, and true have codes zero, one, and two. |
| `tmSym_some_eq` | proved theorem | The nonblank symbol code is the bit value plus one. |
| `tmSym_le_two` | proved theorem | Every encoded work symbol is at most two. |
| `tmBits` | definition / notation | A bit string represented as one integer word per bit in memory. |
| `tmRingMemory` | definition / notation | Zero the next pair of cell-code rows, leaving all previously initialized rows alone. |
| `tmRingMemory_old` | proved theorem | Initializing the next ring preserves every earlier represented cell. |
| `tmRingMemory_new` | proved theorem | Every cell in the new pair of cell-code rows is initialized to blank. |
| `tmSym_injective` | proved theorem | The three symbol codes distinguish blank and the two bits. |
| `tmRingMemory_tapes` | proved theorem | Clearing the next ring extends a correct tape encoding from strict radius `i` to radius `i`. |
| `tmStateCode` | definition / notation | The live states have positive indices in a fixed enumeration; zero denotes halt. |
| `tmStateCode_injective` | proved theorem | Distinct optional machine states have distinct control-state codes. |
| `tmStateCode_le` | proved theorem | All control-state codes are bounded by the size of the fixed state enumeration plus one. |
| `TMRow` | definition / notation | A transition row specifies a live state and the input and work symbols it scans. |
| `tmRows` | definition / notation | All transition rows of a finite binary machine, enumerated once when generating the code. |
| `tmSeq` | definition / notation | Sequential composition of a fixed list of statements. |
| `tmSeq_accumulate` | proved theorem | A static bank preserves its invariant, establishes the property of every visited index, and preserves that property at any index where it already held. |
| `tmBank` | definition / notation | One statically generated block per work tape. |
| `tmHead` | definition / notation | Local numbers for work heads, scanned work symbols, and computed tape addresses. The first ten locals hold the arguments, input position, control state, output length, and round number. |
| `tmScan` | definition / notation | Local index for a scanned work symbol. |
| `tmAddress` | definition / notation | Local index for a computed work address. |
| `tmOldHead` | definition / notation | Local index for a frozen work head. |
| `TMFrame` | private structure | The stable locals describing one simulated configuration. The temporary locals for addresses, frozen heads, scans, and scratch initialization are deliberately unconstrained. |
| `TMLocated` | private structure | The frozen work heads and their direct addresses for one simulated configuration. |
| `TMScanned` | private structure | The scanned input and work symbols captured before the transition writes any tape. |
| `TMTapes` | definition / notation | The represented cells of all work tapes within a strict radius. |
| `TMTapesAway` | definition / notation | The represented work cells away from the old head on each tape; old head cells may be rewritten while a transition's static tape bank is executing. |
| `tmTapesAway_write` | proved theorem | Writing at an old work head preserves every represented cell away from all old heads. The address injectivity theorem separates both different tapes and different signed cells. |
| `tmKeyLocal` | definition / notation | The locals constrained by `TMFrame`: the eight scalar locals and the current work heads. |
| `tmFrame_transfer` | proved theorem | Preserving the stable locals other than the round counter, and assigning a new counter, preserves the configuration frame at that new round. |
| `tmFrame_round` | proved theorem | Assigning the round local changes only the round index of the represented frame. |
| `tmFrame_tmp` | proved theorem | Changing a temporary local outside the scalar and head banks preserves the frame, with no restriction on the replacement memory. |
| `tmLocated_tmp` | proved theorem | A local update outside the frozen-head/address interval preserves the located data, independently of the replacement memory. |
| `tmScanned_tmp` | proved theorem | Updating a local outside the captured input/work scan slots preserves their old symbol codes, independently of the replacement memory. |
| `tmAddrExpr` | definition / notation | The scratch address of the nonnegative cell code `code` on tape `j`. |
| `tmAddrExpr_read` | proved theorem | A natural cell-code expression gives the corresponding safe interleaved address whenever its code, the two constants, and the resulting address fit the limits. |
| `tmClearRing` | definition / notation | Initialize the next two interleaved cell-code rows using the existing pass routine. Locals eight and nine hold its destination and length; its counter is beyond the tape locals. |
| `tmClearRing_ends` | proved theorem | Clearing one newly reachable ring costs `26 * M.k + 18` steps, leaves the represented memory `tmRingMemory`, and changes only the pass's three temporary locals. |
| `tmCodeExpr` | definition / notation | The two arithmetic branches computing a signed tape position's cell code. |
| `tmCodeExpr_read` | proved theorem | The selected sign branch safely computes the signed cell code using only linear arithmetic in the head position. |
| `tmLocate` | definition / notation | Compute a head's direct scratch address by branching on its sign. |
| `tmLocate_runs` | proved theorem | Locating one tape freezes its head and records its direct scratch address, changing no memory and no other locals. |
| `tmLocateBank_runs` | proved theorem | Locating the whole work-head bank preserves the frame and memory and records every frozen head and direct address. |
| `tmReadTape` | definition / notation | Read the symbol at one previously computed work-tape address into its scan local. |
| `tmScanBank_runs` | proved theorem | Reading all work symbols preserves the frame, located data, input code, and memory. |
| `tmInputZeroTest` | proved theorem | The zero-position test is safe and identifies exactly the left input end marker. |
| `tmInputEnd_read` | proved theorem | The expression for the right input end marker is safe and has value `n + 1`. |
| `tmReadInput` | definition / notation | Read the input in place, encoding either end marker as blank. |
| `tmReadInput_runs` | proved theorem | Reading the input changes only the scanned-input local, and returns the machine's actual input symbol under the blank/bit encoding. |
| `tmPrepare` | definition / notation | The read-only preparation of a transition: locate the work heads and read all symbols. |
| `tmPrepare_runs` | proved theorem | Transition preparation preserves memory and the stable frame and captures all addresses, frozen heads, and scanned symbols. |
| `tmDisplace` | definition / notation | A fixed transition displacement applied to a frozen work-head local. |
| `tmDisplace_read` | proved theorem | A displacement expression is safe under its unit and result bounds and returns the signed head position plus the transition displacement. |
| `tmMoveWork` | definition / notation | Move a work head from its frozen position. The frozen locals make all tape updates independent, so the static bank implements simultaneous work-tape actions. |
| `tmMoveWork_runs` | proved theorem | A work-head update changes only its destination local and returns the prescribed signed position; its expression safety is `tmDisplace_read`. |
| `tmMoveInput` | definition / notation | Move the input head, clamping outward moves at the two end markers. |
| `tmMoveInput_runs` | proved theorem | Input-head motion changes only its local and agrees with the machine's clamped movement. |
| `tmWriteMove` | definition / notation | One tape's transition writes the chosen symbol, or writes back the scanned symbol when there is no write, then moves the head. |
| `tmWriteMove_runs` | proved theorem | One tape's write and head movement have the normalized optional-write effect used by `Action.apply_workTapes` and change only that tape cell and head local. |
| `tmWriteBank_runs` | proved theorem | The complete tape-action bank preserves the eight scalar locals and old output, updates all heads and represented tape cells as the action prescribes, and keeps the external memory. |
| `tmEmit` | definition / notation | Append the optional output bit and advance the output length. |
| `tmEmitState` | definition / notation | The exact state after an optional output emission. |
| `tmEmitState_locals` | proved theorem | The output cursor is the only local changed by emission, with absent emission leaving its existing value unchanged. |
| `tmEmitState_data` | proved theorem | Emission extends the output segment and keeps represented work tapes and external memory when the final output region is apart from scratch. |
| `tmEmit_runs` | proved theorem | Output emission appends the optional bit at the output cursor, advances its length, and leaves every other local and memory cell unchanged. |
| `tmFinishState` | definition / notation | Finish a transition after the work-tape bank: move the input head, emit output, and install the next control state, as an exact-state description. |
| `tmFinishState_frame` | proved theorem | Finishing the scalar updates after a correct tape bank gives the complete next frame. |
| `tmActionBody` | definition / notation | The executable block for one fixed action. |
| `tmActionBody_runs` | proved theorem | A fixed transition action updates the complete configuration representation, output, and external-memory promise within the supplied word and region bounds. |
| `tmRowBody` | definition / notation | The block implementing one fixed row of the machine's transition function. |
| `tmRowTests` | definition / notation | The local-value tests identifying a transition row. |
| `tmRowTests_matches_iff` | proved theorem | Reading a row's tests gives exactly its control state and scanned symbols. |
| `tmRowTests_unique` | proved theorem | If the scanned locals encode `actual`, a row's tests succeed exactly for that row. |
| `tmTail` | definition / notation | The block after scratch initialization: read the old configuration, execute its transition row, and advance the round count. |
| `tmAction` | definition / notation | The transition selected by a live configuration. |
| `tmTail_runs` | proved theorem | Reading a live configuration, selecting its row, and advancing the counter simulates exactly one machine step under the given word and region bounds. |
| `tmRound` | definition / notation | One simulator round initializes its newly reachable cells, then executes the transition. |
| `TMRunInv` | private structure | Before round `i`, the stable frame, initialized work cells, output prefix, and untouched external memory encode the machine after exactly `i` steps. |
| `tmRound_ends` | proved theorem | A simulator round preserves the run invariant when its next initialized ring and all intermediate words fit the supplied limits. |
| `tmSetup` | definition / notation | Initialize the scalar configuration locals and the work-head bank. |
| `tmZeroHeads_runs` | proved theorem | Zeroing the static head bank preserves all scalar locals and memory. |
| `tmSetup_runs` | proved theorem | Setup produces the initial machine frame and preserves the argument memory. |
| `tmGuard_read` | proved theorem | The loop guard is safe when zero fits, and it holds exactly for a live encoded state. |
| `tmLoop_ends` | proved theorem | The verified rounds run until the first halting time, with a constant cost per round. |
| `tmBody` | definition / notation | The generated simulator has one procedure and no calls. The loop observes the encoded halting state, and local zero receives the final output length only after the loop. |
| `tmBits_read` | proved theorem | Read a bit segment in the exact default-index form used by the procedure specification. |
| `tmBody_ends` | proved theorem | Setup, the finite simulation loop, and the final return give the complete body contract. |

The private structures' fields record only their named invariant components: `TMFrame` has the
stable scalar locals and heads; `TMLocated` has frozen heads and addresses; `TMScanned` has input
and work scans; `TMRunInv` has frame, tapes, output, and the external-memory promise. Their
constructors/projections and Lean-generated auxiliary constants add no public surface.

## Exact reader additions

- `TCSlib/Programs/Light/Syntax.lean`: `Light.Op.eval_add`, `Light.Op.eval_sub`, `Light.Op.eval_mul`, `Light.Expr.val_const`, `Light.Expr.val_var`, `Light.Expr.val_op`, `Light.Expr.val_load`, `Light.Expr.cost_const`, `Light.Expr.cost_var`, `Light.Expr.cost_op`, `Light.Limits.addr_iff`, `Light.Expr.safe_const_iff`, `Light.Expr.safe_var_iff`, `Light.Expr.safe_op_iff`, `Light.Expr.safe_load_iff`, `Light.Cond.holds_lt_iff`, `Light.Cond.cost_lt`, `Light.Cond.safe_lt_iff`, `Light.Cond.holds_eq_iff`, `Light.Cond.safe_eq_iff`, `Light.frame_apply`.
- `TCSlib/Programs/Light/Rules.lean`: `Light.Stmt.after_skip`, `Light.Stmt.blockSafe_skip_iff`, `Light.Stmt.after_set`, `Light.Stmt.blockSafe_set_iff`, `Light.Stmt.after_store`, `Light.Stmt.blockSafe_store_iff`.
- `TCSlib/Programs/Light/Calls.lean`: `Light.meets_iff`.

The independent positive controls use `rfl`. Each negative control seals the corresponding
definition, checks that `rfl` fails, and then applies its reader. All 28 retained readers are
actually used by the final owned-file proof. No new simp attributes, axioms, or admissions occur.

Added existing imports:

- `TCSlib.Programs.Light.Lib.Pass`: reuse the verified zeroing pass.
- `TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction`: existing finite function,
  product, and Option instances needed to enumerate the transition rows.

## Imported definitions and published interfaces

| Imported definition(s) | Published equations or lemmas used |
|---|---|
| `Op.eval` | `eval_add`, `eval_sub`, `eval_mul` |
| `Expr.val`, `Expr.Safe`, `Expr.cost` | retained constructor readers above |
| `Cond.Holds`, `Cond.Safe`, `Cond.cost` | retained comparison readers above |
| `Limits.Addr` | `Limits.addr_iff` |
| `frame` | `frame_apply` |
| `Meets` | `meets_iff`, `Meets.of_body` |
| `Ends` | `Ends.set`, `seq`, `skip`, `pass`, `block`, `mono`, `whileConst`, `shift_append` |
| `Stmt.after`, `Stmt.BlockSafe` | retained constructor readers, `Stmt.Runs.seq`, `ite_pos`, `ite_neg`, `mono` |
| `Stmt.blockCost` | kept symbolic as a machine-dependent cost; `Ends.block` supplies its bound |
| `wrote` | `wrote_done`, `wrote_rest`, `sameOutside_wrote`, `Ends.pass` |
| `SameOn` | `cell`, `mono`, `then`, and the region preservation/update lemmas |
| `Seg` | `nil`, `get`, `snoc`, `update_out`, `of_sameOutside` |
| `Program.behind`, `Stmt.shift` | `Program.getElem?_behind_right`, `getElem?_append_of_eq_some`, `Ends.shift_append` |
| `moveInputPos` | zero, left/right-boundary, and interior positive/negative equations |
| `Cfg.inputSymbol` | `inputSymbol_of_zero`, `inputSymbol_of_end`, `inputSymbolInner` |
| `Cfg.workTapeSymbols` | `workTapeSymbols_eq` |
| `Cfg.init` | `init_state`, `init_inputPos`, `init_workTapes`, `init_workTapePos`, `init_output` |
| `Action.apply` | `apply_state`, `apply_inputPos`, `apply_workTapePos`, `apply_output`, `apply_workTapes` |
| `MultiTapeTM.step` | `step_of_halt`, `step_of_some` |
| `MultiTapeTM.outputSymbol` | additionally sealed as a boundary control; no direct proof read |
| `MultiTapeTM.initCfg` | `initCfg_eq` |
| `MultiTapeTM.runFrom` | zero/successor equations, initialized head envelope, output prefix, `exists_first_halt` |
| `FinTM.ComputesInTime` | `computesInTime_iff` |

TCSlib ordinary definitions are never unfolded by an owned proof. Abbreviations and primitive
record projections are used as permitted. Core/Mathlib definitions are not passed to `simp`,
`rw`, or `unfold`; their published lemmas are used instead. The seal closes all 29 candidate
TCSlib boundaries listed in `sealed-definitions.txt` and re-elaborates the entire owned source.

## Reuse and factoring

The import closure was searched for Light procedure rules and simulation examples before the
private interpreter construction. The signed encoding/address helpers use core arithmetic
(`Nat.div_mod_unique`, list index injectivity, `List.idxOf_le_length`). The run-envelope and
first-halt helpers cite existing Turing results. Region/output preservation cites the existing
SameOn/SameOutside/Seg APIs. Ring initialization reuses `Ends.pass`; relocation reuses the
existing shifted lookup/execution APIs; the loop reuses `Ends.whileConst` and output-prefix
monotonicity. No handwritten Turing transition table or RecordTable admission is used.

Within the owned construction, `tmSet_runs` and `tmStore_runs` factor primitive exact-state
rules; `tmAddrExpr_read` is shared by ring initialization and head location; input-zero and
input-end expression helpers are shared by reading and motion; `tmSeq_accumulate` handles all
static banks. Frame/located/scanned preservation helpers are shared by the stages. The
fixed-action, dispatch, round, setup, loop, body, and placement lemmas compose these existing
results rather than duplicating their proofs. The report's declaration inventory gives each
helper's concrete role; the source sketches name its reused interfaces.

## Environment and process limits

macOS/APFS, 12 logical CPUs, 19,327,352,832 bytes physical RAM (18 GiB). Initial memory-pressure
available estimate: 47%, approximately 8.46 GiB. Disk free: 116,680,932 KiB, about 111.28 GiB.
These exceed the addendum's floors. Linux `/proc`, cgroups, `df -B1`, and `time -v` do not apply;
`sysctl`, `vm_stat`, `memory_pressure`, `df -k`, `mount`, and `/usr/bin/time -l` were recorded.

The allowed pinned dependency-tree symlink is
`/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-arora-barak-ch3-4/.lake/packages`.
All present package URLs/revisions match the manifest; absent documentation packages are listed
as ABSENT. Zero-byte dependency oleans: zero. No cache fetch, package build, project build, or
borrowed TCSlib olean tree was used. The cache archive store was not changed. The initial
owned-file import closure and full facade closure were bootstrapped from source into
`.lake/fill-ram-tmproc-oleans`.

All checks use at most one of this fill's Lean processes at once. The wrapper has a per-fill
serialization lock, counts machine-wide Lean processes, and waits while the count is at least
three. It records 52 full-pool polls and 105.950 seconds in completed wait segments.
Each module log records start/end UTC, exit code, and maximum RSS. The initial bootstrap lacked
`nice -n 10`; all later checks use it. Two early setup attempts were premature (Seg before a
prerequisite, and a probe after a failed owned check had removed its olean); prerequisites were
then fully bootstrapped, and the wrapper now refuses missing prerequisites before starting Lean.
No new process is launched until the previous owned check wrapper completes.

## Patch and delivery

Owned-file diff against base:

```text
 TCSlib/Programs/Light/TMProc.lean | 2114 ++++++++++++++++++++++++++++++++++++-
 1 file changed, 2099 insertions(+), 15 deletions(-)
```

Whole controlled patch, including the explicit pure-reader exception:

```text
 TCSlib/Programs/Light/Calls.lean  |    9 +
 TCSlib/Programs/Light/Rules.lean  |   26 +
 TCSlib/Programs/Light/Syntax.lean |   86 ++
 TCSlib/Programs/Light/TMProc.lean | 2114 ++++++++++++++++++++++++++++++++++++-
 4 files changed, 2220 insertions(+), 15 deletions(-)
```

This zip contains REPORT.md, the four controlled source files, the patch against the immutable
base, check logs and exact probe/runtime text, and internal SHA256SUMS. No unrelated files or
built artifacts are included. Delivery uses the exchange worktree, `git pull --rebase` before
copying the zip, and a non-force push only to the exchange branch. The proof branch is unchanged
by that delivery process.

Prior checkpoints already delivered to the same inbox:

| Checkpoint | Exchange commit | SHA256 |
|---|---|---|
| 1 | `decd9adeb` | `696ae19899b94a231d422ce5c6496ede1a940166212e6f7035d7dd7df6843266` |
| 2 | `95c340434` | `2b28eb394455c64f86ad144f0196b35a3b464ad7f9b48ea8d637471cf56a19f9` |
| 3 | `ca4a635a8` | `70cbc66ff9afb091fa976b120c1eb12ecac672ba3e8a295ace32bd7b59cde4c6` |

Those reports describe their earlier frontiers. This final delivery supersedes them: the sole
headline target is now completely proved and verified, without admitted dependencies.
