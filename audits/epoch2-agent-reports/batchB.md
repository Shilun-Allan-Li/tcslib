# Epoch 2, Batch B — one work tape

`Turing.FinTM.one_work_tape` is proved. The construction follows the audited
tagged-payload, interleaved-tape, two-sweep design, with a separate zero-work-tape
lockstep case. The final 24-module chapter sweep passed; the target depends only
on `propext`, `Classical.choice`, and `Quot.sound`.

## Repository and scope

| Item | Value |
|---|---|
| Repository | `https://github.com/Shilun-Allan-Li/tcslib` |
| Requested source branch | `complexity/arora-barak-ch1` |
| Verified base commit | `246871220af82a033d5bf869195b081dbd45fb02` |
| Local delivery branch | `fill/epoch2-B` |
| Delivery commit | `40eaff86e0ac818a3194cab37c57a993cecc646c` |
| Commits after base | One |
| Changed repository file | `TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean` |
| Final source length | 1315 lines |
| Final source SHA-256 | `25e0cb9c28e1f99b9c9be6507be08e219d3e9e5dded4021b989c5fad1e81f003` |
| Working tree after commit | Clean |

The brief was read from the requested branch; implementation is based on the
brief's explicitly pinned commit. `policy.md`, plan §5, the two phase-2 audit
reports, the target sketch, and the relevant existing simulation constructions
were read. There was no push, PR, shared-file modification, or vendored-file
modification. All work was performed in this one batch without sub-agents.

The target signature is byte-for-byte identical to the base. Its original sketch
and attribution are retained, followed by the implementation note below. The
entire `one_work_tape_binary` docstring, declaration, and proof are byte-for-byte
identical to the base. The three original file-level `set_option` headers remain.
The owned source contains no `sorry`, `axiom`, `unsafe`, or `native_decide` token.
`freeze-check.json` records these comparisons.

## Brief checklist

- [x] Target filled; relationship to the sketch and the zero-tape path documented.
- [x] Every new authored private declaration listed, with a complete generated
  declaration inventory in the appendix.
- [x] Requested shared lemmas recorded.
- [x] File-size escalation recorded; no mathematical obstruction.
- [x] Appended target docstring note identified and reproduced.
- [x] Complete final sweep and axiom logs attached: zero errors and exactly the
  eight specified remaining sorry warnings.
- [x] Diff changes only `SingleTape.lean`; binary corollary untouched.
- [x] Local commit, format patch, incremental Git bundle, complete source, report,
  and SHA-256 manifest included.

## Construction and proof

### Zero work tapes

`unusedTapeTM` preserves the original control and native input/output action and
adds one work tape whose head stays at zero and whose contents stay blank. The
configuration embedding commutes with one step, including a halted step.
`unusedTape_computes` lifts this to runs and preserves the original time bound.
The conclusion then uses the identity alphabet embedding and constant `1`, since
`T(n) ≤ (T(n) + 1)²`. This branch has no sweeps or setup cost.

### Alphabet, finite control, and layout for positive k

Write `k = M.k`. The internal cell type is

```lean
Fin k × (Option Γ × Bool × Bool)
```

Its fields are the source tape index, payload, current head flag, and saved
left-neighbor head flag. The enlarged alphabet is

```lean
Γ ⊕ Option (Fin k × (Option Γ × Bool × Bool))
```

`Sum.inl` embeds source input/output symbols as unmarked data symbols. Internal
cells use `Sum.inr (some cell)`; `Sum.inr none` is the boundary symbol. The physical
blank is the outer `none` of the machine's work-tape `Option` type. Consequently
an internal cell with payload `none` and head flag `true` is a representable
marked blank, distinct from both a physical blank and a boundary.

`tapeRow` lists the `k` indexed cells in increasing tape-index order, and
`tapeZone` concatenates consecutive rows. After `t` simulated steps the interval
is `[-t, t]`, with `2t + 1` blocks; the physical left boundary is at `-t*k - 1`.
Thus a source coordinate `j` and tape index `i` occupy physical cell `j*k + i`.
Coordinates and interval lengths are proof parameters, not fields of the finite
controller.

The six controller phases are `init`, `back`, `growLeft`, `read`, `growRight`, and
`write`. They contain only finite source states, finite counters, symbols, and
tables indexed by `Fin k`. Both the finiteness and decidable-equality instances
are explicit private declarations, using the controller's sum/sigma
representation. The equality instance locally raises only the typeclass search
size bound to accommodate that representation.

### The two sweeps

Initialization writes the origin block with all `k` blank source heads marked,
sets the right boundary, returns over that block, and writes the left boundary.

For each live source step, the machine first writes one fresh blank block at the
left and moves the boundary. The forward sweep records each marked payload in a
finite table and saves each tape's previous head flag in the next cell of that
tape. At the old right edge, it writes one fresh right block, including the saved
left flags. The completed table is exactly the source's scanned-symbol tuple.

At the new right boundary the machine applies the source's native input movement
and mapped output emission once and turns left. On the return sweep it updates
each old-head payload according to the source action. The new head flag comes
from the old right-neighbor flag for a left move, the current flag for a stay, or
the saved left-neighbor flag for a right move. The return control carries each
tape's old right-neighbor flag. This permits both movement directions in a single
return pass. At the left boundary the controller installs the source's next state
or halts.

`source_bounds` proves by elapsed-time induction that source heads and nonblank
support lie within `[-t, t]`. It supplies the fresh-guard hypotheses. Generic
zipper and list-transduction lemmas establish exact-cost physical sweeps;
`read_row`, `write_row`, `read_zone`, and `write_zone` connect those sweeps to the
source configuration. `sweep_prepare` and `sweep_finish` compose into
`sweep_step`, preserving the entire canonical configuration, not merely the
output. `sweep_run_to_halt` then inducts to the source's first halt.

`sweepPos`, `sweepPos_move`, and `sweepInput_read` connect the true read-only input
tape to `x.map e`, including its endpoints. Output emissions are mapped through
the same embedding. No buffering or alternative input/output model is introduced.

### Exact costs and the quadratic bound

Let `S_k(t)` denote the simulator time at the boundary after `t` source steps.

| Quantity | Formal value |
|---|---|
| Initialization | `S_k(0) = 2k + 2` |
| One step with n old blocks | `(2n + 5)k + 4` |
| One step at source time t, where n = 2t + 1 | `(4t + 7)k + 4` |
| Recurrence | `S_k(t+1) = S_k(t) + (4t + 7)k + 4` |
| Closed form | `S_k(t) = 2kt² + (5k + 4)t + 2k + 2` |
| Uniform bound | `S_k(t) ≤ (9k + 6)(t + 1)²` |

These are proved by `sweep_step`, `sweepTime_eq`, and `sweepTime_le`. If the given
machine halts within `T(|x|)`, its least halting time `τ` satisfies
`τ ≤ T(|x|)`. The simulation reaches the matching halted configuration at
`S_k(τ)`; halt absorption identifies its output with `f x`. Monotonicity then
gives the required bound with constant `9k + 6`. No exact book constant or lower
bound on `T` is assumed.

Notation used here: `Γ` is the source alphabet, `Γ'` the enlarged alphabet,
`e` its symbol embedding, `k` the source work-tape count, `j` a source tape
coordinate, `i` a tape index, `t` elapsed source steps, `n` the current block count,
and `τ` the first source halt time.

## New private declarations

All 75 authored declarations below are `private`, in namespace
`Turing.FinTM`, and precede the target. Lines refer to the included complete
source. Descriptions reproduce the declaration documentation. All are technical
components of the existing [AB09, Claim 1.6] analogue, rather than new public claims.

| Declaration | Kind | Line | Role |
|---|---|---:|---|
| `unusedTapeTM` | def | 60 | Add one unused work tape to a machine with no work tapes. |
| `unusedTapeCfg` | def | 70 | The unused tape is blank and its head stays at the origin. |
| `unusedTape_step` | lemma | 75 | The zero-tape embedding commutes with a single transition, including halt. |
| `unusedTape_computes` | lemma | 93 | The zero-tape path is a lockstep simulation; no sweep or initialization is needed. |
| `sweepTape` | def | 107 | A finite tape zipper; the left list is stored nearest-cell first. |
| `sweepTape_read` | lemma | 112 | Read the current cell of a zipper. |
| `sweepTape_right` | lemma | 121 | A write followed by a right move transfers one cell to the left stack. |
| `sweepCfg` | def | 139 | A configuration at a sweep frontier, with arbitrary native input and output. |
| `sweepAct` | def | 144 | A sweep's local write, with the native input and output left stationary. |
| `sweepCfg_right` | lemma | 148 | The one-cell tape identity lifts to configurations. |
| `sweepFold` | def | 162 | A finite-state left-to-right transduction, recording both its final state and its rewritten word. |
| `sweep_run` | lemma | 175 | A local transition rule realizes a complete finite forward sweep. |
| `sweepRevCfg` | def | 205 | The same zipper viewed while scanning toward decreasing coordinates. |
| `sweepRevCfg_left` | lemma | 211 | Reflection converts the forward zipper identity into a left-moving step. |
| `sweep_run_reverse` | lemma | 228 | The finite transduction lemma for the return sweep, with the exact cost. |
| `sweepTape_turn` | lemma | 257 | Turning round exchanges the two finite stacks. |
| `sweepFold_append` | lemma | 269 | Concatenating two scans threads the finite control between them. |
| `indexedVisit` | def | 280 | A transducer whose state is a table, changing only the entry named by a cell. |
| `indexedFold` | lemma | 291 | On a block with distinct tape indices, each local rule sees the original table entry. This is the block invariant for both sweeps. |
| `indexedFold_block` | lemma | 318 | Each simulated tape contributes exactly one cell to an interleaved block. |
| `SweepCell` | abbrev | 328 | A cell stores a tape index, an optional payload, the head flag, and the left-neighbor head flag recorded by the forward sweep. |
| `readVisit` | def | 331 | The forward rule reads marked payloads and records the preceding head flag. |
| `writeVisit` | def | 339 | The return rule writes the old head's payload and determines the new head from the old flags at its left, current, and right neighbors. |
| `headAt` | def | 349 | The ghost head flag at a source coordinate. |
| `tapeRow` | def | 353 | One interleaved block; `read = true` includes the recorded left flag. |
| `readState` | def | 359 | The forward control immediately before reading block `j`. |
| `read_row` | lemma | 364 | Reading a whole block advances the control invariant by one coordinate. |
| `indexedFold_block_reverse` | lemma | 383 | The return sweep's block rule is valid in reverse tape-index order too. |
| `write_row` | lemma | 397 | A return-sweep block performs exactly the source action on that coordinate. |
| `tapeZone` | def | 425 | Consecutive interleaved blocks, in ascending coordinate order. |
| `read_zone` | lemma | 430 | The forward sweep processes any consecutive block interval. |
| `write_zone` | lemma | 442 | The return sweep processes the same interval in reverse order. |
| `sweepTape_nil` | lemma | 456 | One blank cell can be made explicit at the end of the zipper. |
| `sweepCfg_right_any` | lemma | 465 | The forward write identity also applies beyond the stored zone. |
| `sweepRevCfg_left_any` | lemma | 482 | The backward write identity also applies beyond the stored zone. |
| `sweep_generate` | lemma | 500 | A fixed finite sequence of writes, in either direction, takes its exact length. The hypothesis is the local controller rule, and has no global-run premise. |
| `SweepAlphabet` | abbrev | 523 | An enlarged symbol is input/output data, an internal cell, or a boundary. |
| `sweepEmbed` | def | 526 | Encode a source symbol as an unmarked data symbol. |
| `sweepBoundary` | def | 530 | A nonblank internal boundary, distinct from every payload (including blank). |
| `sweepSymbol` | def | 533 | Tag a complete internal cell. |
| `sweepInput` | def | 537 | Interpret the unchanged native input alphabet. |
| `SweepState` | inductive | 542 | Finite controller phases; unbounded coordinates never enter the state. |
| `sweepStateFintype` | instance | 551 | Enumerate the finite control through its finite sum/product representation. |
| `sweepStateDecidableEq` | instance | 555 | Equality of controller states is decidable through the same representation. |
| `sweepMove` | def | 562 | A stationary-input/output action that preserves the cell it scans. |
| `sweepTM` | def | 568 | The finite controller for the two sweeps and their boundary extensions. The forward sweep records left-neighbor flags in the cells. The backward sweep keeps right-neighbor flags in its control, so it needs no extra scan. |
| `source_bounds` | lemma | 619 | Source heads and nonblank cells stay within the elapsed-time interval. |
| `blankRow` | def | 653 | The initialized interleaving has `k` marked blank cells. |
| `tapeRow_blank` | lemma | 657 | A row outside both the source heads and the written support is blank. |
| `tapeRow_length` | lemma | 667 | The size of each block is the number of source tapes. |
| `tapeZone_length` | lemma | 672 | Zone length is the block count times the source tape count. |
| `tapeZone_append` | lemma | 682 | Split a zone at a block boundary. |
| `sweepPos` | def | 692 | The native input position is unchanged numerically by symbol embedding. |
| `sweepPos_move` | lemma | 697 | Input-head movement commutes with the unchanged-length symbol embedding. |
| `sweepInput_read` | lemma | 705 | The input read by an encoded configuration is the encoded source read. |
| `sweepStart` | def | 720 | Canonical configurations at the left boundary between simulated steps. |
| `sweepTape_write` | lemma | 729 | Replacing the current cell preserves both tails of the zipper. |
| `sweep_turn_left` | lemma | 743 | Write a boundary and turn from a forward scan into a backward scan. |
| `sweep_turn_right` | lemma | 756 | Write the left boundary and turn toward the first forward-scan cell. |
| `sweep_init_block` | lemma | 773 | Initialization writes the marked origin block in exactly `k` steps. |
| `sweep_grow_left_block` | lemma | 797 | Growing the left boundary writes exactly one reversed blank block. |
| `rightRow` | def | 822 | The right guard block records the flags from the last scanned block. |
| `sweep_grow_right_block` | lemma | 826 | Growing the right boundary writes one guard block, retaining the collected reads. |
| `sweepFold_id` | lemma | 850 | A sweep with the identity rule only changes the physical scan frontier. |
| `sweepRevCfg_write` | lemma | 857 | Writing without moving in a backward-facing zipper. |
| `sweep_init` | lemma | 874 | Initialization builds the marked origin block and both boundaries. |
| `sweepCfg_stay` | lemma | 924 | A stationary phase change preserves a forward-facing tape. |
| `sweepRevCfg_stay` | lemma | 930 | A stationary phase change preserves a backward-facing tape. |
| `sweep_prepare` | lemma | 942 | The first half of a simulated step grows the left guard and collects all marked source symbols. Its exact cost includes both phase changes. |
| `sweep_finish` | lemma | 1030 | The second half grows the right guard, executes the native input/output action once, rewrites the zone, and enters the next boundary configuration. |
| `sweep_step` | lemma | 1139 | One source transition is one bounded burst, preserving the complete zone shape and growing it by one block at each end. |
| `sweepTime` | def | 1157 | Exact transition count after a given number of source steps. |
| `sweepTime_eq` | lemma | 1162 | Summing the exact per-step costs gives a quadratic polynomial. |
| `sweepTime_le` | lemma | 1169 | A single constant bounds initialization and all sweeps, at every input size. |
| `sweep_run_to_halt` | lemma | 1188 | Up to the source's first halt, initialized runs agree at every macro boundary. |

`SweepState` also introduces the private constructors `init`, `back`, `growLeft`,
`read`, `growRight`, and `write`. Lean generates recursors, constructor theorems,
matchers, equation theorems, private proof auxiliaries, and the representation
used by the two private instances. The complete exact-name inventory is included
in the appendix and independently in `declarations.log`.

## Requested shared lemmas

These are requests for a later coordinated change; this batch keeps the private
copies above and changes no shared file.

| Suggested shared home | Private components to consider promoting | Purpose |
|---|---|---|
| `Simulation.lean` or a maintainer-approved sweep helper module | `sweepTape`, `sweepCfg`, `sweepRevCfg`, their write/move/turn lemmas, `sweepFold`, `sweep_run`, `sweep_run_reverse`, `sweep_generate` | Reusable finite-word sweep and generation proofs with exact costs and native input/output preservation. |
| `Simulation.lean` | `indexedVisit`, `indexedFold`, `indexedFold_block`, `indexedFold_block_reverse` | Independent finite-table updates over distinct tape indices. |
| `Simulation.lean` / `Finite.lean`, as maintainers choose | `unusedTapeTM`, `unusedTapeCfg`, `unusedTape_step`, `unusedTape_computes` | The zero-work-tape lockstep embedding into one unused work tape. |
| `Simulation.lean` | `source_bounds` | General elapsed-time head and support bounds on initially blank work tapes. |

## Escalations

No mathematical obstruction or statement change was needed.

**File size / future extraction:** the owned file is 1315 lines,
above policy §1's approximate 1000-line threshold. The proof is decomposed into
75 private components, including a generic sweep layer and two explicit
macro-step halves. A maintainership follow-up should move reusable sweep and
finite-table infrastructure into a shared location, then shorten this file's
imports and local proof. This delivery keeps the construction in the one owned
file as the batch explicitly requires; no unilateral file split or shared API
change has been made. This is a structural follow-up, not an unfilled proof.

## Docstring appendices

Only the following implementation note was appended to the existing target
sketch; its preceding paragraphs remain intact:

```text
**Implementation note.** The forward pass records the preceding block's head
flags in the cells; the return pass carries the following block's flags in its
finite control. This implements both movement directions using exactly the two
stated sweeps. Each macro-step extends the zone by one blank block at each end.
For positive `k`, initialization costs `2k + 2` transitions and source step `t`
costs `(4t + 7)k + 4`; `sweepTime_le` supplies the constant `9k + 6`.
The zero-tape branch is a separate lockstep embedding with constant `1`.
```

The new nontrivial helper proofs have their own local explanatory documentation,
including explicit sketches for the sweep invariant, block invariant, bounds,
initialization, both macro-step halves, and induction to halt.

## Verification evidence

The repository's prescribed `scripts/lean_check_tree.sh` was used throughout. It
deletes each old output before checking and rejects a nonzero Lean exit, an
`error:` diagnostic, or a missing fresh `.olean`. `lake build` was never run.

| Check | Outcome | Evidence |
|---|---|---|
| Bootstrap full chapter sweep | Exit 0; 24 modules; the original 9 sorry warnings | `bootstrap-sweep.log` |
| Final owned-module check | Exit 0; no output or warnings | `owned-check.log` |
| Downstream suffix after the owned module | Exit 0; all 15 downstream entries | `downstream-sweep.log` |
| Final full chapter sweep | Exit 0; 24 modules; zero `error:` lines | `final-sweep.log` |
| Final axiom scratch check | Exit 0 | `axioms.log`, `verification/Axioms.lean` |
| Module declaration inventory | Exit 0; 284 recorded constants | `declarations.log`, `verification/Declarations.lean` |
| Scope and frozen statements | All comparisons pass | `freeze-check.json` |
| Patch and bundle integrity | Replay/source comparisons pass | `package-check.json`, `bundle-verify.log` |

The complete final sweep output is attached without truncation. It contains
exactly these eight `declaration uses 'sorry'` warnings:

| Declaration | File under `TCSlib/Complexity/TuringMachine/` | Line |
|---|---|---:|
| `computesFunInTime_comp` | `Composition.lean` | 361 |
| `exists_comp_partial` | `Composition.lean` | 409 |
| `alphabet_reduction` | `Robustness/AlphabetReduction.lean` | 69 |
| `nonnegative_heads` | `Robustness/Bidirectional.lean` | 76 |
| `oblivious_of_mem_DTIME` | `Robustness/Oblivious.lean` | 109 |
| `exists_effectiveMachineCode` | `Encoding.lean` | 455 |
| `universal` | `Universal.lean` | 102 |
| `timed_universal` | `Universal.lean` | 165 |

There are also three pre-existing `Configuration.lean` linter warnings: two
unnecessary-sequence-focus warnings (lines 137 and 155) and one unused-variable
warning (line 140). There are no new owned-file warnings.

The exact final axiom output is:

```text
'Turing.FinTM.one_work_tape' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.one_work_tape_binary' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

`one_work_tape_binary` still depends on `sorryAx` because the separately owned
`alphabet_reduction` remains unfilled at this base. Its other input theorem,
`one_work_tape`, has no such dependency. Neither declaration was weakened.

The axiom and declaration probes were executed from scratch files outside the
repository, using exactly the check script's `LEAN_PATH` construction:

```bash
LP="$PWD/.lake/tcslib-check-oleans"
[ ! -d "$PWD/.lake/build/lib/lean" ] || LP="$LP:$PWD/.lake/build/lib/lean"
for d in "$PWD"/.lake/packages/*/.lake/build/lib/lean; do
  [ ! -d "$d" ] || LP="$LP:$d"
done
export LEAN_PATH="$LP"
lean /absolute/path/outside/repository/Axioms.lean
```

The final sweep command was:

```bash
( while read -r m; do
    bash scripts/lean_check_tree.sh "$m" || exit 1
  done < scripts/ab_ch1_module_order.txt )
```

### Environment

The pinned toolchain is `leanprover/lean4:v4.25.0`, compiler commit
`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`. Mathlib is pinned at
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. The repository toolchain and dependency manifest
were not changed. `lake exe cache get` was used for setup; after a slow broad
download was interrupted, the chapter's transitive dependency cache and the
additional precise imports were retrieved with targeted cache requests.

This container's process namespace required a small runtime compatibility shim:
the compiler's `readlink("/proc/<own-pid>/exe", ...)` lookup is mapped to
`readlink("/proc/self/exe", ...)`. The complete C source is attached as
`environment/lean_proc_compat.c`. It was compiled as a shared object and supplied
through `LD_PRELOAD` for Lean/Lake invocations. It affects executable-path
discovery only; all proofs were checked by the pinned Lean kernel. A conventional
environment does not need this shim. For an environment with the same procfs
issue, it can be rebuilt with:

```bash
cc -shared -fPIC -o /tmp/lean_proc_compat.so environment/lean_proc_compat.c -ldl
export LD_PRELOAD=/tmp/lean_proc_compat.so
```

## Archive, replay, and hashes

Required deliverables are at the archive root, except the complete source,
which retains its repository path. Additional audit evidence consists of
`bootstrap-sweep.log`, `owned-check.log`, `downstream-sweep.log`,
`declarations.log`, `freeze-check.json`, `verification-summary.json`,
`package-check.json`, `bundle-verify.log`, the two verification probe files,
and the compatibility-shim C source.

The patch and bundle were produced with the exact requested base range:

```bash
git format-patch 24687122 --stdout > epoch2-B.patch
git bundle create epoch2-B.bundle 24687122..fill/epoch2-B
```

The bundle is incremental and requires the base commit. To replay the patch in
an existing clone containing that base:

```bash
git switch -c review/epoch2-B 24687122
git am /absolute/path/to/epoch2-B.patch
```

Alternatively, import the commit from the bundle without a GitHub write:

```bash
git fetch /absolute/path/to/epoch2-B.bundle fill/epoch2-B:review/epoch2-B
```

An isolated worktree at the base was used to apply-check and apply the patch;
the resulting complete source matched the delivery source and committed blob
byte-for-byte. The bundle was verified against the base and imported into a
separate local ref; its commit and source tree matched the delivery commit.

`SHA256SUMS` contains a sorted SHA-256 entry for every other archive file, with
paths relative to the archive root. As with a standard checksum manifest, it
excludes itself: a literal checksum of the manifest inside itself is a
self-reference and is not a practical hash-manifest format. Run
`sha256sum -c SHA256SUMS` after extraction. ZIP integrity, member set, and all
manifest hashes were checked before delivery.

## Appendix: complete module declaration inventory

The following is the complete sorted output of the attached Lean environment
probe. It contains 280 private constants, including the 75
authored declarations and all generated auxiliaries; the two existing public
headline theorems; and `Turing.Cfg.workTapeSymbols.eq_1` and
`Turing.MultiTapeTM.step.eq_1`, the lazily materialized equation theorems for
unchanged imported definitions. Those two equation theorems are not newly
authored public helpers. No public `SweepState` instance or other new public
helper is introduced.

```text
Turing.Cfg.workTapeSymbols.eq_1
Turing.FinTM.one_work_tape
Turing.FinTM.one_work_tape_binary
Turing.MultiTapeTM.step.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.SignType.fin3Equiv.match_1.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.SignType.fin3Equiv.match_1.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.SignType.fin3Equiv.match_1.eq_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.SignType.fin3Equiv.match_1.splitter
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.Action.apply.match_1.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.Action.apply.match_1.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.Action.apply.match_1.splitter
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepAlphabet
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepCell
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState._sizeOf_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState._sizeOf_inst
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.back
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.back.elim
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.back.sizeOf_spec
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.casesOn
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.ctorElim
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.ctorElimType
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.ctorIdx
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growLeft
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growLeft.elim
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growLeft.inj
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growLeft.injEq
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growLeft.noConfusion
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growLeft.sizeOf_spec
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growRight
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growRight.elim
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growRight.inj
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growRight.injEq
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growRight.noConfusion
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.growRight.sizeOf_spec
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.init
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.init.elim
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.init.inj
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.init.injEq
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.init.noConfusion
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.init.sizeOf_spec
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.noConfusion
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.noConfusionType
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.proxyType
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.proxyTypeEquiv
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.read
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.read.elim
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.read.inj
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.read.injEq
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.read.noConfusion
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.read.sizeOf_spec
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.rec
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.recOn
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.write
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.write.elim
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.write.inj
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.write.injEq
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.write.noConfusion
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.SweepState.write.sizeOf_spec
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.blankRow
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.blankRow.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.headAt
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.headAt.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.indexedFold
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.indexedFold._simp_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.indexedFold_block
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.indexedFold_block._simp_1_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.indexedFold_block_reverse
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.indexedFold_block_reverse._simp_1_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.indexedFold_block_reverse._simp_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.indexedVisit
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.indexedVisit.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.readState
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.readState.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.readVisit
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.read_row
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.read_row._proof_1_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.read_zone
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.read_zone._proof_1_7
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.rightRow
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.rightRow.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.source_bounds
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.source_bounds._proof_1_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.source_bounds._proof_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.source_bounds._proof_1_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepAct
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepAct.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepBoundary
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepCfg
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepCfg.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepCfg_right
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepCfg_right_any
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepCfg_stay
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepEmbed
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepEmbed._proof_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepEmbed.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold._sunfold
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold._unsafe_rec
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold.eq_def
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold.match_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold.match_1.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold.match_1.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold.match_1.splitter
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold_append
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepFold_id
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput.match_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput.match_1.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput.match_1.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput.match_1.splitter
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput_read
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepInput_read._simp_1_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepMove
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepMove.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepPos
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepPos._proof_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepPos.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepPos_move
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepRevCfg
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepRevCfg.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepRevCfg_left
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepRevCfg_left._proof_1_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepRevCfg_left._simp_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepRevCfg_left_any
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepRevCfg_stay
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepRevCfg_write
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepRevCfg_write._simp_1_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStart
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateDecidableEq
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateFintype
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateFintype.match_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepStateFintype.match_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepSymbol
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM._proof_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM._proof_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM._proof_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM._proof_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM._proof_7
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM._proof_8
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_1.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_1.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_1.splitter
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_3.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_3.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_3.splitter
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5.eq_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5.eq_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5.eq_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5.eq_6
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTM.match_5.splitter
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_nil
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_read
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_read._simp_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_right
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_right._proof_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_right._proof_1_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_right._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_right._proof_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_turn
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_turn._proof_1_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_turn._proof_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_turn._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_turn._proof_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_write
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTape_write._proof_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime._sunfold
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime._unsafe_rec
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime.eq_def
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime_eq
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweepTime_le
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_finish
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_finish._proof_1_15
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_finish._proof_1_17
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_finish._proof_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_finish._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_finish._proof_1_8
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_finish._simp_1_10
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_finish._simp_1_16
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_generate
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_generate._proof_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_generate._proof_1_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_generate._proof_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_generate._proof_1_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_generate._proof_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_generate._proof_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_generate._simp_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_left_block
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_left_block._proof_1_10
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_left_block._proof_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_left_block._proof_1_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_left_block._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_left_block._proof_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_right_block
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_right_block._proof_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_right_block._proof_1_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_right_block._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_grow_right_block._proof_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_init
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_init._proof_1_14
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_init._proof_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_init._simp_1_7
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_init_block
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_init_block._proof_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_init_block._proof_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_init_block._proof_1_3
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_init_block._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_init_block._proof_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_prepare
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_prepare._proof_1_15
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_prepare._proof_1_16
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_prepare._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_prepare._proof_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_prepare._proof_1_8
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_prepare._proof_1_9
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_prepare._simp_1_11
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_reverse
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_reverse._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_to_halt
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_to_halt._proof_1_10
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_to_halt._proof_1_11
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_to_halt._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_to_halt._proof_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_to_halt._proof_1_6
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_to_halt._proof_1_7
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_to_halt._proof_1_8
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_run_to_halt._proof_1_9
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_step
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_turn_left
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_turn_right
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_turn_right._proof_1_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.sweep_turn_right._simp_1_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeRow
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeRow.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeRow_blank
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeRow_length
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone._sunfold
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone._unsafe_rec
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.eq_def
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.match_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.match_1.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.match_1.eq_2
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone.match_1.splitter
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone_append
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone_append._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone_append._proof_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone_length
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.tapeZone_length._proof_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.unusedTapeCfg
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.unusedTapeCfg.eq_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.unusedTapeTM
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.unusedTapeTM.congr_simp
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.unusedTape_computes
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.unusedTape_step
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.writeVisit
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.writeVisit.match_1
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.write_row
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.write_row._proof_1_5
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.write_row._proof_1_6
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.write_row._proof_1_7
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.write_row._simp_1_4
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.write_zone
_private.TCSlib.Complexity.TuringMachine.Robustness.SingleTape.0.Turing.FinTM.write_zone._proof_1_7
```
