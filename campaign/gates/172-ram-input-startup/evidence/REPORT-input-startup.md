# Input-bit and RAM startup — final round 2 delivery

Both requested theorems are proved modulo only the explicitly permitted word-arithmetic and
keyed-assignment rows. There are no admissions in either owned file. All final checks pass.

Base: `7342f98b58704d6c25faf668ed1a64ea0b27c4af` (`ram/readers-2`, PR #375), fetched read-only. Source commit:
`6ebc27ff461ca1ebc611d15bcc448b217051906d` on local branch `codex/fill-ram-input-startup-r2`. The source branch was neither
rebased nor pushed. Rules and brief were read at
`e40383d88d79e23026c95e20608ee8827d45e59b`. The earlier dispatch bundle was checked in round 1;
round 2 retrieved the round-1 archive from the exchange, verified all 189 member checksums,
and applied its patch to this new base before continuing. This archive's patch is against
the new base, not the old round-1 base.

Delivery destination: `exchange/pass-shelat-ch5-8`,
`arora-barak-ch3-4/inbox/fill-ram-input-startup/fill-ram-input-startup-r2.zip`.
The delivery checkout is separate from the source checkout and uses pull/rebase before push;
no force push or PR is part of this delivery. Checkpoint 1 was already delivered there as
`fill-ram-input-startup-r2-checkpoint-1.zip`, SHA256
`292c5b6e49086ba4b8b59b60107f49f7a0c7ac31db040ab6d43e14fb1d5b0467`,
exchange delivery commit `fb6682950fbb2a683fa8be54a20d9dc9cddb2f96`.

## Targets and admitted dependencies

| Target | Result | Reachable direct admissions |
| --- | --- | --- |
| `Turing.exists_inputBitTM` | Proved, statement byte-identical | `Turing.exists_wordIntTM`, `Turing.exists_wordSignTM` |
| `WordRAM.Sim.exists_startup` | Proved, statement byte-identical | `Turing.exists_keyAssignTM`, `Turing.exists_wordIntTM` |

Neither proof reaches an admitted `Build/RecordTable` declaration. The dependency walks traverse
types and values, identify constants that directly use `sorryAx`, and assert the exact permitted
sets. The printed results are:

```text
'Turing.exists_inputBitTM' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
WALK|Turing.exists_inputBitTM|[Turing.exists_wordIntTM, Turing.exists_wordSignTM]
ADMISSION_SET_OK
'WordRAM.Sim.exists_startup' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
WALK|WordRAM.Sim.exists_startup|[Turing.exists_keyAssignTM, Turing.exists_wordIntTM]
ADMISSION_SET_OK
```

## Input-bit construction and reuse

The equality comparator against empty scratch handles width zero. The permitted sign row
handles negative indices. The private unequal-width numeric comparator scans little-endian
words while retaining the highest differing bit pair, then uses two catalog backward skips
to restore both heads. The catalog comparator supplies equality, not this numeric verdict.

For an in-range nonnegative index, catalog copy and successful increment prepare the seek
word. The existing two-tape native seek is embedded on scratch tapes 3/4; catalog clear restores
those tapes. A fixed stationary native-input verdict selects the permitted zero/one integer
writers. No catalog leaf returns that verdict without moving a head. Calls compose through
`Contract.ofReaches`, `seq`, `branch` and `inPhase`; no replacement dispatch host was written.
The seek's linear input-time bound is kept separate from its small work radius.

### Requested shared lemma

`inputBit_increment_value` is the explicitly authorized fresh private induction:
`incFixed w = some v → Nat.ofDigits 2 (v.map Bool.toNat) = Nat.ofDigits 2 (w.map Bool.toNat) + 1`.
It uses the published nil/false-cons/true-cons equations of `incFixed`, without copying the
private proof in CodeSimulator. **Requested shared lemma:** publish `incFixed_value` in
Build/Convention and retire both private copies, as requested in the dispatch.

## Startup construction and bounds

The returning silent embedding captures the width witness's output at its first live exit.
Its visited-set lemmas count the witness bank exactly once. The sum over the actual tape
partition gives the witness's original space plus a constant times `|bits W| + 1`.

A fixed one-step native advance ensures positivity even when the witness finishes at input
position zero. The published input rewind then returns to position one. The published input
length row runs in its own blank bank; its logarithmic work radius is preserved separately
from its linear time through the contract composition.

The ordinary preparation uses ten selected tapes: the eight simulation tapes, the captured
width master, and a reusable counter. It rewinds the master, copies it to the counter, expands
`W` zero cells using `expandTM`, rewinds the register and copies its zero word to the two
other registers. A fixed advancing writer supplies the key's `a` cells; a second counter copy
and expansion supply its `W` cells. The writer is routed through `ReturnContract.release`,
retaining its positive first return rather than treating a cyclic anchor as an ordinary exit.
The permitted integer row installs the key of `-1`.

Copying the full binary length over the zero register pads short words and temporarily leaves
long words beyond width `W`. A catalog walk guided by the width register reaches `W + 1`.
A fixed two-action leaf erases the preceding cell and restores the head; catalog backward
skips then restore both heads. The register predicate only needs the two delimiters, so the
unused tail remains framed beyond cell `W`. `startup_padded_low` proves the register is exactly
the low-width length word, including width zero. No truncating-copy host or suffix-clearing
routine is introduced.

The permitted keyed assignment installs the singleton in the buffered empty table. The range
fact follows from `inRange_iff` for every positive key width, including `W = 0, a = 1`.
All first-eight heads return to zero, both scratch tapes are globally blank, and physical output
is empty in either output mode. `startup_finished_encodes` verifies the complete initial RAM
encoding.

The only new startup transition tables are the one-step native advance and the two-step
previous-cell erasure; their docstrings state the missing catalog operation. All other runtime
composition uses the existing contract and seam hosts. The native length radius plus the
ordinary preparation's time-derived radius is `O(W + |bits |x|| + 1)`. The final shared seam
space sum therefore gives **`sw + C * (W + |bits |x|| + 1)`**, with coefficient exactly one on
`sw`. Time is weakened to `tw + C * (|x| + W² + 1)` using `|bits n| ≤ n` and `W ≤ W²`.

## Authorized exact readers and imports

The tier-2 missing-reader exception was used only for these four pure restatements, all with
proof `rfl`, beside the definitions in their home files, without simp attributes:

| Reader | Home file | Reads |
| --- | --- | --- |
| `Turing.Cfg.select_eq` | `TCSlib/Complexity/TuringMachine/Build/Embed.lean` | Exact selected configuration, including empty source output |
| `Turing.Contract.embed_pre` | `TCSlib/Complexity/TuringMachine/Build/Contract/Embed.lean` | Embedded precondition |
| `Turing.Contract.embed_time` | same | Embedded chosen time |
| `Turing.Contract.embed_post` | same | Embedded physical endpoint |

These were absent from the pinned base, including PR #375, before they were added. Every
existing declaration in both home files is unchanged. Every other new library declaration
is private and in an owned file. There are no new library files or global simp attributes.

InputBit adds `Build.Contract` for shared composition and `Build.SeamLayout` to expose the
existing BufferWords off-buffer blank theorem. Startup adds `Build.Contract` for shared
composition, `Build.InterpreterStartup` for the published returning capture/initialization
lemmas, and `RAMSimulation.WordSize` for the published monotonic space API through its import
closure. The original imports are retained.

## Searches, foreign definitions and published readers

Searches covered the imported catalog, contract, counter-loop, input-call/input-length,
embedding, word-arithmetic, keyed-table, buffer/layout and core bit-vector APIs before adding
helpers. The declaration ledger below gives each helper's particular role; the following
families describe the existing facts searched and used by those helpers.

- Comparison: catalog comparison is equality. The new numeric verdict uses a fresh list
  induction and the public `Nat.ofDigits_cons` arithmetic; restoration cites `skipBackTM`.
- Increment: searched Convention and CodeSimulator. The needed value law was private and is
  reproduced only under the dispatch's explicit exception; the other increment facts cite
  the published equations, nonoverflow characterization and `incFixed_length`.
- Buffer replacement: inspected `wordPatch_append`, `wordPatch_self`, `wordPatch_twice`,
  `wordPatch_frame` and `wordPatch_replicate`. The general unequal-length prefix overlay is a
  private cell identity; adjacent appending cites `wordPatch_append`. Existing buffer clipping
  and off-buffer blank lemmas are cited rather than duplicated.
- Fixed actions: searched the catalog input and tape actions, writer/scan/seek rows, and their
  contracts. No row supplies the stationary input verdict, positive-input advance, or previous-
  cell erase/return operation. Their small leaves use the public one-step action equations.
- Layout: inspected `joinFields_singleton`, `joinFields_cons_cons`, `fieldsTape_of_nonneg`,
  `fieldsTape_of_neg`, `fieldsTape_of_length_le`, `tableFields_eq` and table predicate readers.
  The empty/singleton keyed-table facts specialize those APIs, without invoking admitted record
  table machines.
- Bit-vector and input-length arithmetic: uses `bvBits_def`, `bvBits_length`, core signed-value
  and bit-access lemmas, `BitVec.ofInt_natCast`, `Nat.testBit_eq_inth`, `counterValue_eq`,
  `counterValue_bits`, `counterOverhead_le` and `length_bits_le_self`.
- Runtime calls: `copyTM`, `clearTM`, `incrementTM`, `compareTM`, `skipBackTM` and their contracts
  are read through the contracts' pre/time/post/lo/hi equations. `walkTM_contract` uses its
  published pre/time/post equations. `rewindTM` and `writeAdvTM` use their public framed runs.
- Contract hosts: `Contract.ofReaches` uses its published field equations and time bound;
  `Contract.seq`, `branch`, `inPhase` use their field equations and trajectory compositions;
  `Contract.embed` uses the four authorized/new and existing public interfaces;
  `ReturnContract.release` uses its pre/time/post equations. Private stage/route records carry
  specifications only; their machines are the shared hosts.
- `Cfg.mapState`, `Cfg.bindState`, `Cfg.init`, `Cfg.inputSymbol` and `MultiTapeTM.initCfg` use
  their published field, congruence, initialization and input-symbol readers. Whole-tape
  equalities are proved pointwise using the tape-cell reader.
- `MultiTapeTM.step`, `Action.apply`, `inputMoveAction`, `tapeAction` use the published step and
  action field readers. Runs use zero/one/successor equations and `catalog_trace_run` with
  `catalogTrace_eq`; no foreign transition table is unfolded.
- `embedEmitTM` and `embedSilentRetTM` use the public run/first-return lemmas. Forwarding
  configurations use `embedEmitCfg_eq`, `embedEmitCfg_mapState_eq`, selected/unselected field
  equations and `embedEmitCfg_select`. Silent capture uses `embedSilentCfg_initCfg`,
  `embedSilentCfg_cap`, returning visited-set equality, selected-bank visited sets, the frame
  singleton and the capture-space bound.
- `expandTM`, `counterLoopCfg` and `counterLoopBody` use `expandTM_run` and the published body
  reconstruction/state/input/tape/head/output equations. The loop's amortized bound is cited.
- `WordAt`, `ScratchBlank`, `ReachesWithin`, `TableAt`, `KeyTableAt`, `TableOf`, `Encodes` and
  `InRange` use their `_iff` readers. `wordWrite`, `keyTableWrite`, `keyAssign`, `keyFields`,
  `keyTableLength`, `keyBits`, `initMem` and `XCfg.init` use their published apply/definition
  equations. The transparent word constructor abbreviation is converted using core bit-vector
  equations.
- Visited space uses `spaceUsed_eq_sum`, `spaceUsedByTape_eq_card`, embedding visited-set and
  frame lemmas, `spaceUsed_mono`, `spaceUsed_le_of_abs_le`, and
  `seamCompTM_spaceUsed_le_add_ofCfg`. General-configuration seam run and first-return lemmas
  supply the final machine's exact endpoint and strict cut.

The sealed mirrors make all valid public ordinary imported TCSlib definition names
irreducible: 425 for InputBit and 722 for Startup, including unused definitions. They remove
three active definition simp rules and assert every seal. Startup's inventory separately lists
one generated hygienic internal matcher whose name is not a source-level API identifier;
it is excluded from the attribute list. Private imported names, projections and transparent
aliases are outside the ordinary-definition inventory. The strict tactic-argument audit
checks that direct rewrite/simp arguments name no foreign/core/Mathlib definitions; it excludes
procedural simproc hints and nested term arguments. Core/Mathlib values reduce only through
permitted computation or published equations.

## Verification and environment

Final checks, all in `evidence/logs/final/`:

| Check | Exit/result |
| --- | --- |
| Both reader home modules and contract facade | 0 |
| InputBit and Startup native elaboration | 0, **zero warnings** |
| Both complete sealed replays | 0, seal guards passed |
| Both axiom/dependency walks | 0, exact allowed admission sets |
| Direct tactic-definition audit | 0 |
| Both negative seal controls | **1 expected**, `rfl` cannot read sealed `bvBits` |
| Sim/Phases, Simulation, Classes, RAMSimulation facade, TuringMachine facade | 0 |
| Literal target statements and existing declarations | frozen |
| Patch check plus actual four-file replay | 0; bytes match delivered SHA256 |

The five downstream modules are exactly the reverse import closure of the owned files after
excluding the standing-workflow root `TCSlib` facade; both owned files are checked separately.
The isolated import cache was bootstrapped earlier: 129 TCSlib modules in the complete required
closure, 53 present Mathlib roots, the initial 45-module bootstrap plus additional prerequisites.
The archive includes those unchanged-prerequisite logs separately as cache-bootstrap evidence;
final proof validation is exclusively in the final logs, whose source hashes match this delivery.
Unrelated base admissions may warn in prerequisite logs. No owned proof emits an admission warning.

Every Lean launch checks the machine-wide executable-name count below three, runs at most one
of ours, and uses `nice -n 10`, Lean `-j4`, and the isolated
`.lake/fill-ram-input-startup-r2-oleans` tree. The process log contains 294
count samples, including 3 wait/recheck samples at the limit. No `lake build`
was run. Exact package revisions match the manifest. This host is macOS ARM64; native
`vm_stat`, `memory_pressure` and `/usr/bin/time -l` replace Linux procfs/time fields. Preflight
records 12 CPUs, 18 GiB RAM, about 117.8 GiB free disk and conservative headroom above 3 GiB.
Native time/RSS records accompany every check.

InputBit is 2055 lines and Startup is
2836 lines. Both exceed 1,500 lines, as permitted by the tier-2
addendum; the maintainer can split them at landing. All proofs over twenty lines have named
proof sketches. New library documentation contains no campaign labels. Unrelated generated
blueprint changes and the untracked evidence directory are excluded from the source commit
and patch.

```
 TCSlib/Complexity/RAMSimulation/Sim/Startup.lean   | 2794 +++++++++++++++++++-
 .../TuringMachine/Build/Contract/Embed.lean        |   19 +
 TCSlib/Complexity/TuringMachine/Build/Embed.lean   |    7 +
 .../Complexity/TuringMachine/Build/InputBit.lean   | 2005 +++++++++++++-
 4 files changed, 4798 insertions(+), 27 deletions(-)
```

## Delivered source hashes

| File | Lines | SHA256 |
| --- | ---: | --- |
| `TCSlib/Complexity/TuringMachine/Build/InputBit.lean` | 2055 | `250f329a099e7b6dda8126eb0074e6225cb8737ac9d3f3c78a550f179034d0a1` |
| `TCSlib/Complexity/RAMSimulation/Sim/Startup.lean` | 2836 | `a50e9ac39d02ffb4f6a80b4899b10f2667498427c5438ee92120d8585bcfceea` |
| `TCSlib/Complexity/TuringMachine/Build/Embed.lean` | 1177 | `9be234e9924457fa39de90fc6069364d7302132425089eccee6184fb684ffdb6` |
| `TCSlib/Complexity/TuringMachine/Build/Contract/Embed.lean` | 149 | `1f8b7f5cff36b77a644b7254ecce5f78ccaaadebdc247bb39417a00e55c7b04b` |

## New private declaration ledger

There are 237 new private declarations across the two owned files. Each role below
comes from its declaration's documentation; the delivered source contains its proof and named
API references.

- `Turing.inputBitOrder` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The remembered order after scanning two little-endian words. Missing high digits are zero, and a higher unequal pair replaces the order remembered from the lower digits.
- `Turing.inputBitOrder_spec` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The remembered comparison equals the order of the words' values; the incoming comparison breaks ties. This includes unequal word lengths and high zero padding.
- `Turing.inputBitOrder_lt` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Starting with equality compares the unsigned values of any two bit lists.
- `Turing.inputBitNext` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): A higher unequal digit pair decides the order of two little-endian prefixes.
- `Turing.inputBitPrefix` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The remembered order after `r` synchronized input-word positions.
- `Turing.inputBitPrefix_shift` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Processing the first digit pair first shifts the rest of the prefix scan to the tails.
- `Turing.inputBitPrefix_complete` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Scanning through the longer word computes the full unsigned comparison.
- `Turing.InputBitComparePhase` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The comparison sweep carries the remembered order and then returns it at an exit.
- `Turing.inputBitCompareForward` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): A read-only comparison pass over tapes zero and one. The catalog's `compareTM` tests equality and stops at its first differing cell; no row compares unequal-width numeric words. This pass remembers the highest unequal bit pair, parking a head at its right delimiter while the other word continues. Its exit advances both heads one cell beyond the delimiters, so the published `skipBackTM` can restore each head.
- `Turing.inputBitCompareCfg` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The forward sweep at index `r`: each head stops advancing at its word's delimiter.
- `Turing.inputBitCompareDone` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The forward comparison's exit, one cell beyond each right delimiter.
- `Turing.inputBit_move_step` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): A nonwriting action with an arbitrary work-head displacement vector preserves all data. The published one-tape action lemmas do not cover the comparison's two moving heads.
- `Turing.inputBitCompareCfg_reads` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The two parked-or-advancing heads read the corresponding optional digits.
- `Turing.inputBitCompareForward_step` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): One forward comparison step advances each unfinished word head and updates the order.
- `Turing.inputBitCompareForward_turn` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): At both delimiters the comparison exits with the complete remembered order.
- `Turing.inputBitCompareForward_reaches` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The forward comparison has a first exit after the longer word's length plus one step.
- `Turing.inputBitContractOn` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Reindex a contract while retaining an additional invariant in its precondition.
- `Turing.inputBit_mapState_heads` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The published pointwise state-map head reader also identifies the whole head vector.
- `Turing.inputBit_mapState_tapes` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The pointwise tape reader identifies the whole unchanged tape bank.
- `Turing.inputBit_seekPost_heads` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The published seek endpoint reader identifies its whole updated head vector.
- `Turing.inputBitCompareBack` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The two published backward skips restore the two comparison heads in sequence.
- `Turing.inputBitCompareBackContract` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The restoration contract retains both word premises and uses the catalog rows.
- `Turing.inputBitCompareBack_pre` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The backward composite requires the two words immediately before their parked heads.
- `Turing.inputBitCompareBack_post` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The two backward skips preserve all data and subtract each word length plus one.
- `Turing.inputBitCompareBack_time` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The two backward skips cost the sum of the word lengths plus seven steps.
- `Turing.inputBitCompareForwardContract` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The numeric comparison pass as a composable framed contract.
- `Turing.inputBitCompare_link` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The forward exit places both delimited words exactly where the backward skips expect.
- `Turing.InputBitCompareState` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The comparison control consists of its forward pass and the two tagged restorations.
- `Turing.inputBitCompareTM` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The comparison first branches on its remembered order, then restores both heads.
- `Turing.inputBitCompareEntry` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The comparison entry is the false-initialized forward scan.
- `Turing.inputBitCompareExit` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The tagged backward exit retains the comparison result in finite control.
- `Turing.inputBitCompareExits` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The exit set supplied by the branch contract, before simplifying the two images.
- `Turing.inputBitCompareContract` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The complete comparison contract composes one forward pass with a tagged restoration.
- `Turing.inputBitCompare_pre` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The complete comparison has exactly the original two-word precondition.
- `Turing.inputBitCompareForward_time_le` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The chosen running time of the forward contract is at most its stated linear bound.
- `Turing.inputBitCompare_time_le` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The full comparison, including both head restorations, has linear running time.
- `Turing.inputBitCompareExits_eq` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The branch contract's image exits are exactly the false and true comparison anchors.
- `Turing.inputBitCompare_post` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The complete comparison restores both heads and all data, retaining only its verdict.
- `Turing.inputBitCompare_reaches` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Comparing two unequal-width words preserves every physical field and returns their unsigned order in linear time and radius.
- `Turing.inputBit_bvBits_cons` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Adding a most-significant bit appends it to the little-endian tape word.
- `Turing.inputBit_bvBits_value` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The unsigned value of a word's tape bits is its `BitVec.toNat` value.
- `Turing.inputBit_seek_row` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The native seek's framed conclusion is a `ReachesWithin` row. The input position in the endpoint is the unique position with value `p`, and all work-tape contents are restored.
- `Turing.inputBit_increment_exists` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): A nonoverflowing bit list has a successor of exactly the same width.
- `Turing.inputBit_increment_value` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): A successful fixed-width increment adds one to the unsigned value of the bits.
- `Turing.inputBitSuccBits` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The fixed-width successor bits used by the input-head counter.
- `Turing.inputBitSuccBits_spec` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): A positive-width nonnegative signed position has a nonoverflowing successor counter.
- `Turing.inputBit_exists_seek_row` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): A native seek witness with the endpoint and the head envelope packaged for composition. Its position word is restored, its scratch tape remains blank, and the input head lands at `p`.
- `Turing.InputBitData` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The physical fields of a reader configuration, independent of its control states.
- `Turing.InputBitData.cfg` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Attach a live control state to physical fields.
- `Turing.InputBitData.ofCfg` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Forget a configuration's control state.
- `Turing.InputBitData.ofCfg_cfg` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Forgetting an attached state recovers the physical fields.
- `Turing.InputBitData.cfg_ofCfg` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Reattaching a configuration's live state recovers it.
- `Turing.InputBitData.cfg_mapState` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Re-tagging a live configuration only changes its attached state.
- `Turing.InputBitData.ofCfg_mapState` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Forgetting control is invariant under a re-tagging.
- `Turing.InputBitCall` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): A single-exit catalog composition with a state-independent physical specification. The head-return clause lets subsequent calls use the same origins.
- `Turing.InputBitCall.contract` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Package a physical call as the published `Contract.ofReaches` adapter.
- `Turing.InputBitCall.time_le` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The call's chosen contract time obeys its advertised bound.
- `Turing.InputBitCall.seq` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Sequence two head-returning calls with the published seam host.
- `Turing.InputBitCall.adapt` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Strengthen a call's precondition, identify its physical endpoint and enlarge its bounds.
- `Turing.InputBitJoinPhase` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The original machine and a terminal catalog phase used to identify live exits.
- `Turing.inputBitJoinMachines` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Place a source machine beside the terminal phase in the published phase host.
- `Turing.inputBitJoinRed` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Redirect exactly the live exits to one terminal anchor.
- `Turing.InputBitCall.close` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Identify a finite family's live exits using `Contract.inPhase`.
- `Turing.InputBitCall.branch` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Compose a read-only test with two calls and identify the resulting exits.
- `Turing.InputBitCall.ofContract` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Use a catalog contract with a bounded time as a head-returning call.
- `Turing.InputBitData.scratch` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Install a globally delimited scratch word at tape three's current origin.
- `Turing.InputBitData.hasScratch` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Whether tape three globally holds a scratch word.
- `Turing.InputBitData.wordAt` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): `WordAt` does not inspect the attached control state.
- `Turing.InputBitData.blank` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The scratch-tape predicate does not inspect the attached control state.
- `Turing.InputBitData.scratch_wordAt` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): A globally stored scratch word is delimited at its origin.
- `Turing.InputBitData.hasScratch_scratch` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Installing a scratch word satisfies its global specification.
- `Turing.InputBitData.hasScratch_nil` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): A globally blank tape three is the empty scratch word.
- `Turing.InputBitData.scratch_nil` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Emptying an originally blank scratch tape recovers all physical fields.
- `Turing.InputBitData.scratch_twice` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): A second scratch installation keeps only the final word.
- `Turing.InputBitData.write_scratch` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Writing a same-width replacement over a globally stored word installs exactly the new scratch word; writing the first word into an empty scratch tape does too.
- `Turing.InputBitArgs` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The logical parameters shared by the calls in one input-read operation.
- `Turing.inputBitReady` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The external tape precondition, with the control state forgotten.
- `Turing.inputBitCopyCall` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Copy the position word to the globally blank scratch tape using the catalog row.
- `Turing.inputBitIncrementCall` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Increment the copied nonnegative positive-width position using the catalog counter.
- `Turing.inputBitClearCall` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Clear the globally stored successor counter with the catalog's clearing sweep.
- `Turing.inputBitWrite` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Replace the register by a Boolean integer constant, leaving its surroundings framed.
- `Turing.inputBitConstantCall` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The permitted integer-constant row supplies each branch's register writer.
- `Turing.inputBitCanRead` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The in-range case of a positive-width, nonnegative signed index.
- `Turing.inputBitSeek` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Move the input head to the index's shifted input position; outside the intended precondition the minimum merely keeps the configuration well typed.
- `Turing.inputBitSeekCall` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Place the restored two-tape native seek on scratch tapes three and four.
- `Turing.inputBitSeek_scratch` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): A scratch installation commutes with the input-only head change.
- `Turing.inputBitReady_seek` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Seeking does not change the work-tape precondition.
- `Turing.inputBitValidSeekCall` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The whole valid-index seek: copy, increment, native seek, and erase the scratch counter.
- `Turing.inputBitNativeBit` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The bit currently under the native input head, with blanks read as false.
- `Turing.inputBitReadTM` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): A one-step native-input test. No catalog row returns a Boolean native-input read as a verdict without moving a head; this leaf only uses the published stationary input action.
- `Turing.inputBitRead_reaches` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Read the native bit without changing any physical field.
- `Turing.inputBitNativeBit_seek` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The shifted seek position reads precisely the requested list digit.
- `Turing.inputBitTest_ofContract` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Derive a read-only verdict row from a catalog contract and its endpoint equation.
- `Turing.inputBitWidth_reaches` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The catalog equality comparator detects width zero by comparing with blank scratch.
- `Turing.inputBitOrder_index` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Unsigned tape comparison agrees with the signed natural index when its sign is clear.
- `Turing.inputBitReadWriteCall` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Read the current native bit and write its Boolean word using the two constant rows.
- `Turing.inputBitAnswer` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The Boolean answer specified by a signed input read.
- `Turing.inputBitResult` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The finished physical data, retaining whichever input position the selected path used.
- `Turing.inputBitAnswer_nonneg` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): With a nonnegative index, the Boolean answer is the requested list digit.
- `Turing.inputBitResult_negative` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): Negative indices take the zero-writing path without seeking.
- `Turing.inputBitResult_past` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): An index past the input takes the zero-writing path without seeking.
- `Turing.inputBitWrite_width_zero` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): At width zero every Boolean constant is the same empty register word.
- `Turing.inputBitResult_width_zero` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The width-zero branch can always write zero.
- `Turing.inputBitValidReadCall` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): A complete valid-index input read, with scratch already cleared before the bit test.
- `Turing.inputBitRangeCall` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The range decision: read a valid index and write zero for a position past the input.
- `Turing.inputBitSignCall` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The signed decision: a negative index writes zero, and a nonnegative index tests its range.
- `Turing.inputBitFullCall` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The full reader call, including the empty-width boundary case.
- `Turing.inputBitResult_cfg` (TCSlib/Complexity/TuringMachine/Build/InputBit.lean): The physical result has precisely the public row's framed endpoint shape.
- `WordRAM.Sim.startup_initMem_neg_one` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The marked startup entry stores the length word at the distinguished cell.
- `WordRAM.Sim.startup_initMem_of_ne` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Every other startup cell holds zero.
- `WordRAM.Sim.startup_tableOf` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The singleton table is the initial memory as soon as the distinguished cell's signed range obligation is supplied. This isolates that obligation from the tape construction.
- `WordRAM.Sim.startup_inRange_neg_one` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Every positive width represents `-1`, including the single-bit boundary.
- `WordRAM.Sim.startup_inRange_neg_one_of_two_le` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Every width at least two represents `-1` in the signed range.
- `WordRAM.Sim.startup_encodes_of_tapes` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The finished eight tapes encode the initial RAM configuration once the distinguished address's range fact is supplied.
- `WordRAM.Sim.startup_lengthWord` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The length word consists of the low input-length bits, padded by false bits to its width.
- `WordRAM.Sim.startup_capture` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The shared returning silent embedding captures the width witness at its first live exit.
- `WordRAM.Sim.startupBank` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Place the width witness after the eight simulation tapes, before the auxiliary bank.
- `WordRAM.Sim.startupCaptureIndex` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The capture tape is the first tape of the final auxiliary bank.
- `WordRAM.Sim.startupCapture_separated` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The auxiliary capture tape is disjoint from the width witness's bank.
- `WordRAM.Sim.startup_capture_space` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Silent capture adds only the frame/capture tapes' space, with coefficient one on the width witness's original space.
- `WordRAM.Sim.startupExpandPost` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The catalog expansion writes a zero register on tape zero and exhausts the binary counter on tape one, returning only the counter head.
- `WordRAM.Sim.startup_expand_run` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The existing counter-driven expansion supplies the zero-register writer at every width.
- `WordRAM.Sim.startup_expand_time` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Amortized counter overhead makes the zero-register expansion linear in the width.
- `WordRAM.Sim.startupErase` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Erase only a configuration's finite control tag.
- `WordRAM.Sim.startupErase_eq` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Normalize erasure to physical fields before forming arithmetic-dependent conditionals.
- `WordRAM.Sim.startupAttach` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Attach a phase's tag to unit-tagged physical data.
- `WordRAM.Sim.startupErase_mapState` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Erasing is invariant under a control relabeling.
- `WordRAM.Sim.startupErase_attach` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Re-tagging physical data and then erasing the tag gives the same unit-tagged data.
- `WordRAM.Sim.startupAttach_mapState` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): A final relabeling may be applied to the phase tag before attachment.
- `WordRAM.Sim.StartupStage` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): A startup stage is a finite catalog composition together with its physical specification and time bound. Its heads may move: only the native length stage needs a separate small-space argument; all subsequent stages get their work envelope from their linear time bound.
- `WordRAM.Sim.StartupStage.ofContract` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Reindex a catalog contract and strengthen its physical precondition to make a startup stage. All runtime behavior and envelopes remain the catalog contract's.
- `WordRAM.Sim.StartupStage.ofRow` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Package a bounded row through `Contract.ofReaches` before composing it as a stage.
- `WordRAM.Sim.StartupStage.seq` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Compose stages through the published seam contract, retaining their physical forecasts.
- `WordRAM.Sim.startupErase_select` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Selection and control erasure commute; both keep the same bank and empty source output.
- `WordRAM.Sim.startupEmbed_mapState` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Relabeling an embedded source is relabeling its host, by the shared reconstruction lemma.
- `WordRAM.Sim.StartupStage.embed` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Place a stage in any selected tape bank using `Contract.embed`.
- `WordRAM.Sim.StartupStage.Radius` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): A uniform work radius for the chosen contract time of a startup stage.
- `WordRAM.Sim.StartupStage.radius_time` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Every stage's time bound is also a sufficient work radius.
- `WordRAM.Sim.StartupStage.radius_of_box` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Read a symmetric contract envelope as a stage radius.
- `WordRAM.Sim.StartupStage.radius_embed` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): A selected-bank embedding preserves a source radius, since every other head is fixed.
- `WordRAM.Sim.StartupStage.radius_seq` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Sequential stages add their radii; the dispatch is stationary.
- `WordRAM.Sim.StartupStage.spec` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Strengthen a stage and replace its forecast by an equal one under that precondition.
- `WordRAM.Sim.StartupTemplate` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): A physical configuration template leaves the native input position as its parameter.
- `WordRAM.Sim.StartupRoute` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): A preparation route records its two physical templates and a linear time coefficient.
- `WordRAM.Sim.StartupRoute.ofStage` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Package a catalog stage checked on two explicit physical templates.
- `WordRAM.Sim.StartupRoute.seq` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Join preparation routes with the shared seam, matching their common physical template.
- `WordRAM.Sim.StartupRoute.withTarget` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Normalize a route's final template without changing its machine or time metadata.
- `WordRAM.Sim.startup_wordAt_erase` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The word predicate sees only physical fields, so it is invariant under control erasure.
- `WordRAM.Sim.startupExpand_attach` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The expansion forecast commutes with attaching its specified exit control.
- `WordRAM.Sim.startupExpandStage` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The zero-register expansion as a reusable two-tape startup stage.
- `WordRAM.Sim.startupPatch` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The physical forecast of a word write, with its control tag supplied separately.
- `WordRAM.Sim.startupPatch_attach` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): A framed word write commutes with control erasure and attachment.
- `WordRAM.Sim.startupCopyStage` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Copy any indexed word with the catalog contract, preserving its exact destination frame.
- `WordRAM.Sim.startupRewindPost` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The physical forecast of rewinding one full word from its right delimiter.
- `WordRAM.Sim.startupRewind_attach` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Rewinding's head update commutes with erasing and reattaching the control tag.
- `WordRAM.Sim.startupRewindStage` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The catalog's framed rewind as a startup stage; the empty word is included.
- `WordRAM.Sim.startupClearStage` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Clear an indexed word by the catalog sweep while retaining its interval frame.
- `WordRAM.Sim.startupSkipBackStage` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Return from one cell beyond a word's right delimiter with the catalog backward skip.
- `WordRAM.Sim.startupAdvancePost` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The advancing writer's physical forecast.
- `WordRAM.Sim.startupWriteAdvanceStage` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Use the shared positive-return release for a fixed advancing writer.
- `WordRAM.Sim.startupWalkPost` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The shared walk's physical forecast for a set of work heads.
- `WordRAM.Sim.startupWalkStage` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Walk selected heads across a guide word, including its right blank.
- `WordRAM.Sim.startupErasePreviousPost` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Erase the cell immediately before the current head and restore the head.
- `WordRAM.Sim.startupErasePreviousTM` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): There is no catalog row for erasing the previous cell and returning in place. This fixed two-action leaf moves left, erases, and moves right; the surrounding walks remain catalog rows.
- `WordRAM.Sim.startupErasePrevious_run` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The two fixed actions erase exactly the previous cell and first reach the exit at two.
- `WordRAM.Sim.startupErasePrevious_attach` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The fixed erasure forecast commutes with erasing and reattaching finite control.
- `WordRAM.Sim.startupErasePreviousStage` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The previous-cell erasure as a two-step startup stage.
- `WordRAM.Sim.startupInputPost` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The forecast of a native input-head change with all work data kept.
- `WordRAM.Sim.startupInputPost_attach` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): An input-only change commutes with erasing and reattaching the control tag.
- `WordRAM.Sim.startupAdvanceInputTM` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The shared rewind expects a positive input position. No catalog leaf advances just the native input head once and returns; this leaf supplies that single fixed input action.
- `WordRAM.Sim.startupAdvanceInputStage` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Advance the native input head once, with zero work radius.
- `WordRAM.Sim.startup_advance_positive` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): A clamped right step is always at a positive native input position.
- `WordRAM.Sim.startupInputRewindStage` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Rewind only the native input head, retaining the shared row's zero work radius.
- `WordRAM.Sim.startup_native_position_radius` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The two native positioning stages do not move any work head.
- `WordRAM.Sim.startup_length_stage` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Count the input length in a blank selected bank, preserving the published small radius.
- `WordRAM.Sim.startupWords` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): A bank of finite words with specified heads and empty physical output.
- `WordRAM.Sim.startupWordsTemplate` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Read a word bank as a template indexed by the width and the input.
- `WordRAM.Sim.startupWords_wordAt` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): A word at head zero is delimited in the canonical bank.
- `WordRAM.Sim.startup_buffer_patch` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): A prefix patch replaces that prefix and keeps the old word's suffix.
- `WordRAM.Sim.startup_buffer_append` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Appending a patch at a finite buffer's end appends the word itself.
- `WordRAM.Sim.startupWords_patch` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): A word patch at head zero updates one finite word in the canonical bank.
- `WordRAM.Sim.startupCopyRoute` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Copy between two zero-headed finite words, retaining an arbitrary old destination suffix.
- `WordRAM.Sim.startupRewindRoute` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Rewind a finite word from its right delimiter to head zero.
- `WordRAM.Sim.startupWords_advance` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Appending a fixed word advances exactly one head in the canonical word bank.
- `WordRAM.Sim.startupWriteAdvanceRoute` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Append a fixed prefix with the released catalog writer.
- `WordRAM.Sim.startupPair` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Select two distinct physical tapes, with destination first and counter second.
- `WordRAM.Sim.startupWords_expand` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Expanding into the end of a finite word appends zeroes and exhausts the binary counter.
- `WordRAM.Sim.startupExpandRoute` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Append `W` zeroes through the shared two-tape counter-loop expansion.
- `WordRAM.Sim.startupSeedWords` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The preparation bank initially holds the input length on tape five and the captured width on tape eight; tape nine is a reusable expansion counter.
- `WordRAM.Sim.startupSeedHeads` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The captured width's head starts at its right delimiter.
- `WordRAM.Sim.startupRegisterWords` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The finite word bank after allocating the registers, key and empty table header.
- `WordRAM.Sim.startupRegisterRoute` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Allocate the zero registers, the extended key and the empty table's header.
- `WordRAM.Sim.startup_integer_stage` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The permitted integer row as a startup stage, with its guide width made explicit.
- `WordRAM.Sim.startupEmbed_patch` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Embedding a selected word patch patches the corresponding physical tape.
- `WordRAM.Sim.startupIntegerBank` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The integer row uses the two zero registers as its untouched pair and tapes six/seven as its blank scratch pair; its destination is the key register.
- `WordRAM.Sim.startupKeyWords` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The word bank after installing the signed address of the distinguished initial cell.
- `WordRAM.Sim.startup_integer_route` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Install the constant key by the permitted integer row, preserving the entire other bank.
- `WordRAM.Sim.startupPaddedLength` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Copying the length over a zero register leaves these bits and its unfilled zero suffix.
- `WordRAM.Sim.startup_padded_low` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Erasing cell `W` delimits the low `W` bits of a padded input length, at every width.
- `WordRAM.Sim.startupValueTapes` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The value tape's trailing delimiter is blank; the unused suffix beyond it is framed.
- `WordRAM.Sim.startupValueTemplate` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): All preparation heads return to zero after delimiting the length register.
- `WordRAM.Sim.startupValueRoute` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Form the low-width length word without touching the native input again.
- `WordRAM.Sim.startup_fields_singleton` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): A single field's layout tape is exactly its finite word buffer.
- `WordRAM.Sim.startup_keyLength_empty` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The empty keyed table occupies just its one-cell header.
- `WordRAM.Sim.startup_keyLength_singleton` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The singleton layout includes two markers and two separators after the header.
- `WordRAM.Sim.startup_empty_table` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): A globally buffered header is the empty keyed table, including both sentinels.
- `WordRAM.Sim.startup_keyTable_erase` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Keyed-table assertions depend only on the physical tapes.
- `WordRAM.Sim.startupTablePost` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The physical forecast of laying out the singleton initial memory.
- `WordRAM.Sim.startupTable_attach` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): A table write commutes with erasing and reattaching finite control.
- `WordRAM.Sim.startup_assignment_stage` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The permitted keyed-assignment row, specialized to the initial singleton memory.
- `WordRAM.Sim.startupEmbed_table` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Embedding a table write writes the corresponding host tape at the same origin.
- `WordRAM.Sim.startupAssignmentBank` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Select the table, key, value and two globally blank scratch tapes for keyed assignment.
- `WordRAM.Sim.startupFinishedTemplate` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The final preparation template contains the installed initial-memory singleton.
- `WordRAM.Sim.startup_assignment_route` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Install the singleton memory table through the permitted keyed-assignment row.
- `WordRAM.Sim.startup_table_post_at` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Writing the singleton over a buffered empty header gives its complete keyed-table layout.
- `WordRAM.Sim.startup_finished_encodes` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The finished ten-tape template encodes the initial RAM configuration on its first eight.
- `WordRAM.Sim.startup_preparation_route` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Compose the ordinary preparation after input counting; its route has a uniform linear time coefficient and therefore a linear work radius.
- `WordRAM.Sim.startupPositionStage` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): First advance off the native left boundary, then use the shared input rewind.
- `WordRAM.Sim.startupPosition_next` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The native positioning composition keeps all work data and ends at input position one.
- `WordRAM.Sim.startupPosition_radius` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Native positioning has zero work radius, including its stationary dispatch.
- `WordRAM.Sim.startup_native_stage` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Compose native positioning with the length row in any blank selected bank.
- `WordRAM.Sim.startupTapeCount` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Eight simulation tapes, the witness bank, capture/counter tapes and length scratch bank.
- `WordRAM.Sim.startupOrdinaryBank` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Place the preparation's first eight tapes first, then its width master and counter.
- `WordRAM.Sim.startupLengthBank` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The length row's output is tape five; its private tapes follow capture and counter.
- `WordRAM.Sim.startupOrdinary_capture` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The preparation master is the returning silent embedding's capture tape.
- `WordRAM.Sim.startupLength_zero` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Native counting and ordinary preparation use the same physical length tape.
- `WordRAM.Sim.startupOrdinary_first` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The preparation preserves the required ordering of the eight simulation tapes.
- `WordRAM.Sim.startupOrdinary_fresh` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Every preparation tape lies outside the width witness's selected bank.
- `WordRAM.Sim.startupLength_fresh` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The length bank is outside the witness bank and avoids the capture tape.
- `WordRAM.Sim.startupReady` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The exact physical facts supplied by silent capture, with the finite control erased.
- `WordRAM.Sim.startupReady_ordinary` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The capture frame makes every preparation tape other than the master globally blank.
- `WordRAM.Sim.startup_seed_after_length` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Counting supplies precisely the canonical start expected by ordinary preparation.
- `WordRAM.Sim.startup_encodes_mapState` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): The initial-configuration encoding is invariant under finite-control relabeling.
- `WordRAM.Sim.startup_encodes_embed` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Forwarding the prepared bank into an empty-output frame preserves its RAM encoding.
- `WordRAM.Sim.startup_after_capture` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): All work after silent capture: native counting followed by the prepared RAM bank.
- `WordRAM.Sim.startup_init_mapState` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): Initial blank configurations commute with finite-control relabeling.
- `WordRAM.Sim.startup_space_factor` (TCSlib/Complexity/RAMSimulation/Sim/Startup.lean): A radius proportional to a positive size has a visited-cell bound of the same size.
