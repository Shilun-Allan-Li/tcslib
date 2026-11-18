# fill-ram-phases, round 2 — complete

Both requested targets are proved with their original statements. The instruction phase is
proved modulo exactly the allowed native statements of jobs A, B and C. There is no remaining
`sorry`, `admit` or axiom in the delivered owned file or its new helper files.

## Base, inputs and local history

- Repository: Shilun-Allan-Li/tcslib.
- Exact read-only source base: `7342f98b58704d6c25faf668ed1a64ea0b27c4af` (`ram/readers-2`, PR #375).
- Binding round-2 briefs: COMMON.md (tier 2 addendum included) and fill-ram-phases.md at
  `e40383d88d79e23026c95e20608ee8827d45e59b`, read using git show and included here.
- Local source branch: `codex/fill-ram-phases-r2`, created directly off the base and never
  rebased or pushed. Final local source commit: `1f8f174e43ecdeac15ab18dbee8da5def870ba8a`.
- The round-1 delivery was fetched from exchange/pass-shelat-ch5-8; its ZIP SHA256 was
  `0010aa48f09bbd1253cb93e46fb5771aba057c7ac59ee4f363b737f99f4e8ad3`.
  Its patch was restored to the new base before continuing; the patch in this package is
  against the **new** base, including the restored round-1 proof and table lemmas.
- Original dispatch README and bundle were read, including the bundle's first two sections.
  Their SHA256SUMS checks passed: bundle
  `8ac131f6e08c0b89a52ee0cf6baf09d852e5f92cf565384fba02b556082a79da`, README
  `637446f075c2b2162d766a6c54539aa2c40cc4d8ccd20804fe9cdaa9e26fd16e`.
  The original integrity log and report are in round1/.
- Round-2 checkpoint 1 was delivered to the same exchange inbox at `42dfe0122`, SHA256
  `fbe85603c6794b67f6b4ad4538dccd7b2bf01037e3dec71a4db171b6d1a39a0c`.
  It was a progress checkpoint; this package supersedes its remaining instruction frontier.

## Targets and construction

| Target | Status | Reachable admitted declarations |
|---|---|---|
| `WordRAM.Sim.exists_phase` | **Proved**, statement byte-identical | only the A/B/C statements listed below |
| `WordRAM.Sim.exists_verdictPhase` | **Proved**, statement byte-identical | none |

The phase proof splits by instruction and chooses a finite PhaseMachine certificate. Immediate
addresses are converted to keys on register one. Keyed lookups load the two operand registers,
arithmetic or input access writes the result register, and one final assignment updates the
memory table. Indirect stores fetch their value before constructing the computed key. Range,
key injectivity, default-zero lookup, assignment and physical-table lemmas preserve TableOf
and Encodes, including width zero and absent zero cells. The table length is exactly
`1 + entries.length * (keyWidth + valueWidth + 4)`, so its charge fits the footprint allowance.

PhaseFrame separates control from tapes and heads. Native contracts are placed through
embedEmitTM and phase_reaches_embed. PhaseRow and PhaseBlock sequence them using
Contract.ofReaches and Contract.seq; restored heads retain a common radius center. Common
phaseTime/phaseSpace units dominate table scans, linear word rows, quadratic multiplication,
input length time and binary input length radius. Dispatches are absorbed into constants.

The signed branch uses the native sign test and two live exits. Emit uses the native nonzero
test and one optional-output leaf, with empty physical output in verdict mode. Coin uses one
stationary entry choice that remembers the bit in finite control. NDTM.phaseHostND runs the
selected deterministic continuation and joins both branches at next. Its fixed slices are
phaseHostTM; Contract.inPhase and the published host prefix theorem give the runs, cuts and
bounds. Tagging transfers no-entry and choice agreement. No transition returns to the choice
entry. Finally PhasePost supplies the exact xstep for the matching program and compatible
coin stream; installing next/jump control preserves the encoding.

The verdict proof retains its one-step optional emission and halt, with unchanged work heads.
All proof bodies over 20 lines have human-readable proof sketches; the proof-sketch audit passes.

## Authorized source scope

There are 25 new helper files under TCSlib/Complexity/RAMSimulation/Sim/, all public declarations
in the internal namespace WordRAM.Sim:

| File stem | Role |
|---|---|
| `PhaseTable` | eight key/table lookup, width, count and assignment invariants retained from round 1 |
| `PhaseLayout` | signed address ranges, exact table layout length, footprint bound and table-write preservation |
| `PhaseCore` | state-independent frames, finite rows and Contract.seq-based seam runs |
| `PhaseTape` | layout congruence, native embedding, one-tape update factoring and exact write endpoints |
| `PhaseInvariant` | encoding preservation by register writes, assignment and footprint enlargement |
| `PhaseRows` | placed native constant, binary arithmetic, half and sign-extension rows |
| `PhaseRegister` | encoded readiness, scratch, preserved operands and frame invariants |
| `PhaseMemory` | semantic data, selected represented table, native lookup/assignment rows and costs |
| `PhaseInput` | native input-bit placement and its chosen input-head endpoint |
| `PhaseBounds` | common time/radius units and domination of every native allowance |
| `PhaseBlock` | finite blocks with semantic pre/postconditions and tracked register contents |
| `PhaseAtoms` | shared normalized register writers and keyed-memory blocks |
| `PhaseCompute` | normalized arithmetic, unary, computed-key and input blocks |
| `PhaseSchedules` | shared immediate fetch/store, constant and binary arithmetic schedules |
| `PhaseOperations` | factored unary schedule, half/input and indirect load/store schedules |
| `PhaseControl` | fresh entry, unused exits, deterministic embedding, zero prefix and phase package |
| `PhaseSemantics` | program/coin-parametric PhasePost and memory-write semantic conversion |
| `PhaseMemoryMachines` | full one/add/sub/mul/load/store/half/input phase certificates |
| `PhaseTests` | native sign/nonzero adapter, unchanged-frame endpoints and two-exit blocks |
| `PhaseBranching` | ordinary-prefix and fresh-entry wrappers for two-exit tests |
| `PhaseBranchMachines` | shared fetched-operand test and complete signed-branch phase |
| `PhaseHost` | Contract.inPhase placement, other-phase cuts and same-host run concatenation |
| `PhaseFork` | registered ND phase host with two deterministic continuations and shared return |
| `PhaseCoin` | one-choice stationary source, fixed constant continuations and exact coin semantics |
| `PhaseEmit` | optional live-return emission, mode-sensitive encoding and complete output phase |

The owned Phases.lean imports the helpers and proves both targets. The RAMSimulation facade
changes **only** imports and Contents entries. Every child is wired into both the owned
import closure and the facade. All files are below the repository's 600-line target.

The exact public declaration inventory, including generated nonsimp field readers, constructors,
projections, recursors and finite instances, is in `evidence-r2/logs/final-declarations.tsv`.
`final-declaration-roots.txt` also lists the three home readers. Every inventoried root has an
axiom print and direct-admission walk. Frame.ofCfg/cfg/write/assign/emit publish both their
full equation and the policy's generated field equations, with isSimp=false.

Only three explicit private declarations are added: PhaseTable's phase_keyAssign_mem
(assignment membership) and phase_keyAssign_nodup (distinct keys), and PhaseTape's
phase_single_tape_update (shared conditional-patch normalization for word and table writes).
There are no new simp attributes, admissions or axioms, and no existing statement/visibility
is changed. The existing six control declarations in Phases are byte-identical.

Three pure missing readers are added beside their definitions, as the revised COMMON.md permits:

| Home file | Reader | Exact restatement / proof |
|---|---|---|
| Build/Embed.lean | `Turing.Cfg.select_eq` | selected configuration's record body; rfl |
| Build/Seam.lean | `Turing.seamCompTM_tr_inl` | left dispatch/action conditional; rfl |
| Build/NDHost.lean | `Turing.NDTM.phaseHostND_tr` | redirect/source-action match; rfl |

The static audit removes each inserted reader and compares its home file byte-for-byte with
the base: there are **no other home-file changes**. The reader insertion and target statement
freeze receipts are in final-static-audit.json. The earlier missing range/table readers are
consumed from PR #375; no further API changes were needed.

## Reuse and definition boundaries

The construction registry and actual import closure were searched before each helper cluster:
range/key/layout, lookup/assignment, selection/framing, seam/host composition, native word and
input rows, sign/nonzero tests, output leaves and fresh-entry control. Existing facts are cited,
not replaced: bvBits_length/injective, toInt_wd, core signed-word bounds/sign extension, list
find/membership/distinctness/cardinality lemmas, layout equations, embedding lockstep/frame
lemmas, Contract.ofReaches/seq/inPhase and phaseHostTM_run_le.

The word-writing, unary, memory precondition/cost, register-invariant, immediate fetch/store,
unary schedule, zero prefix, fresh seam and registered-host framing proofs are factored and
shared by their variants. The host implementations remain the existing seam and phase hosts;
PhaseFork instantiates their control tags and redirects rather than implementing a new host.
The supplied leaf actions cover the documented catalog gaps: one entry choice with live returns,
stationary optional output with a live return, and optional verdict emission/halt. The Boolean
padding leaf performs no native computation; the existing seam supplies its dispatch.

| Other-file TCSlib definition | Published reader/contract used |
|---|---|
| InRange; keyBits; TableOf; Encodes; ImmBound; immediates | inRange_iff, keyBits_def, tableOf_iff, encodes_iff, immBound_iff, immediates_def |
| xstep; effect; inBitWord; coinWord; touches/baseTouches | xstep_def, effect_def, inBitWord_def, coinWord_def, XInstr.touches_def, baseTouches_def |
| bvBits and word/scratch layouts | bvBits_def/length/injective, wordAt_iff, wordWrite_apply, scratchBlank_iff |
| keyed/table layouts and operations | keyFields_def, keyTableLength_def, keyTableAt_iff, keyLookup_def, keyAssign_def, keyTableWrite_apply, tableFields_eq, tableAt_iff, joinFields_length, fieldsTape_of_neg/of_length_le, bufferTape_left/nat |
| Cfg.select; Cfg.mapState; Cfg.bindState | select_eq; mapState field equations and mapState_eq_of_fields; bindState field equations |
| embedEmitTM; embedEmitCfg | embedEmitTM_runFrom; embedEmitCfg_eq/select/state/selected_pos/unselected |
| machine run/step and action application | runFrom_zero/one/add/succ_eq_step', step_of_some/of_halt, Action.apply field equations, moveInputPos_zero |
| FinTM.controlAction | controlAction_def and controlAction_apply |
| seamCompTM | new tr_inl, existing tr_inr; Contract.seq and phase_reaches_seq |
| Contract.ofReaches, Contract.seq, Contract.inPhase | published pre/time/post/lo/hi equations, ofReaches_time_le and primitive contract run/cut/env fields |
| phaseHostTM; NDTM.phaseHostND | phaseHostTM_run_le; new phaseHostND_tr and existing phaseHostND_fixChoice |
| NDTM.fixChoice; MultiTapeTM.toNDTM | published q0/tr field equations; phase_toNDTM_fixChoice proved from those fields and record eta |
| Cross-file frame/register/block helpers | full equations and generated field readers; phaseReady_iff, phaseScratch_iff, phaseState_iff, phasePost_iff, bank apply equations, PhaseArith.value_eq/steps_eq, PhaseTestKind.bit_eq and proved contracts |

Core/Mathlib definitions reduce only through permitted kernel reduction; explicit simp/rw lists
contain equations and theorems, not those definitions. WordRAM.wd is a reducible abbreviation.
All ordinary public foreign TCSlib definitions in each actual closure are sealed below;
abbreviations, projections, private and internal-detail constants are excluded by the standard
inventory. The seals caught an input helper's Frame.write reduction and host contract closures reading
Frame.cfg/Contract.ofReaches directly. They were replaced by the published equation readers;
both affected native/downstream replays and all final seals pass.

## Axioms and admitted frontier

The final probe prints axioms and walks **every reachable type and value**, including theorem
bodies, for all 380 inventoried roots. It reports each reachable constant whose own
value directly uses sorryAx. The exact lists are in final-admissions.json and final-axioms.log.
The only directly admitted declarations reachable from exists_phase are:

- `Turing.bvBits_injective`
- `Turing.exists_inputBitTM`
- `Turing.exists_keyAssignTM`
- `Turing.exists_keyLookupTM`
- `Turing.exists_wordAddTM`
- `Turing.exists_wordHalfTM`
- `Turing.exists_wordIntTM`
- `Turing.exists_wordMulTM`
- `Turing.exists_wordNonzeroTM`
- `Turing.exists_wordSignExtendTM`
- `Turing.exists_wordSignTM`
- `Turing.exists_wordSubTM`

All belong to the three allowed files Build/WordArith, Build/KeyTable and Build/InputBit.
No admitted RecordTable declaration or other admission is reached. The probe asserts that
frontier for every root, and that axiom prints contain at most propext, Classical.choice,
Quot.sound and sorryAx. The verdict target has no reachable admission. The owned proofs
introduce no sorry; their sorryAx dependency is solely the authorized modular native-row frontier.

## Verification receipts

Every Lean check runs through the repository's leanelab-o.sh, nice -n10, lean -j4, in a private
fresh-output tree. The driver deletes the target olean before a run, requires a nonempty result,
and rejects nonzero exit or error diagnostics. No lake build is used.

- Round-2 base bootstrap: 47 fresh TCSlib modules, plus pinned Mathlib cache probe, all exit 0.
  The select reader was followed by 35 dependent replays; the seam reader by 34. NDHost's pure
  reader was checked in its home module. All source records are in the included logs.
- Complete exists_phase first passes in phases-complete-02.log, with **no errors or warnings**.
- Final generated-field-reader replay: final-native-00..26, **all 27 exit 0**, including
  Phases, Simulation, Classes and RAMSimulation. After the input seal repair,
  final-input-repair-00..20 replays **all 21 affected modules, exit 0**, including those consumers.
  The host seal repair is followed by final-host-repair-00..07, **all 8 exit 0**.
- The facade's final import closure contains 102 TCSlib modules. Its full topological
  source replay order is final-replay-order.txt; every corresponding private-tree olean is
  nonempty. Earlier unaffected prerequisites retain their successful fresh-tree checks.
  The campaign's standing rule excludes the root TCSlib facade; no full-root build is claimed.
- All **26 sealed module copies** pass with zero errors. The inventory counts and
  removed simp attributes are shown below; every final log has exit 0.
- final-axioms.log: all axiom prints and full direct-admission walks pass; the allowed-set
  assertions pass. final-declarations.log inventories the complete public surface.
- final-static-audit.json and final-proof-sketch-audit.json: statement freeze, three pure-reader
  home changes only, no new admissions/simp, namespace/header/sketch and facade scope pass.
- git diff --check passes for every delivered path. The package's patch applies cleanly to an
  export of the exact new base, and all delivered source bytes match the patched export and
  final local commit. See final-package-validation.json. ZIP CRC and SHA256SUMS are validated.

| Module seal | Foreign definitions | Simp attributes removed | Exit |
|---|---:|---:|---:|
| `PhaseTable` | 330 | 3 | 0 |
| `PhaseLayout` | 330 | 3 | 0 |
| `PhaseCore` | 330 | 3 | 0 |
| `PhaseTape` | 332 | 3 | 0 |
| `PhaseInvariant` | 332 | 3 | 0 |
| `PhaseRows` | 332 | 3 | 0 |
| `PhaseRegister` | 339 | 3 | 0 |
| `PhaseMemory` | 339 | 3 | 0 |
| `PhaseInput` | 343 | 3 | 0 |
| `PhaseBounds` | 344 | 3 | 0 |
| `PhaseBlock` | 346 | 3 | 0 |
| `PhaseAtoms` | 347 | 3 | 0 |
| `PhaseCompute` | 347 | 3 | 0 |
| `PhaseSchedules` | 347 | 3 | 0 |
| `PhaseOperations` | 347 | 3 | 0 |
| `PhaseControl` | 355 | 4 | 0 |
| `PhaseSemantics` | 355 | 4 | 0 |
| `PhaseMemoryMachines` | 356 | 4 | 0 |
| `PhaseTests` | 355 | 4 | 0 |
| `PhaseBranching` | 356 | 4 | 0 |
| `PhaseBranchMachines` | 357 | 4 | 0 |
| `PhaseHost` | 357 | 4 | 0 |
| `PhaseFork` | 381 | 4 | 0 |
| `PhaseCoin` | 384 | 4 | 0 |
| `PhaseEmit` | 384 | 4 | 0 |
| `Phases` | 385 | 4 | 0 |

Development logs, including failed iterations, are included. Reused final labels contain their
latest run; final-* logs and final-seals.json identify the successful final receipts. The initial
input/host seal failures and their reader repairs are described above. Scratch probes are
shipped as .lean.txt, not library sources; rename those copies to .lean to replay them.
The audit scripts and exact environment/check wrappers are included.

## Environment, waits and delivery discipline

Native macOS arm64, 12 logical CPUs, 18 GiB RAM. Native sysctl/vm_stat/df replace Linux /proc
and cgroup interfaces. The v2.6 preflight recorded APFS free **118,478,614,528 bytes** and
conservative free+inactive+speculative memory **5,663,850,496 bytes**, above the required floors.
All scratch outputs and temporary patch exports use APFS, not a memory-backed filesystem.

The existing pinned package-tree link points to
/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-arora-barak-ch3-4/.lake/packages.
Manifest URLs/revisions were checked, 39 Mathlib roots were available at bootstrap, and no
package cache fetch, dependency copy, executable shim or cross-tree TCSlib olean reuse occurred.
Round-1 TCSlib oleans were not used. This round's tree is .lake/fill-ram-phases-r2-oleans.

The checker holds an exclusive per-fill lock and runs one owned Lean at a time. It checks the
machine-wide count before every launch, waits at three or more and uses TCSLIB_LEAN_SLOTS=3.
There are 22 logged wait polls (110 seconds nominal), with maximum observed
machine count 3. All waits and launch counts are preserved. During development, a coin-entry check found its fork prerequisite olean absent after a
failed iteration. It exited immediately and was superseded by a serial dependency-order
check. No second owned Lean process was started in parallel in round 2. Round 1's brief
historical bootstrap overlap remains disclosed in its separately included report.

Thirty unrelated blueprint modifications were preserved and excluded from the source commit
and patch. The source branch is never pushed, and no PR is opened. Only the designated ZIPs
are delivered on exchange/pass-shelat-ch5-8. The shared exchange checkout could not pull over
another fill's untracked startup ZIP, so an isolated managed delivery checkout was used,
preserving the other fill's file. It is synchronized with pull --rebase before each delivery,
and no force push is used. Checkpoint and final delivery receipts record their archive hashes.

## Source diff against the new base

```text
 TCSlib/Complexity/RAMSimulation.lean               |  50 ++++
 .../Complexity/RAMSimulation/Sim/PhaseAtoms.lean   | 190 +++++++++++++
 .../Complexity/RAMSimulation/Sim/PhaseBlock.lean   | 172 ++++++++++++
 .../Complexity/RAMSimulation/Sim/PhaseBounds.lean  |  89 ++++++
 .../RAMSimulation/Sim/PhaseBranchMachines.lean     | 100 +++++++
 .../RAMSimulation/Sim/PhaseBranching.lean          | 121 ++++++++
 TCSlib/Complexity/RAMSimulation/Sim/PhaseCoin.lean | 147 ++++++++++
 .../Complexity/RAMSimulation/Sim/PhaseCompute.lean | 160 +++++++++++
 .../Complexity/RAMSimulation/Sim/PhaseControl.lean | 214 ++++++++++++++
 TCSlib/Complexity/RAMSimulation/Sim/PhaseCore.lean | 196 +++++++++++++
 TCSlib/Complexity/RAMSimulation/Sim/PhaseEmit.lean | 174 ++++++++++++
 TCSlib/Complexity/RAMSimulation/Sim/PhaseFork.lean | 229 +++++++++++++++
 TCSlib/Complexity/RAMSimulation/Sim/PhaseHost.lean | 157 +++++++++++
 .../Complexity/RAMSimulation/Sim/PhaseInput.lean   | 109 +++++++
 .../RAMSimulation/Sim/PhaseInvariant.lean          | 135 +++++++++
 .../Complexity/RAMSimulation/Sim/PhaseLayout.lean  | 158 +++++++++++
 .../Complexity/RAMSimulation/Sim/PhaseMemory.lean  | 251 +++++++++++++++++
 .../RAMSimulation/Sim/PhaseMemoryMachines.lean     | 151 ++++++++++
 .../RAMSimulation/Sim/PhaseOperations.lean         | 152 ++++++++++
 .../RAMSimulation/Sim/PhaseRegister.lean           | 104 +++++++
 TCSlib/Complexity/RAMSimulation/Sim/PhaseRows.lean | 312 +++++++++++++++++++++
 .../RAMSimulation/Sim/PhaseSchedules.lean          | 116 ++++++++
 .../RAMSimulation/Sim/PhaseSemantics.lean          | 119 ++++++++
 .../Complexity/RAMSimulation/Sim/PhaseTable.lean   | 246 ++++++++++++++++
 TCSlib/Complexity/RAMSimulation/Sim/PhaseTape.lean | 234 ++++++++++++++++
 .../Complexity/RAMSimulation/Sim/PhaseTests.lean   | 133 +++++++++
 TCSlib/Complexity/RAMSimulation/Sim/Phases.lean    | 164 +++++++++--
 TCSlib/Complexity/TuringMachine/Build/Embed.lean   |   7 +
 TCSlib/Complexity/TuringMachine/Build/NDHost.lean  |  10 +
 TCSlib/Complexity/TuringMachine/Build/Seam.lean    |  12 +
 30 files changed, 4391 insertions(+), 21 deletions(-)
```
