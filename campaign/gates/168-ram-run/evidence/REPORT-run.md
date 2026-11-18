# fill-ram-run, round 2

Both frozen targets are proved modulo the three permitted tier-2 interfaces. There is no
remaining target frontier, no new admission and no statement change.

## Provenance and scope

- Repository: `Shilun-Allan-Li/tcslib`.
- Base: `7342f98b58704d6c25faf668ed1a64ea0b27c4af` (`ram/readers-2`, PR #375).
- Local source branch: `codex/fill-ram-run-r2`, created directly at that base and never rebased.
- Brief records: `e40383d88d79e23026c95e20608ee8827d45e59b`, read with `git show` from
  `complexity/ram-simulation`; the exact common rules and brief are under `evidence-r2/inputs/`.
- Fetched the base and exchange read-only. Extracted and applied the round-1 documentation patch
  from the exchange ZIP, SHA-256 `57cd9fc6f1f228f64c8db9c5d3456cba567cd7dfdcaf205c302b040f0ed42600`.
- Original outbox README and bundle were read in round 1. The bundle checksum is
  `ef30f5b89e0ae78a44b28e888a4a5a7f68f9e3fef18c1ca73fda78576ade7e32`;
  `SHA256SUMS` and segment verification passed. Round 2 rechecked the bundle checksum.
- `fill-ram-run-r2.patch` is against the new base, not the round-1 base. It changes exactly
  22 authorized Lean files: Simulation, the facade's imports/contents, 17 new internal Run*
  files, and three homes containing four permitted pure readers.
- Every existing declaration statement in those files is byte-identical. Existing declaration
  bodies are unchanged except the two target bodies. Simulation's module description and
  target proof sketches describe the completed proof. There are no private helper additions.
- Unrelated APFS case-collision blueprint differences were present on checkout. They were not
  edited, staged, included in the patch, or delivered.

## Targets and admission frontier

| Target | Result |
|---|---|
| `WordRAM.exists_simulation` | Proved modulo the permitted interfaces; native and sealed replay pass. |
| `WordRAM.exists_ndSimulation` | Proved modulo the permitted interfaces; native and sealed replay pass. |

Both axiom prints are exactly `[propext, sorryAx, Classical.choice, Quot.sound]`.
A full walk of types and values records these direct admission sites for **each** target:

- `WordRAM.Sim.exists_phase`
- `WordRAM.Sim.exists_startup`
- `WordRAM.Sim.exists_verdictPhase`

The same exact three-site list occurs for all nine `RAMSimulation/Classes` corollaries.
Nothing admitted in `Build/RecordTable` is reached. See `evidence-r2/logs/admission-frontier.json`,
`downstream-axioms.log`, and the scratch probes under `evidence-r2/probes/`.

## Proof and reuse

The machine is the published `NDTM.phaseHostND`, with startup and position/parity phases.
`runEmbedND` is exactly the requested construction: under bit b its transition is the
transition of `embedEmitTM` applied to the source phase's `fixChoice b`. No manual instruction
transition table or replacement startup/search machine is introduced. `phaseHostND_run`,
`phaseHostND_fixChoice`, the deterministic host transition equation and the published forwarding
embedding run/frame equations provide the host transitions and dispatch.

The single `run_execution` fuel induction tracks exact source touches, consumed coins,
source traces valid for every agreeing stream, actual branch words, and a common time/head
bound. It handles zero-duration phase rows and empty choice prefixes. Continuing phases
restore all heads, so the radius does not accumulate over source steps. A source halting
witness bounds the exact prefix and its footprint; `HaltsWithin.unique` identifies the
completed verdict and emitted output. There is no copy of completed-run uniqueness.

`input_run` adds startup once. The visited set is the union of startup's visited cells and one
bounded interval per host tape, retaining coefficient one on the word-size witness's SW cost.
The sufficient constant is
`C0 + 3*C1 + (8+extraTapes)*(6*C1+1) + 3`, where C0 is the startup coefficient and C1 the finite
maximum phase coefficient. `time_total_le` and `space_total_le` give the frozen polynomials.
The deterministic target uses a constant false timed schedule. Arbitrary ND branches use
their defaulted-read timed schedule; prescribed streams use `RunDriver.ofCoins`. Both modes
reuse the same instruction and execution induction. Existing halt/padding lemmas handle
exact final branch lengths and post-halt space.

Before adding helpers, the import closure was searched for encoding transports, deterministic
slice/host transfers, source-run uniqueness, visited-set concatenation, range bounds and binary
length bounds. Existing `runWith_eq_fixChoice_runFrom`, forwarding embedding and ND host lemmas,
`HaltsWithin.unique`, and `length_bits_le_log` were reused. The general range lemma in
`NARMCompile` requires bounds for all words of a length, while the invariant here bounds the
actual driven prefixes and must preserve startup space additively; `runSpace_append_le`
therefore proves the necessary visited-set union statement. The new exact source trace is
prefix/footprint bookkeeping, rather than a second source interpreter. The new schedule words
are finite list slices, not another TM runner. Each module's role and declarations are listed
below. No external project code or new proof architecture was consulted during round 2.

## Added pure readers

These are the only added declarations outside `WordRAM.Sim`. Each is beside its definition,
restates it exactly, has a reading docstring, and is proved by `rfl` or `Iff.rfl` as authorized
by the tier-2 missing-readers addendum.

| File | Reader | Proof |
|---|---|---|
| `TuringMachine/Build/Embed.lean` | `Turing.embedEmitTM_q₀` | `rfl` |
| `TuringMachine/NondeterministicSpace.lean` | `Turing.NDTM.visitedWith_eq` | `rfl` |
| `TuringMachine/NondeterministicSpace.lean` | `Turing.NDTM.spaceUsedWith_eq` | `rfl` |
| `RAMSimulation/WordSize.lean` | `WordRAM.wordSizeComputable_iff` | `Iff.rfl` |

The four home-file reader seals pass. `tableAt_iff`, already published at the new base, resolves
the round-1 blocker; no RecordTable proof was used or changed.

## Verification

All Lean checks use `scripts/lean_check_tree.sh` through the logged slot wrapper. No `lake build`,
whole-library build, package update or cache download was run.

| Check | Result / log |
|---|---|
| Own clean base bootstrap | 77 modules, exit 0; `bootstrap.log`, `bootstrap-order.txt` |
| Final native ordered replay | 24 checks, every exit 0; `final-checks.json` |
| Simulation target warnings | No sorry warnings or errors for either target |
| Downstream | `Classes` and RAMSimulation facade, exit 0 |
| Axiom prints and full admission walks | Both targets and all nine class corollaries, exit 0 |
| Compiled definition metadata | 209 theorem constants; `metadata-final.log`, `metadata.json` |
| Complete-source opacity replay | 18 owners / 205 compiled proofs, exit 0; `seals/RESULT.json` |
| Pure-reader opacity replay | Four home-file readers, exit 0; `reader-seal-Reader*.log` |
| Seal controls | 76 heads / 152 paired identities: native exit 0; sealed halves each expected exit 1 |
| Source freeze | Every existing statement byte-identical; `full-source-freeze.json` |
| Explicit foreign-definition syntax sweep | No foreign definitions in simp/rw/dsimp lists; `foreign-syntax-sweep.json` |
| Style | Zero findings in all 17 new modules and Simulation; `style-final.log` |
| Whitespace | `git diff --cached --check`, exit 0 |
| Patch round-trip | Reapplied to a base export and all 22 source files compared byte-for-byte; `patch-roundtrip.json` |
| ZIP verification | CRC and every payload SHA-256 verified; `package-verification.json` |

The top-level `TCSlib.lean` aggregate was not replayed: it imports unrelated areas outside the
77-module campaign snapshot. The explicitly requested Classes and RAMSimulation facade were
replayed. No unrelated import closure was built.

The first target seal caught a dependent projection through the finite-host bundle. The
specialization now uses an explicit local finite bundle of the same host, and the full final
seal passes. An initial all-head rejection-control run hit Lean's 100-diagnostic limit; the
final controls run in two 38-head halves and every expected rejection is accounted for.
Historical failing development logs are retained and distinguished from final checks.

## Environment and Lean slots

Native Darwin/arm64, pinned Lean 4.25.0. The existing package-cache symlink was reused read-only;
all present package URLs and revisions match the manifest. Four documentation-only packages
are absent and unneeded. Preflight recorded 12 logical CPUs, 18 GiB physical memory,
4,492,967,936 bytes conservative headroom and 119,521,304,576 bytes disk free. These native
checks substitute sysctl/vm_stat/df for Linux-only environment commands. See `preflight.log`
and `manifest.log`.

Own oleans are in `.lake/fill-ram-run-r2-oleans`; no shared olean tree was modified. Every launch
acquires one of the first three shared Lean slots, checks the machine-wide count, and records
waits in `lean-slots.log`. One early axiom-probe launch overlapped the still-running metadata
probe for about three seconds, contrary to the one-own-process rule; the shared three-process
limit was still observed. The checker was then strengthened with an exclusive per-worktree
fcntl lock, and all later checks were serialized. No crash or out-of-memory failure occurred.

## New internal files and all public declarations

All paths in this section are under `TCSlib/Complexity/RAMSimulation/Sim/`, and all names are in
`WordRAM.Sim`. The listing includes generated public readers, constructors, projections and
recursors (247 public constants in total); source declarations are also separately listed in
`declaration-inventory.json`. Technical generated constants inherit the role of their source
structure or definition. Full per-proof foreign boundaries are in `metadata.json`.

### RunEncoding.lean

Encoding congruence, state renaming, output-preserving tape-bank selection and forwarding embedding.

- `WordRAM.Sim.encodes_congr`
- `WordRAM.Sim.encodes_embed`
- `WordRAM.Sim.encodes_mapState`
- `WordRAM.Sim.runBank`
- `WordRAM.Sim.runBank_embed`
- `WordRAM.Sim.runBank_encodes`
- `WordRAM.Sim.runBank_inputPos`
- `WordRAM.Sim.runBank_output`
- `WordRAM.Sim.runBank_reconstruct`
- `WordRAM.Sim.runBank_state`
- `WordRAM.Sim.runBank_workTapePos`
- `WordRAM.Sim.runBank_workTapes`
- `WordRAM.Sim.runEntry_reconstruct`

### RunSlices.lean

Choice-slice transfer, unrepeated entry, constant words and the prescribed forwarding ND tape embedding.

- `WordRAM.Sim.runDet_fixChoice`
- `WordRAM.Sim.runEmbedND`
- `WordRAM.Sim.runEmbedND_fixChoice`
- `WordRAM.Sim.runEmbedND_q₀`
- `WordRAM.Sim.runEmbedND_runWith`
- `WordRAM.Sim.runEmbedND_tr`
- `WordRAM.Sim.runSlice_avoids_entry`
- `WordRAM.Sim.runWith_entry_slice`
- `WordRAM.Sim.runWith_replicate`

### RunPhase.lean

One uniform package for ordinary and verdict phase interfaces, and arbitrary branch-prefix transfer.

- `WordRAM.Sim.RunPhase`
- `WordRAM.Sim.RunPhase.State`
- `WordRAM.Sim.RunPhase.agrees`
- `WordRAM.Sim.RunPhase.avoids_entry`
- `WordRAM.Sim.RunPhase.branch_prefix`
- `WordRAM.Sim.RunPhase.branch_prefix_choice`
- `WordRAM.Sim.RunPhase.branch_slice`
- `WordRAM.Sim.RunPhase.casesOn`
- `WordRAM.Sim.RunPhase.correct`
- `WordRAM.Sim.RunPhase.cost`
- `WordRAM.Sim.RunPhase.ctorIdx`
- `WordRAM.Sim.RunPhase.decidableState`
- `WordRAM.Sim.RunPhase.entry`
- `WordRAM.Sim.RunPhase.finiteState`
- `WordRAM.Sim.RunPhase.machine`
- `WordRAM.Sim.RunPhase.mk`
- `WordRAM.Sim.RunPhase.mk.inj`
- `WordRAM.Sim.RunPhase.mk.injEq`
- `WordRAM.Sim.RunPhase.mk.noConfusion`
- `WordRAM.Sim.RunPhase.mk.sizeOf_spec`
- `WordRAM.Sim.RunPhase.noConfusion`
- `WordRAM.Sim.RunPhase.noConfusionType`
- `WordRAM.Sim.RunPhase.rec`
- `WordRAM.Sim.RunPhase.recOn`
- `WordRAM.Sim.RunPhase.redirect`
- `WordRAM.Sim.exists_runPhase`
- `WordRAM.Sim.runPhase_of_instruction`
- `WordRAM.Sim.runPhase_of_verdict`
- `WordRAM.Sim.runVerdict_cases`

### RunHost.lean

Finite immediate bound, chosen startup/phases, clamped position/parity host and fixed-slice reader.

- `WordRAM.Sim.RunSetup`
- `WordRAM.Sim.RunSetup.Index`
- `WordRAM.Sim.RunSetup.PhaseState`
- `WordRAM.Sim.RunSetup.StartState`
- `WordRAM.Sim.RunSetup.State`
- `WordRAM.Sim.RunSetup.bounded`
- `WordRAM.Sim.RunSetup.casesOn`
- `WordRAM.Sim.RunSetup.ctorIdx`
- `WordRAM.Sim.RunSetup.decidableStart`
- `WordRAM.Sim.RunSetup.extraTapes`
- `WordRAM.Sim.RunSetup.finHost`
- `WordRAM.Sim.RunSetup.finHost_State`
- `WordRAM.Sim.RunSetup.finHost_k`
- `WordRAM.Sim.RunSetup.finHost_tm`
- `WordRAM.Sim.RunSetup.finiteStart`
- `WordRAM.Sim.RunSetup.host`
- `WordRAM.Sim.RunSetup.host_fixChoice`
- `WordRAM.Sim.RunSetup.host_q₀`
- `WordRAM.Sim.RunSetup.host_runWith`
- `WordRAM.Sim.RunSetup.index_eq`
- `WordRAM.Sim.RunSetup.mk`
- `WordRAM.Sim.RunSetup.mk.inj`
- `WordRAM.Sim.RunSetup.mk.injEq`
- `WordRAM.Sim.RunSetup.mk.noConfusion`
- `WordRAM.Sim.RunSetup.mk.sizeOf_spec`
- `WordRAM.Sim.RunSetup.noConfusion`
- `WordRAM.Sim.RunSetup.noConfusionType`
- `WordRAM.Sim.RunSetup.phase`
- `WordRAM.Sim.RunSetup.phaseDecidableEq`
- `WordRAM.Sim.RunSetup.phaseFintype`
- `WordRAM.Sim.RunSetup.phaseState_none`
- `WordRAM.Sim.RunSetup.phaseState_some`
- `WordRAM.Sim.RunSetup.phase_none`
- `WordRAM.Sim.RunSetup.phase_some`
- `WordRAM.Sim.RunSetup.phases`
- `WordRAM.Sim.RunSetup.rec`
- `WordRAM.Sim.RunSetup.recOn`
- `WordRAM.Sim.RunSetup.redirect`
- `WordRAM.Sim.RunSetup.redirect_none`
- `WordRAM.Sim.RunSetup.redirect_some`
- `WordRAM.Sim.RunSetup.resumeTag`
- `WordRAM.Sim.RunSetup.resumeTag_eq`
- `WordRAM.Sim.RunSetup.startCost`
- `WordRAM.Sim.RunSetup.startEntry`
- `WordRAM.Sim.RunSetup.startExit`
- `WordRAM.Sim.RunSetup.start_correct`
- `WordRAM.Sim.RunSetup.startup`
- `WordRAM.Sim.RunSetup.state_eq`
- `WordRAM.Sim.RunSetup.width`
- `WordRAM.Sim.RunSetup.width_pos`
- `WordRAM.Sim.exists_runSetup`
- `WordRAM.Sim.runPosition`
- `WordRAM.Sim.runPosition_fetch`
- `WordRAM.Sim.runPosition_val`
- `WordRAM.Sim.runProgram_immBound`

### RunSource.lean

Exact touched-cell source traces, prefix/halting comparison and consumed read-once coin bookkeeping.

- `WordRAM.Sim.RunCoinsAgree`
- `WordRAM.Sim.RunCoinsSatisfy`
- `WordRAM.Sim.RunSourceTrace`
- `WordRAM.Sim.RunSourceTrace.below`
- `WordRAM.Sim.RunSourceTrace.below.casesOn`
- `WordRAM.Sim.RunSourceTrace.below.cons`
- `WordRAM.Sim.RunSourceTrace.below.nil`
- `WordRAM.Sim.RunSourceTrace.below.rec`
- `WordRAM.Sim.RunSourceTrace.bounded_by_halt`
- `WordRAM.Sim.RunSourceTrace.brecOn`
- `WordRAM.Sim.RunSourceTrace.casesOn`
- `WordRAM.Sim.RunSourceTrace.cons`
- `WordRAM.Sim.RunSourceTrace.nil`
- `WordRAM.Sim.RunSourceTrace.rec`
- `WordRAM.Sim.RunSourceTrace.recOn`
- `WordRAM.Sim.RunSourceTrace.to_stepsIn`
- `WordRAM.Sim.runCoinsAgree_append_bit`
- `WordRAM.Sim.runCoinsAgree_append_left`
- `WordRAM.Sim.runCoinsAgree_iff`
- `WordRAM.Sim.runCoinsAgree_refl`
- `WordRAM.Sim.runCoinsSatisfy_append`
- `WordRAM.Sim.runCoinsSatisfy_iff`
- `WordRAM.Sim.runCoinsSatisfy_nil`
- `WordRAM.Sim.runNextCoins`
- `WordRAM.Sim.runNextCoins_eq`
- `WordRAM.Sim.runNextCoins_length`
- `WordRAM.Sim.runNextCoins_prefix`
- `WordRAM.Sim.runNextCoins_read`
- `WordRAM.Sim.runNextCoins_satisfy`
- `WordRAM.Sim.source_pc_lt`
- `WordRAM.Sim.source_step_coin_congr`
- `WordRAM.Sim.source_step_rd`
- `WordRAM.Sim.source_verdict_not_coin`
- `WordRAM.Sim.source_verdict_stream`

### RunChoices.lean

Finite timed choice slices, concatenation and extraction of a finite word prefix.

- `WordRAM.Sim.runChoices`
- `WordRAM.Sim.runChoices_append`
- `WordRAM.Sim.runChoices_const`
- `WordRAM.Sim.runChoices_eq`
- `WordRAM.Sim.runChoices_getD`
- `WordRAM.Sim.runChoices_head`
- `WordRAM.Sim.runChoices_length`
- `WordRAM.Sim.runChoices_one`
- `WordRAM.Sim.runChoices_succ`
- `WordRAM.Sim.runChoices_take`
- `WordRAM.Sim.runChoices_zero`

### RunDriver.lean

A single driver interface for timed schedules and prescribed RAM streams.

- `WordRAM.Sim.RunDriver`
- `WordRAM.Sim.RunDriver.Follows`
- `WordRAM.Sim.RunDriver.Respects`
- `WordRAM.Sim.RunDriver.casesOn`
- `WordRAM.Sim.RunDriver.coin`
- `WordRAM.Sim.RunDriver.ctorIdx`
- `WordRAM.Sim.RunDriver.dispatch`
- `WordRAM.Sim.RunDriver.follows_iff`
- `WordRAM.Sim.RunDriver.mk`
- `WordRAM.Sim.RunDriver.mk.inj`
- `WordRAM.Sim.RunDriver.mk.injEq`
- `WordRAM.Sim.RunDriver.mk.noConfusion`
- `WordRAM.Sim.RunDriver.mk.sizeOf_spec`
- `WordRAM.Sim.RunDriver.noConfusion`
- `WordRAM.Sim.RunDriver.noConfusionType`
- `WordRAM.Sim.RunDriver.ofCoins`
- `WordRAM.Sim.RunDriver.ofCoins_coin`
- `WordRAM.Sim.RunDriver.ofCoins_dispatch`
- `WordRAM.Sim.RunDriver.ofCoins_respects`
- `WordRAM.Sim.RunDriver.ofCoins_word`
- `WordRAM.Sim.RunDriver.ofSchedule`
- `WordRAM.Sim.RunDriver.ofSchedule_coin`
- `WordRAM.Sim.RunDriver.ofSchedule_dispatch`
- `WordRAM.Sim.RunDriver.ofSchedule_follows`
- `WordRAM.Sim.RunDriver.ofSchedule_word`
- `WordRAM.Sim.RunDriver.rec`
- `WordRAM.Sim.RunDriver.recOn`
- `WordRAM.Sim.RunDriver.respects_iff`
- `WordRAM.Sim.RunDriver.word`
- `WordRAM.Sim.RunDriver.word_head`
- `WordRAM.Sim.RunDriver.word_length`

### RunStep.lean

Embedded phase correctness, live dispatch, restored heads and instruction/verdict endpoints.

- `WordRAM.Sim.RunSetup.host_ordinary`
- `WordRAM.Sim.RunSetup.host_phase_dispatch`
- `WordRAM.Sim.RunSetup.host_phase_run`
- `WordRAM.Sim.RunSetup.host_slice_prefix`
- `WordRAM.Sim.RunSetup.host_verdict`
- `WordRAM.Sim.RunSetup.phase_branch_prefix`
- `WordRAM.Sim.RunSetup.phase_correct`
- `WordRAM.Sim.RunSetup.resumeTag_of_step`

### RunSpace.lean

Exact startup/constant-word space transfer, common head envelopes and additive visited-cell union bounds.

- `WordRAM.Sim.runEnvelope_append`
- `WordRAM.Sim.runSpace_append_le`
- `WordRAM.Sim.runSpace_eq_of_clamped_heads`
- `WordRAM.Sim.runSpace_replicate`

### RunStartup.lean

Startup inside the standard host, including a stationary dispatch with no extra visited cells.

- `WordRAM.Sim.RunSetup.host_initCfg`
- `WordRAM.Sim.RunSetup.startup_run`
- `WordRAM.Sim.RunSetup.startup_trajectory`

### RunCosts.lean

Finite maximum phase coefficient and monotone uniform block time/radius.

- `WordRAM.Sim.RunSetup.blockRadius`
- `WordRAM.Sim.RunSetup.blockRadius_eq`
- `WordRAM.Sim.RunSetup.blockRadius_mono`
- `WordRAM.Sim.RunSetup.blockTime`
- `WordRAM.Sim.RunSetup.blockTime_eq`
- `WordRAM.Sim.RunSetup.blockTime_mono`
- `WordRAM.Sim.RunSetup.phaseCost`
- `WordRAM.Sim.RunSetup.phaseCost_eq`
- `WordRAM.Sim.RunSetup.phase_cost_le`
- `WordRAM.Sim.RunSetup.phase_radius_le`
- `WordRAM.Sim.RunSetup.phase_time_le`

### RunInstruction.lean

One instruction executed by either driver, with one time/head bound and the schedule clause.

- `WordRAM.Sim.RunSetup.instruction_run`

### RunPrefix.lean

Execution certificates and their zero, verdict, prepend and halting-comparison constructors.

- `WordRAM.Sim.RunExecution`
- `WordRAM.Sim.RunExecution.casesOn`
- `WordRAM.Sim.RunExecution.cells`
- `WordRAM.Sim.RunExecution.coin_index`
- `WordRAM.Sim.RunExecution.coins_extend`
- `WordRAM.Sim.RunExecution.coins_ok`
- `WordRAM.Sim.RunExecution.completed`
- `WordRAM.Sim.RunExecution.ctorIdx`
- `WordRAM.Sim.RunExecution.ending`
- `WordRAM.Sim.RunExecution.envelope`
- `WordRAM.Sim.RunExecution.finish`
- `WordRAM.Sim.RunExecution.follows`
- `WordRAM.Sim.RunExecution.last`
- `WordRAM.Sim.RunExecution.mk`
- `WordRAM.Sim.RunExecution.mk.inj`
- `WordRAM.Sim.RunExecution.mk.injEq`
- `WordRAM.Sim.RunExecution.mk.noConfusion`
- `WordRAM.Sim.RunExecution.mk.sizeOf_spec`
- `WordRAM.Sim.RunExecution.noConfusion`
- `WordRAM.Sim.RunExecution.noConfusionType`
- `WordRAM.Sim.RunExecution.of_verdict`
- `WordRAM.Sim.RunExecution.outCoins`
- `WordRAM.Sim.RunExecution.prepend`
- `WordRAM.Sim.RunExecution.rec`
- `WordRAM.Sim.RunExecution.recOn`
- `WordRAM.Sim.RunExecution.run`
- `WordRAM.Sim.RunExecution.source`
- `WordRAM.Sim.RunExecution.steps`
- `WordRAM.Sim.RunExecution.time_bound`
- `WordRAM.Sim.RunExecution.word`
- `WordRAM.Sim.RunExecution.zero`

### RunInduction.lean

The single fuel induction shared by deterministic and nondeterministic targets.

- `WordRAM.Sim.RunSetup.run_execution`

### RunBounds.lean

One fixed coefficient absorbing startup, instruction and interval costs while retaining leading TW/SW.

- `WordRAM.Sim.RunSetup.boundCost`
- `WordRAM.Sim.RunSetup.boundCost_eq`
- `WordRAM.Sim.RunSetup.space_total_le`
- `WordRAM.Sim.RunSetup.time_total_le`

### RunInput.lean

Startup plus the shared induction, source verdict/output identification and final resource bounds.

- `WordRAM.Sim.RunSetup.input_run`

### RunBranch.lean

Uniform halting and space for arbitrary sufficiently long branches, using their timed schedules.

- `WordRAM.Sim.RunSetup.branch_run`

## Foreign definitions and their published readers

The compiled boundaries contain the following ordinary other-file TCSlib definitions. Type
abbreviations and structure projections remain reducible type/field notation. Definitions
only appearing as opaque terms in reader statements or interface types require no reduction;
those cases are marked below. The complete-source seals made every listed head irreducible
in each consuming file and removed definition simp-unfold entries. Thus implicit reduction,
including through change/rfl/instance elaboration, was checked as well as explicit syntax.

| Foreign definition | Reader or opaque use |
|---|---|
| `Complexity.logSpace` | `Complexity.logSpace_eq` |
| `Turing.Action.apply` | `Action.apply_state` |
| `Turing.Action.mapState` | opaque action term in published host-transfer equations |
| `Turing.Cfg.init` | `Cfg.init_state`, `_inputPos`, `_workTapes`, `_workTapePos`, `_output` |
| `Turing.Cfg.inputSymbol` | opaque symbol term in transition reader statements |
| `Turing.Cfg.mapState` | `Cfg.mapState_state`, `_inputPos`, `_workTapes`, `_workTapePos`, `_output` |
| `Turing.Cfg.workTapeSymbols` | opaque symbol term in transition reader statements |
| `Turing.FinNDTM.AcceptsWithin` | `FinNDTM.acceptsWithin_iff`, `AcceptsWithin.mono` |
| `Turing.FinTM.ComputesInTime` | `FinTM.computesInTime_iff`, `ComputesInTime.mono`, `.spaceUsed_le_of_halt` |
| `Turing.FinTM.bufferTape` | opaque term in existing startup interface; no reduction |
| `Turing.KeyTableAt` | `keyTableAt_iff` |
| `Turing.MultiTapeTM.initCfg` | `MultiTapeTM.initCfg_eq` |
| `Turing.MultiTapeTM.runFrom` | zero/one/succ/add/of_halt run equations and existing embedding run lemmas |
| `Turing.MultiTapeTM.spaceUsed` | `spaceUsed_eq_sum` and existing startup space interface |
| `Turing.MultiTapeTM.spaceUsedByTape` | `spaceUsedByTape_eq_card` |
| `Turing.MultiTapeTM.step` | `step_of_some`, `step_of_halt`, `runFrom_one` |
| `Turing.MultiTapeTM.toNDTM` | `toNDTM_q₀`, `_tr`, `_runWith` |
| `Turing.MultiTapeTM.visitedByTapeHead` | `mem_visitedByTapeHead_iff` |
| `Turing.NDTM.HaltsWithin` | `NDTM.haltsWithin_iff` |
| `Turing.NDTM.fixChoice` | `fixChoice_q₀`, `_tr`, `stepWith_eq_fixChoice_step`, slice run transfer |
| `Turing.NDTM.initCfg` | `NDTM.initCfg_eq` |
| `Turing.NDTM.phaseHostND` | `phaseHostND_fixChoice`, `phaseHostND_run` |
| `Turing.NDTM.runWith` | nil/cons/append/of_halt equations and published host/embedding transfers |
| `Turing.NDTM.spaceUsedWith` | `spaceUsedWith_eq`, `spaceUsedWith_append_of_halt` |
| `Turing.NDTM.stepWith` | `stepWith_of_some`, `stepWith_eq_fixChoice_step` |
| `Turing.NDTM.visitedWith` | `visitedWith_eq` |
| `Turing.ReachesWithin` | `reachesWithin_iff` |
| `Turing.TableAt` | `tableAt_iff` |
| `Turing.WordAt` | `wordAt_iff` |
| `Turing.embedEmitCfg` | state/output/selected tape/position/frame equations, reconstruction and map-state equations |
| `Turing.embedEmitTM` | `embedEmitTM_q₀`, `embedEmitTM_runFrom`, frame equations |
| `Turing.fieldsTape` | opaque layout term after `tableAt_iff`/`keyTableAt_iff` |
| `Turing.joinFields` | opaque layout term after encoding readers |
| `Turing.keyFields` | opaque layout term after `keyTableAt_iff` |
| `Turing.keyTableLength` | opaque bound term in the existing instruction interface |
| `Turing.phaseHostTM` | `phaseHostTM_q₀`, `phaseHostTM_tr_of_red_none` |
| `Turing.tableFields` | opaque layout term after `tableAt_iff` |
| `WordRAM.HaltsWithin` | `haltsWithin_iff`, `HaltsWithin.unique` |
| `WordRAM.InRange` | `inRange_iff` |
| `WordRAM.Sim.Encodes` | `encodes_iff` |
| `WordRAM.Sim.ImmBound` | `immBound_iff` |
| `WordRAM.Sim.RunCoinsAgree` | `runCoinsAgree_iff`, append/prefix/read lemmas |
| `WordRAM.Sim.RunCoinsSatisfy` | `runCoinsSatisfy_iff`, nil/append lemmas |
| `WordRAM.Sim.RunDriver.Follows` | `RunDriver.follows_iff` |
| `WordRAM.Sim.RunDriver.Respects` | `RunDriver.respects_iff` |
| `WordRAM.Sim.RunDriver.ofCoins` | `ofCoins_respects` and generated coin/word/dispatch readers |
| `WordRAM.Sim.RunDriver.ofSchedule` | `ofSchedule_follows`, generated coin/word/dispatch readers |
| `WordRAM.Sim.RunSetup.blockRadius` | `blockRadius_eq`, monotonicity and phase-bound lemmas |
| `WordRAM.Sim.RunSetup.blockTime` | `blockTime_eq`, monotonicity and phase-bound lemmas |
| `WordRAM.Sim.RunSetup.boundCost` | `boundCost_eq` |
| `WordRAM.Sim.RunSetup.host` | `host_fixChoice`, `host_q₀`, `host_runWith`, `host_initCfg` |
| `WordRAM.Sim.RunSetup.phase` | `phase_none`, `phase_some` |
| `WordRAM.Sim.RunSetup.phaseCost` | `phaseCost_eq`, `phase_cost_le` |
| `WordRAM.Sim.RunSetup.phaseDecidableEq` | opaque synthesized instance; no reduction |
| `WordRAM.Sim.RunSetup.phaseFintype` | opaque synthesized instance; no reduction |
| `WordRAM.Sim.RunSetup.redirect` | `redirect_none`, `redirect_some` |
| `WordRAM.Sim.RunSetup.resumeTag` | `resumeTag_eq`, `resumeTag_of_step` |
| `WordRAM.Sim.TableOf` | opaque memory-table term in encoding readers |
| `WordRAM.Sim.immediates` | `immediates_def` for default rejection; opaque finite-set key elsewhere |
| `WordRAM.Sim.isCoin` | `isCoin_def` |
| `WordRAM.Sim.isVerdict` | `isVerdict_def` |
| `WordRAM.Sim.jumpTarget` | opaque target in source/phase interfaces; `resumeTag_eq` reads the redirect |
| `WordRAM.Sim.runBank` | generated state/input/output/tape/head readers, reconstruction lemmas |
| `WordRAM.Sim.runChoices` | `runChoices_eq`, length/append/head/constant/take lemmas |
| `WordRAM.Sim.runEmbedND` | generated q₀/tr readers, `runEmbedND_fixChoice`, `runEmbedND_runWith` |
| `WordRAM.Sim.runNextCoins` | `runNextCoins_eq`, length/prefix/read/satisfy lemmas |
| `WordRAM.Sim.runPosition` | generated `runPosition_val`, `runPosition_fetch` |
| `WordRAM.WordSizeComputable` | `wordSizeComputable_iff` |
| `WordRAM.XCfg.init` | `XCfg.init_def` |
| `WordRAM.XInstr.touches` | opaque exact-touch term; no reduction |
| `WordRAM.XStepsIn` | `XStepsIn.zero_iff`, `XStepsIn.succ_iff` |
| `WordRAM.coinWord` | opaque term after `xstep_def`; no reduction |
| `WordRAM.effect` | opaque term after `xstep_def`; no reduction |
| `WordRAM.inBitWord` | opaque term after `xstep_def`; no reduction |
| `WordRAM.initMem` | opaque term in `XCfg.init_def` and startup encoding |
| `WordRAM.xstep` | `xstep_def`, existing source-run interface |

## Diff against the base

```text
 TCSlib/Complexity/RAMSimulation.lean               |  29 ++
 TCSlib/Complexity/RAMSimulation/Sim/RunBounds.lean | 115 ++++++
 TCSlib/Complexity/RAMSimulation/Sim/RunBranch.lean |  84 +++++
 .../Complexity/RAMSimulation/Sim/RunChoices.lean   | 116 ++++++
 TCSlib/Complexity/RAMSimulation/Sim/RunCosts.lean  |  95 +++++
 TCSlib/Complexity/RAMSimulation/Sim/RunDriver.lean | 102 ++++++
 .../Complexity/RAMSimulation/Sim/RunEncoding.lean  | 143 ++++++++
 TCSlib/Complexity/RAMSimulation/Sim/RunHost.lean   | 242 +++++++++++++
 .../Complexity/RAMSimulation/Sim/RunInduction.lean |  88 +++++
 TCSlib/Complexity/RAMSimulation/Sim/RunInput.lean  | 114 ++++++
 .../RAMSimulation/Sim/RunInstruction.lean          | 105 ++++++
 TCSlib/Complexity/RAMSimulation/Sim/RunPhase.lean  | 248 +++++++++++++
 TCSlib/Complexity/RAMSimulation/Sim/RunPrefix.lean | 269 ++++++++++++++
 TCSlib/Complexity/RAMSimulation/Sim/RunSlices.lean | 148 ++++++++
 TCSlib/Complexity/RAMSimulation/Sim/RunSource.lean | 249 +++++++++++++
 TCSlib/Complexity/RAMSimulation/Sim/RunSpace.lean  | 148 ++++++++
 .../Complexity/RAMSimulation/Sim/RunStartup.lean   | 148 ++++++++
 TCSlib/Complexity/RAMSimulation/Sim/RunStep.lean   | 398 +++++++++++++++++++++
 TCSlib/Complexity/RAMSimulation/Simulation.lean    | 196 ++++++----
 TCSlib/Complexity/RAMSimulation/WordSize.lean      |   8 +
 TCSlib/Complexity/TuringMachine/Build/Embed.lean   |   4 +
 .../TuringMachine/NondeterministicSpace.lean       |  13 +
 22 files changed, 3000 insertions(+), 62 deletions(-)
```

## Delivery

`fill-ram-run-r2.zip` contains this report, the 22 source files at their repository paths,
`fill-ram-run-r2.patch`, all round-2 logs and reproducible probes/tools, and `SHA256SUMS`.
The original bundle provenance and round-1 archive are included as inputs. No oleans, package
cache, unrelated blueprint files, or Git metadata are included. The archive is delivered only
to `arora-barak-ch3-4/inbox/fill-ram-run/` on `exchange/pass-shelat-ch5-8`, after pulling with
rebase, without force or a pull request. No source branch is pushed.

The existing shared exchange checkout could not pull because an incoming file collided with
another fill's untracked `fill-ram-input-startup.zip`. The delivery uses an isolated managed
worktree based on the fetched exchange tip. The shared checkout's other fill files were left
in place. The failed first pull is retained in the delivery attempt log.
