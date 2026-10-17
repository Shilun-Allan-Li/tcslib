# MIG-24's candidate triage (maintainer, 2026-10-17; read-only)

**Input:** the overnight library-wide screen's 92 candidate pairs, those at 90% or more not owned by
MIG-1, MIG-2 or the small-pair floor (`README.md`): 58 in `TuringMachine/` and 34 in
`SpaceComplexity/`.

**Method** (`triage-tm.tsv`, `triage-sc.tsv`; the classifier `classify.py.txt`):
- each pair's two declarations were extracted at #118's head with `declfreeze`'s chunker;
- their docstrings and comments were stripped, and the token sequences compared;
- **rename-mirror:** equal up to a consistent renaming of identifiers. There are 9 such pairs.
- **variant:** any other difference. These carry their equal-token percentage. There are 82, and 1
  pair's declaration was not found.
- each pair was then assigned to an owner by its files.

The screen measures text, not proof structure, so a family is a factoring candidate only once read.

## Result: most candidates belong to an existing item

| Family | Pairs | Shared chars (largest) | Owner | Why |
|---|---|---|---|---|
| **`SpaceComplexity/`: ARM, codec, Savitch, `Machines/`** (ARMSim's `sim_*`, `ARMLoops`, `Codec/Run`, `Codec/Deciders`, `SavitchARM/Recursion`, NARM, the reachability family `AReach`/`MReach`/`Rch`/`Reaches`/`ReachesB`, `Parse2`/`ParsePlain`, `Bin`/`FragDec`) | 34 (all) | 960 | **ARM-2**, coordinated with Hydroxyi (the user, 2026-10-14) | Every file is in ARM-2's scope, which names the reachability family, `move2_run`/`dmove_run` and the codec layouts. `Machines/` is Hydroxyi's library. The 12.2c window, not MIG-24. |
| The chapter-1 universal (`Universal`, `UniversalBlock`, `UniversalInterpreter`, `UniversalStartup`, `Oblivious*`) | 9 | 911 | **MIG-2 with U-1**, and MIG-7 for `UniversalStartup` | The timed layer, the interpreter's re-derivation and the startup; they wait on U2. |
| The catalog's `a2_` copies (`loop_halted_run` ↔ `a2_loop_halted_run`, `a2_map_*`) and `catalog_redirect_step` ↔ `Wrappers.redirect_step` | 5 | 826 | **MIG-1** | Its deletion plan retires the copies; the redirect pair is a 94% rename-mirror between two MIG-1 files. |
| `Basic.Segment.trans` ↔ `CfgRecord.recordRun_trans` | 1 | 291 | **MIG-12** (in flight) | `CfgRecord` moves onto the contract layer. |
| `SingleTape.dg_sweep_prefix` / `_reverse_prefix` | 1 | 232 | **MIG-3** | `one_work_tape` reuses `dg_all_inputs`. |
| `EmitIterBody.rwTape_none` / `_some` | 1 | 1,015 | **MIG-5** | The emitting-iteration files' re-proved run facts. |
| `Codes2Tape.Code2TM.serialize` ↔ `NDCodes.CodeNDTM.serialize` | 1 | 290 | **MIG-6** (CH34-D2) | The parse layer's parameterization. |
| `CounterLoop.counterLoopTM` ↔ `counterLoopTMVia` | 1 | 261 | MIG-4, **closed as kept** (the user, 2026-10-16) | The identity instance stays; no action. |
| `Zone.zoneShiftIn` / `Out`, `zoneSide_rebalance_right` / `zoneTrackTape_rebalance_right` | 2 | 314 | §13d (the zone statements, gated) | Mirrored by design (two directions of a gated contract). Recorded, no action until G4 integrates. |

## What is left for MIG-24 (`TuringMachine/`; 37 pairs in 8 groups)

The other 21 `TuringMachine/` pairs belong to the items above (58 in all).

| # | Family | Files | Pairs | Shared chars | Reading |
|---|---|---|---|---|---|
| T1 | **The rewind family:** `Simulation.timed_rewind`, `rewind_heads`, `rewind_from_any`, `Primitives.catalogRewind`, `Loop.loop_rewind_bounded` | Simulation, Primitives, Loop | 4 | 465 | Five proofs that a head walks back to the origin. One rewind lemma over a bound, with the others as corollaries. 78–99% equal tokens. |
| T2 | **`Primitives`' mirrored emitter lemmas:** `emitterP2_body_erase_left`/`_right`, `_prepare_rewind_candidate`/`_suffix`, `_pair_frame`/`_small_frame`, `_left_frame`/`_right_frame`, `emitterP2PairIndex`/`SmallIndex`, `emitterSplit_find` ↔ `splitFind_eq`, and `Loop.emCall_first_entry` ↔ `emitter_first_entry` (a 100% rename-mirror) | Primitives, Loop | 7 | 1,078 | Left and right, pair and small: a direction or a variant parameter, one proof each. |
| T2b | **`Primitives`' parser variants:** `extract_replay` ↔ `rawStrip_replay`, `lenParse_first` ↔ `lenSuffix_run`, `mapParse_block` ↔ `mapParse_first`, `emitterToken_double` ↔ `_separator` | Primitives | 4 | 390 | Low equal-token shares (27–73%): probably different proofs with shared scaffolding. Read before factoring. |
| T3 | **`Loop`'s call-bank pair:** `emCall_bank_initial` / `_final` | Loop | 1 | **3,070** | The largest single pair (85% equal tokens): one bank lemma at a phase parameter. |
| T4 | **`Composition`'s buffered-composition family:** `bufferedCompTM_computes_iff` ↔ `exists_comp_partial`, `bufferedCompTM_computesFunInTime` ↔ `computesFunInTime_comp`, `_on_image` ↔ `exists_comp_on_image` | Composition | 3 | 1,207 | Each public corollary re-proves its general form (86–95%). Derive the corollaries. |
| T5 | **`Catalog`'s copy, transfer, clear and increment rows:** `copyTM_run`, `transferTM_run`, `clearTM_run`, the `Cfg.ofWords_copy_endpoint` / `_transfer_endpoint` lemmas, `copyMapTM` ↔ `transferMapTM`, `clearTM` ↔ `copyMapTM`, `incrementTM_run_succ_ofCfg` ↔ `_overflow_ofCfg` | Catalog | 9 | 617 | One sweep-row argument, read three ways. The contract layer (MIG-11's framed rows) may already subsume it. |
| T6 | **`Catalog`'s pair-projection space rows:** `computesFunInTime_pairFst`/`Snd`/`Concat_spaceUsed` | Catalog | 3 | 305 | One lemma over the extractor's selector (97%). |
| T7 | **Singletons:** `Sweep.sweep_run`/`_reverse` (638, 97%); `Loop.loop_halted_run`/`loop_run` (627, 88%); `Embed.embedEmitRetTM`/`embedSilentRetTM` (215); `Basic.ReturnContract`/`RoundContract` (412, structures); `Encoding.toCodeTM_computesInTime_iff` ↔ `exists_codeTM_spaceUsed` (293, 49%); `Simulation.bufferedSecondCfg_run` ↔ `VirtualInput.vhostEmitTM_runFrom` (241, two lockstep hosts) | Sweep, Loop, Embed, Contract/Basic, Encoding, Simulation, VirtualInput | 6 | 638 | Read case by case. The two lockstep hosts could both derive from `Turing.Lockstep`. The contract structures may be intentional. |

## The scheduling question (for the user)

T1–T6 (with T2b) live in `Simulation`, `Primitives`, `Loop`, `Composition` and `Catalog`. MIG-1's fill batches
F-A to F-D edit those same files (its scope), and none is briefed yet. **Recommended:** fold T1–T6
and T2b into MIG-1's batches as named factoring obligations. Each file is then edited, replayed and gated
once, and MIG-1's deletions and MIG-24's factoring cannot collide. T7's singletons go into the next PR
that edits their file. The alternative is a separate MIG-24 pass after MIG-1, which costs a second
round of replays over the same closures.
