# MIG-1 overnight megafill — final delivery (revision 2) — **PARTIAL**

**Delivered head: `246d81d2ce247d9e76dcc0ffbfc5080fd1d8fde5`** on `fill/mig1-mega` (base
`83ac315ed9e7089466bd16a32f3b71fbadc556d2`, records `7df0d047d501a1d08982d17d20208faf49d39131`).
This zip supersedes `fill-mig1-mega.zip` (revision 1, head `cbfdba81…`, already pushed and kept).
The revision-1 report follows unchanged below this section as the record of the main fill; this
section states what revision 2 changes and re-validates. Where the two disagree, this section
is current.

## What revision 2 adds (three commits after `cbfdba81`)
1. `16d61dcd` — **MIG-24 T1, Primitives part: done.** Private `catalogRewind` was
   statement-identical to the public `Turing.FinTM.timed_rewind`; retired, its four call sites
   use `timed_rewind`. **MIG-24 T3: partial.** The twelve frame-exactness side proofs in
   `emCall_bank_initial`/`_final` now cite two private lemmas `emCall_pair_not_mem`,
   `emCall_triple_not_mem` (the screened pair falls from 3,070 to 2,096 shared characters; the two
   lemmas still differ in the selected bank's contents and the cleaned-prefix index, so a single
   bank lemma at a phase parameter was not reached). CertShell and CodeSimulator read the
   canonical seam's state through `Cfg.ofWords_state` instead of `rfl`. Primitives: several moved
   forwarding-map / poly-space steps read `runFrom 0`, `runFrom 2`, `initCfg` and `Action.apply`
   through published equations.
2. `0b88b8e3` — the T3-factored bank lemmas use the published `Turing.embedEmitCfg_unselected`
   instead of the time-0 instance of `embedEmitTM_frame` (a definitional `runFrom 0` read);
   CodeSimulator reads two more seam states through `Cfg.ofWords_state`.
3. `246d81d2` — `pairMapSndTM_computes` (a new public proof) and the moved `fwdMap_finish` no longer
   pass Encoding's `pairEncode` (nor `initCfg`/`Cfg.init`) to `simp`; they use the published
   `Turing.pairEncode_eq`.

No statement, public name, import or witness table changed in revision 2: `freeze-final-r3.log`
— RESULT PASS, exactly the 3 authorized additions and 6 authorized removals relative to the base,
the 2 approved imports; only the 11 owned files differ (`changed-files-r3.txt`). Static admissions
in owned files: 3 (the frozen RAM theorems).

## Validation of the delivered head
- **Final sweep, two parts covering all 641 modules at the delivered tree.**
  `logs/final-sweep-2/`: the complete 641-module order at `0b88b8e3` (clean tree), **641/641
  exit 0, 0 errors**, 10:44:50Z–12:20:46Z, static 149 = Lean 149 admissions, no mismatch.
  `logs/final-sweep-3-downstream-of-Primitives/`: the only file changed between `0b88b8e3` and
  `246d81d2` is `Build/Primitives.lean`; every module of the final order that imports it
  transitively (**223 modules**, computed from the import graph, `after-prim-full.txt`) was
  recompiled in order at `246d81d2` (clean tree): **223/223 exit 0, 0 errors**, 12:26:46Z–13:30:17Z, static 61 = Lean 61 admissions, no mismatch. The other 418 modules
  have byte-identical sources and an unchanged import closure, so their sweep-2 results are
  results for this tree. (Revision 1's full sweep at `cbfdba81` is `final-sweep-1/`.)
- **Axioms** at the delivered head (`axioms/Ax_final-r3.*`): all 60 names (the 17 targets, the 3 exports and every public declaration whose proof body changed) within {propext, Classical.choice, Quot.sound}.
- **Compiled census** at the delivered head (`census-head-final-r3.out`): base 1,234 → 1,205 non-private constants; added exactly the 3 exports and the derived instance `instDecidableEqFwdMapState` (+ compiler auxiliaries), removed exactly the 6 retired rows and `instDecidableEqA2_MapState` (+ auxiliaries); identical to revision 1's census.
- **Screens**: the fresh base screen (identical to the maintainer's) and the final screen at
  `246d81d2` (`screens/screen-final-r3.txt`): **1,003 declarations, 623 pairs, 208,120 chars**
  (base 1,279 / 1,589 / 636,810). Delta `pair-delta-final.txt`: 93 head-only, 1,059 base-only;
  `new-pairs-classified-final.txt`: 45 moved-and-renamed, 48 others, of which 8 share ≥ 200
  characters: the moved summation bodies (`loopHostTM_decides`↔`_finds`, and `emitLoopTM_computes`
  with each), the `branchTM_initCfg_false`↔`_true` mirror, and `fwdMap_emit`↔`fwdMap_backA`/`_backB`
  (phase lemmas of the moved forwarding controller, over the threshold after the seal-repair
  rewrites). Per file (`per-file-pairs-final.txt`, base → final): Catalog 1,074 → 92, Primitives
  713 → 278, Loop 292 → 115, Simulation 88 → 57, Wrappers 74 → 33, CodeSimulator 70 → 70,
  Composition 52 → 26, TimeConstructible 52 → 12, Encoding 4 → 7.
- **Seals at the delivered head**: Composition, Encoding, TimeConstructible, Simulation, Wrappers,
  Catalog: as revision 1 (sources unchanged). **Loop** (`Seal_LoopR2.*`, now including
  `emCall_bank_initial`/`_final` and the two new helpers): **exit 0, 0 errors**. **Primitives**
  (`Seal_PrimitivesR3.*`, now also sealing `Turing.pairEncode`): **17 errors, all in
  verbatim-moved material** (`fwdMap_*`, `poly_space`); the new public proofs and the three specs
  have no foreign definition among their `simp`/`rw`/`unfold` arguments (`argscan/Primitives.txt`).
  **CertShell/CodeSimulator strict runs** (also sealing `Cfg.ofWords`): the reads introduced by
  this fill are fixed; what remains are pre-existing reads elsewhere in the same declarations —
  `(vhostCfg …).state` in `cert_prepare_exists` and `Cfg.mapState` of a `Cfg.ofWords` seam in
  `canonPreserveInstall` (E3).

## Updated dispositions and escalations
- MIG-24: **T1 done** (Simulation, Loop, Primitives); **T3 partial**; T2, T5 not done; T2b as
  revision 1 (replay pair not factored); T4, T6 done; T7 inspected.
- **E3** (new; pre-existing reads, no published statement): `Turing.Cfg.ofWords_mapState :
  (Cfg.ofWords q w).mapState f = Cfg.ofWords (f q) w` (Convention) and
  `Turing.vhostCfg_state : (vhostCfg c tag p pre).state = c.state.map …` (VirtualInput), or
  `simps` field equations for `vhostCfg`.
- E1, E2 unchanged.

## Line sizes at the delivered head (base → final)
Composition 829 → 773; Simulation 1212 → 1268; Wrappers 806 → 1004; Encoding 797 → 793;
TimeConstructible 490 → 579; Loop 5294 → 5409; Primitives 7023 → 7579; Catalog 13241 → 4058;
CertShell 904 → 927; CodeSimulator 9124 → 9129; WordSize 98 → 98.

---

# Revision 1 report (head `cbfdba81…`), retained

# MIG-1 overnight megafill — final delivery — **PARTIAL** (all 17 targets and the 3 gated exports proved; validation complete at the delivered commit; seal of moved forwarding/polynomial material and some MIG-24 factoring incomplete)

Agent: **Claude** (Anthropic), single session, one clone, one cumulative branch.
Repository `Shilun-Allan-Li/tcslib`; branch `fill/mig1-mega` created at exactly
**`83ac315ed9e7089466bd16a32f3b71fbadc556d2`** (from `complexity/arora-barak-ch3-4`; ancestor check passed);
issued records/brief/inputs **`7df0d047d501a1d08982d17d20208faf49d39131`**. Delivered head: `HEAD.txt`
(**`cbfdba8102e6a5d956a1fdd2be7518b490a5abac`**), commits in `COMMITS.txt`, all authored as
`Claude <noreply@anthropic.com>`. Session start 2026-11-07T07:22:26Z; branch created 07:23:15Z.

## Verdict
**Partial.** Every one of the 17 existing target admissions is proved, the three gated forwarding
exports are added with complete proofs, the six canonical rows are retired with consumers
re-pointed, and Catalog's copies are deleted. At the delivered commit the full **641-module**
final sweep passed (0 failures), both fresh copy-text screens ran, the compiled census and the
axiom walks are clean, and the freeze is exactly the authorized delta. It is **not** labelled
complete because:
1. **Rule-10 seal of moved material in Primitives is incomplete**: sealing the verbatim-moved
   forwarding family (`fwdMap*`, from Catalog `a2_map*`) and `poly_space` gives 18 definitional-read
   errors, and the moved `poly_step`/`fwdMap*` proofs still pass `MultiTapeTM.step` /
   `Action.apply` to `simp`/`unfold` (inventory in `seal/argscan/`, `seal/Seal_Primitives.out`).
   All *new* proofs (the 17 specs, the 3 exports, all re-pointed rows) seal cleanly.
2. MIG-24 T2, T2b (partly), T3 and T5 factoring were not completed (dispositions below).
3. Escalations E1–E2 (missing public field/tape-count equations) leave documented definitional reads.

## Checkpoints delivered (all under `arora-barak-ch3-4/inbox/fill-mig1-mega/`)
cp01 (F-A same-home group), cp02 (F-A), cp03 (F-C; also the cp04 recovery point — the
time/configuration and space groups landed in one checked commit), cp05 (F-B targets), cp07 (F-D
deletions and consumers), and this final zip. cp04 and cp06 were not delivered as separate zips
(their content is in cp03 and cp05/cp07 respectively).

## Environment (fresh, this host)
- Preflight (`logs/preflight.log`): `nproc` 4; cgroup v1, `memory.limit_in_bytes`
  9223372036854771712 (no limit), in use 36,806,656 B (`usage − total_cache + total_shmem`), so
  headroom = MemAvailable 15.39 GiB; clone filesystem ext4 `/dev/vda`, 29.09 GiB free; scratch,
  TMPDIR and HOME on the same ext4 (no tmpfs). **PASS**.
- Toolchain `leanprover/lean4:v4.25.0` installed by elan (`toolchain-install.log`); Lean started
  normally — **the `/proc` shim was not used**.
- Cache store before fetch: absent (0 files) (`cache-store.log`); narrowed fetch of the **239**
  roots (recomputed from the final order: identical to `inputs/mathlib-roots.txt`) downloaded
  3,331 files, decompressed 3,331, 0 failures, exit 0 (`cache-get.log`); 0 empty oleans;
  package check last line: `packages present=11 match=11 mismatch=0 absent=4 («doc-gen4»,
  UnicodeBasic, BibtexQuery, MD4Lean)` — RESULT PASS; cache probe (`import
  Mathlib.Algebra.BigOperators.Field` through `scripts/lean_check_tree.sh`) passed after two
  setup attempts that started no Lean (`/usr/bin/time` missing; probe path outside the root).
- Scratch `/work/mig1/scratch` (`TCSLIB_SCRATCH`), `TCSLIB_REPO=/work/mig1/clone`,
  `TCSLIB_LEAN_SLOTS=1`, one olean tree `TCSLIB_OLEANS=/work/mig1/scratch/oleans` (`tools/env.sh`);
  packet extracted to `/work/mig1/packet` outside the clone before checkout (`packet-extract.log`:
  bundle SHA-256 `43ebed18…62ebcf`, 324 sections, 0 problems; fresh Git-export rebuild verified).
- One Lean process at a time (`withslot.sh` shares `leanelab.sh`'s slot lock), `nice -n 10`,
  `-j4`; no `lake build`, no bare Lean command. Process deviations: `logs/deviations.log` (D1: one
  ~3 s overlap of a `leanelab.sh` check with the base bootstrap's Catalog compile, before the
  sweep runner took the slot lock; D2: a self-deadlocked wrapper, no Lean ran).
- Bootstraps: base 51 modules (07:26–07:33, failed=0); cp02 51 modules; per-package downstream
  tails `tail-fc` (36), `tail-fb` (35), `tail-fd1` (34); a separate base-export tree for the base
  census (`base-census-bootstrap`, 51 modules, failed=0; first attempt failed before Lean started
  for a missing `lean-toolchain` file in the export).

## Targets (17 existing specifications + 3 gated forwarding exports)

| # | Package | Declaration | Status | Axioms |
|---|---|---|---|---|
| 1 | F-A | `Turing.FinTM.idTM_computes` (Composition) | proved | standard |
| 2 | F-A | `Turing.FinTM.ifEqTM_computes` (Composition) | proved | standard |
| 3 | F-A | `Turing.FinTM.condTM_computes_iff` (Composition) | proved | standard |
| 4 | F-A | `Turing.FinTM.branchTM_spaceUsed` (Simulation) | proved | standard |
| 5 | F-A | `Turing.FinTM.timedCondTM_computes` (Wrappers) | proved | standard |
| 6 | F-A | `Turing.FinTM.timedCondTM_spaceUsed` (Wrappers) | proved | standard |
| 7 | F-A | `Turing.pairDiagTM_computes` (Encoding) | proved | standard |
| 8 | F-A | `Turing.FinTM.lengthBitsTM_computes` (TimeConstructible) | proved | standard |
| 9 | F-A | `Turing.FinTM.lengthBitsTM_spaceUsed` (TimeConstructible) | proved | standard |
| 10 | F-C | `Turing.FinTM.loopHostTM_contracts` (Loop) | proved, coefficient 10 | standard |
| 11 | F-C | `Turing.FinTM.loopHostTM_decides` (Loop) | proved | standard |
| 12 | F-C | `Turing.FinTM.loopHostTM_finds` (Loop) | proved | standard |
| 13 | F-C | `Turing.FinTM.loopHostTM_spaceUsed_le_budget` (Loop) | proved, `23·k·(T+1)`, no `R` | standard |
| 14 | F-C | `Turing.FinTM.emitLoopTM_computes` (Loop) | proved | standard |
| 15 | F-B | `Turing.FinTM.polyUnaryTM_spaceUsed` (Primitives) | proved | standard |
| 16 | F-B | `Turing.FinTM.unaryTokenTM_computes` (Primitives) | proved | standard |
| 17 | F-B | `Turing.FinTM.appendBitTM_computes` (Primitives) | proved | standard |
| + | F-B | `Turing.FinTM.pairMapSndTM` (def), `pairMapSndTM_computes`, `pairMapSndTM_spaceUsed` | added; headers and definition identical to the gated contract; both proofs complete | standard |

Residual admissions in the owned files (by full name, all unchanged and frozen, out of scope):
`WordRAM.WordSizeComputable.mono`, `WordRAM.wordSizeComputable_logSpace`,
`WordRAM.wordSizeComputable_of_spaceConstructible`. Static count 20 → 3.

## Public surface
- Added (exactly the authorized three): `Turing.FinTM.pairMapSndTM`,
  `Turing.FinTM.pairMapSndTM_computes`, `Turing.FinTM.pairMapSndTM_spaceUsed`.
- Removed (exactly the authorized six): `Turing.transferTM_run`, `Turing.copyTM_run`,
  `Turing.clearTM_run`, `Turing.compareTM_run`, `Turing.incrementTM_run_succ`,
  `Turing.incrementTM_run_overflow`.
- No other public addition, removal, rename, visibility, header or relative-order change; no
  public definition body (witness table) changed (`freeze-*.log`, complete top-level headers,
  depth-aware so `(input := x)` binders are not taken for the proof delimiter).
- Imports: exactly the two approved additions — `Mathlib.Algebra.BigOperators.Fin` in
  Simulation, `TCSlib.Complexity.TuringMachine.Build.Primitives` in Catalog.

## Moved private material (original → final home)
| Original (base) | Final home and name |
|---|---|
| Catalog `f2_branch_space` (+ `f2_sum_add`, `f2_finSumEquiv`) | Simulation `branchTM_spaceUsed`; the sum split is Mathlib's `Fin.sum_univ_add` (no copy) |
| Catalog `f2_cond_space`, `f2_cond_ledger`, `f2_condHeads`, `f2_control_heads`, `f2_branch_heads`, `f2_read_heads` | Wrappers `timedCondTM_spaceUsed`, `timed_ledger`, `timedHeads`, `timed_control_heads`, `timed_branch_heads`, `timed_read_heads` (+ new private `timedReadyCfg_workTapePos`, `timedReady_dispatch`); first halt via `MultiTapeTM.exists_first_halt` |
| Catalog `f2_counter_count_space`, `f2_counter_heads`, `f2_counter_space` | TimeConstructible: merged into `counter_count` (strengthened in place) and `lengthBitsTM_spaceUsed`; new private `counter_emit_start`, `counter_halt` |
| Catalog `f2_loopHost_prepare` (fuel-head clause), `f2_loopHost_contracts`, `f2_loopCall_heads`, `f2_segment_heads`, `f2_seamed_space` | Loop: clause added to `loopHost_prepare`; `loopHost_contracts` restated (coefficient 10, two head clauses); `loopCall_heads`, `segment_heads`, `seamed_space`; `f2_space_radius` replaced by the published `MultiTapeTM.spaceUsed_le_of_abs_le` |
| Catalog `f2_polyHeads`, `f2_polyHeads_bounds`, `f2_poly_step`, `f2_poly_space` | Primitives `polyHeads`, `polyHeads_bounds`, `poly_step`, `poly_space` |
| Catalog `a2_MapState` … `a2_map_space` (forwarding controller family) | Primitives `FwdMapState` … `fwdMap_space` (renamed per the gate's fate table); `a2_mapSumEquiv`/`a2_map_sum` not moved (`Fin.sum_univ_add`) |
| Catalog `f2_head_steps`, `f2_space_of_time`, `f2_loop_rewind_bounded`, `f2_loop_first_halt`, all other `f2_`/`a2_`/`catalog_redirect*` | deleted; published `workTapePos_runFrom_mem_Icc`, `ComputesInTime.spaceUsed_le`, `timed_rewind`, `exists_first_halt` or the originals in their homes are used |
| Loop `loop_rewind_bounded` | retired; `timed_rewind` (Simulation, public, identical statement) |
| Primitives `pairMapTM` family (`mapAction` … `pairMap_computes`), `catalogPayload_computes`, `pairDupTM` family | retired (replaced by `pairMapSndTM` and `Turing.pairDiagTM`) |

Catalog: 392 → 36 private declarations (356 unreachable copies, 8,202 lines, deleted by
reachability from the public surface, `fd-prune-1.log`), 113 → 107 public; 13,241 → 4,058 lines.

## Line sizes (base → final)
Composition 829 → 773; Simulation 1212 → 1268; Wrappers 806 → 1004; Encoding 797 → 793;
TimeConstructible 490 → 579; Loop 5294 → 5439; Primitives 7023 → 7597; Catalog 13241 → 4058;
CertShell 904 → 927; CodeSimulator 9124 → 9129; WordSize 98 → 98. Total 39,818 → 31,665.
(Wrappers crosses the 1,000-line WARN threshold of the style lint; sizes are reported, not acted
on.)

## Validation at the delivered commit (fresh runs)
- **Final sweep** (`logs/final-sweep-1/`): all **641** modules of `inputs/final-order.txt` (order
  re-checked for the two new import edges, `final-order-check.log`: 0 violations, Primitives
  before Catalog) through `scripts/lean_check_tree.sh` under the slot lock, at
  `cbfdba8…` with a clean tree: **641/641 exit 0, 0 errors**, 08:37:12Z–10:10:47Z
  (5,609 s of module time; longest `ClassP/BinaryArith/DetMod` 1,331 s; peak RSS 4.66 GB at
  `Build/ZoneRebalance`). Per-module start/end/RSS/exit/raw output retained.
- **Admission counts**: static sorried declarations = Lean `declaration uses 'sorry'` warnings =
  **149** over the 641 modules, no per-module mismatch (`static-vs-lean.txt`); in the owned files
  only WordSize's three frozen RAM admissions remain.
- **Axioms** (`axioms/Ax_final.*`): 60 names (the 17 targets, the 3 exports and every public
  declaration whose proof body changed): all within {propext, Classical.choice, Quot.sound}.
- **Compiled census** (`census-head.out`, `census-base.out`, `census-delta-summary.txt`): unfiltered
  non-private constants owned by the 11 modules, base 1,234 → head 1,205. Added: 3 declarations
  (the authorized exports), 1 derived instance of a private type
  (`Turing.FinTM.instDecidableEqFwdMapState`, the renamed successor of Catalog's removed
  `instDecidableEqA2_MapState`; no name clash in the tree; open-PR refs were not fetched, per the
  brief's no-fetch rule), 126 compiler auxiliaries. Removed: exactly the 6 retired rows, the
  `A2_MapState` derived instance, 152 auxiliaries.
- **Freeze** (`freeze-final.log`, depth-aware complete headers): PASS — added exactly
  `pairMapSndTM`, `_computes`, `_spaceUsed`; removed exactly the six rows; no header, visibility,
  relative-order or public-definition-body (witness table) change; imports changed only by the two
  approved additions; only the 11 owned files differ from the base (`changed-files.txt`).
  The three exports' headers and the definition are identical to
  `inputs/forwarding-map-contract.lean.txt` (`forwarding-contract-check.log`).
- **Retirement enumeration on the final tree**: 0 hits in `TCSlib/`; outside the owned files only
  records and three live documents (`machine-library-design.md` ×2, `campaign/backlog.md`,
  `campaign/design/plans/AroraBarakChapters3-4Plan.md`) mention the retired names — for the
  maintainer.
- **Style lint** (`lint/`): FAIL count 37 → 37 (none in owned files); WARN 350 → 351 — the one new
  WARN is Wrappers' size (1,004 lines > 1,000). No new check-8 name.
- **Screens** (`screens/`): population = the 16-file `screen-population.txt` (no further Lean
  source is cited by the new proofs: they cite Configuration, Deterministic, Finite, Simulation,
  Convention, Embed and the owned files). Fresh base screen at `83ac315…`: **byte-identical** to the
  maintainer's `screen-base.txt` (SHA-256 `a6e24611…`; 1,279 declarations, 1,589 pairs, 636,810
  chars). Final screen at `cbfdba8…`: **1,002 declarations, 627 pairs, 210,586 chars**. Pair delta
  (`pair-delta.txt`): 95 head-only pairs, 1,057 base-only. Classified (`new-pairs-classified.txt`):
  50 are pre-existing pairs whose members moved and were renamed (forwarding map, poly invariant,
  conditional ledger, loop seam space); the 45 others are (a) the two summation bodies moved from
  `exists_loopTM`/`exists_loopFindTM`/`exists_emitLoopTM` into `loopHostTM_decides`/`_finds`/
  `emitLoopTM_computes` (the base pair `exists_loopFindTM`↔`exists_loopTM`, 686 chars, moved with
  them), (b) short corollary boilerplate under 200 shared characters (zero-tape space rows,
  hypothesis passing in the loop corollaries, `computesFunInTime_pairDup`↔
  `computesFunInTime_pairEncode_diag`), and (c) two small intended mirrors introduced here:
  `branchTM_initCfg_false`↔`_true` (418 chars, left/right block) and `rewind_heads`↔
  `rewind_from_any` (155 chars, after the T1 factoring). No new copy of another file's
  material. Pairs involving each file (`per-file-pairs.txt`, base → final): Catalog 1,074 → 92,
  Primitives 713 → 283, Loop 292 → 115, Simulation 88 → 63, Wrappers 74 → 33, CodeSimulator
  70 → 70, Composition 52 → 26, TimeConstructible 52 → 12, Encoding 4 → 7 (the `pairDiagTM`
  corollary boilerplate), CertShell and WordSize 0 → 0.

## Rule-10 seal (fresh; `seal/`)
Each changed or new declaration is sealed in its own section (`tools/mkseal.py`) with
`attribute [local irreducible]` on 14 core definitions (`core-list.txt`: `MultiTapeTM.step`,
`runFrom`, `initCfg`, `Cfg.init`, `Action.apply`, `Cfg.inputSymbol`, `Cfg.workTapeSymbols`,
`moveInputPos`, `ComputesInTime`, `ComputesFunInTime`, `Computes`, `spaceUsed`, `spaceUsedByTape`,
`visitedByTapeHead`) plus, outside Simulation, five Simulation definitions
(`simulation-list-v3.txt`: `controlAction`, `leftAction`, `rightAction`, `emitAction`,
`bufferTape`), and `attribute [-simp]` on the `@[simp]` definitions `Action.apply`, `Cfg.init`,
`MultiTapeTM.initCfg`.
- **Pass (exit 0, 0 errors)**: Composition, Encoding, TimeConstructible, Simulation, Wrappers,
  Loop (15 declarations; 61 warnings = the base file's own multiset), Catalog (19 rows),
  CertShell (`cert_prepare_exists`), CodeSimulator (`canonPreserveInstall`).
- **Fail — Primitives** (42 declarations, 18 errors, all in verbatim-moved material:
  `fwdMap_move`, `_block`, `_suffix`, `_emit`, `_finish`, `_parse`, `_setup`, `_launch`,
  `fwdMapVirtual_step`/`_run`, `fwdMapSetup_*`, `poly_space`). Not complete.
- **Strict runs** adding the witness machines and `Cfg.ofWords` (`witness-list.txt`): Catalog fails
  exactly at the seven zero-work-tape/`C = 0` rows, which read a foreign witness's tape count
  `M.k = 0` definitionally (E2); CertShell and CodeSimulator fail at one `rfl : (Cfg.ofWords q w).state
  = some q` each (fixable with `Cfg.ofWords_state`; not fixed in this commit).
- **Unsealable / unsealed, inventoried**: `Cfg.Halted` (reducible abbrev); `branchTM`'s tape count
  and state type, read in *types* (`(branchTM M₁ M₂ b).k = M₁.k + M₂.k`); `leftCfg`, `rightCfg`
  (Simulation) and `captureCfg` (Wrappers) for other homes — no published field equations (E1).
- **Controls**: `seal/controls/ControlsUnsealed` 38 examples (pointwise + abstracted for each of
  the 19 sealed definitions) exit 0, 0 errors; `ControlsSealed` exit 1, exactly 38 errors.
  Multiplicity checker `tools/ctlcheck.py` (gate 16 R2-2): both PASS; its negative controls
  (duplicate diagnostic, missing diagnostic, zero exit) all FAIL as required.
- **Argument inspection** (`seal/argscan/*.txt`, every `simp`/`rw`/`unfold`/`show`/`change`
  argument resolved against the TCSlib definition index): foreign definitions passed explicitly
  are `leftCfg`/`rightCfg` (Composition 1, Wrappers 6, Loop 2), `captureCfg` (Loop 2), the
  abbrev `Cfg.Halted` (Loop 1), and, in Primitives' moved material, `MultiTapeTM.step`,
  `Action.apply`, `MultiTapeTM.initCfg`, `Cfg.init`.

## Assigned MIG-24 work — dispositions
| Kind | Disposition |
|---|---|
| T1 rewind family | Simulation: done (private `rewind_first_step` shared by `rewind_from_any`, `timed_rewind`, `rewind_heads`; public order frozen). Loop: done (`loop_rewind_bounded` retired → `timed_rewind`). Primitives: **not done** — `catalogRewind` is statement-identical to `timed_rewind` and should be retired the same way (4 call sites). |
| T2 mirrored emitter lemmas (Primitives/Loop) | **Not done.** In-file direction/variant parametrisation needs Lean iteration not completed; `emCall_first_entry` ↔ `emitter_first_entry` is cross-file and private on both sides — sharing needs a new public lemma (gap; no copy added). |
| T2b parser variants | Inspected. `mapParse_block`↔`mapParse_first` retired with the old captured-output mapper. `lenParse_first`↔`lenSuffix_run` and `emitterToken_double`↔`_separator` are different statements/transitions (not shared). `extract_replay`↔`rawStrip_replay` are the same replay on two machines — a private parametric replay lemma would serve both; **not done**. |
| T3 call-bank pair (Loop) | **Not done in this commit.** Prepared (12 frame-exactness side proofs → two private `emCall_pair_not_mem`/`emCall_triple_not_mem` lemmas) but not compiled before delivery. |
| T4 buffered-composition corollaries | Done (`exists_comp_partial`, `computesFunInTime_comp`, `exists_comp_on_image` derived). |
| T5 Catalog sweep rows | Partly resolved by the approved retirement of the six canonical rows (the canonical row bodies, the largest members, are gone). Remaining members (`copyMapTM`↔`transferMapTM`, the two endpoint lemmas, increment succ/overflow framed rows) are public, statement-frozen; a shared private helper was **not** built. |
| T6 pair-projection space rows | Done by re-pointing: each is now a four-line corollary of `pairExtractTM_fst`/`_snd`/`_concat` and `ComputesInTime.spaceUsed_le`. |
| T7 singletons (Loop, Encoding, Simulation) | Inspected: `loop_halted_run`↔`loop_run` differ in terminal and bound; `toCodeTM_computesInTime_iff`↔`exists_codeTM_spaceUsed` share only the relabeling scaffold; `bufferedSecondCfg_run`↔`VirtualInput.vhostEmitTM_runFrom` are cross-file lockstep hosts (needs a public lockstep interface). No change; no new debt. |

## Escalations (exact missing public statements; nothing was guessed or added)
- **E1** field equations for the block embeddings and the capture configuration:
  `Turing.FinTM.leftCfg_state : (leftCfg f c tapes heads).state = c.state.map f`,
  `leftCfg_inputPos`, `leftCfg_workTapes : … = Fin.addCases c.workTapes tapes`,
  `leftCfg_workTapePos : … = Fin.addCases c.workTapePos heads`, `leftCfg_output`, the five
  `rightCfg_*` analogues (with `Fin.addCases tapes c.workTapes` etc.), and
  `Turing.captureCfg_state/_inputPos/_workTapes/_workTapePos/_output` (Wrappers) — e.g. by
  `simps (config := { isSimp := false })`.
- **E2** tape-count equations for the zero-work-tape witnesses, e.g. `Turing.FinTM.idTM_k :
  idTM.k = 0`, `constTM_k`, `prependTM_k`, `pairValidTM_k`, `incFixedTM_k`, `Turing.pairDiagTM_k`,
  and `polyBitsTM_k_zero : (polyBitsTM 0 e).k = 0` — so the Catalog space rows need not read
  another file's definition by `rfl`.

## New / removed public names; imports
Added: `Turing.FinTM.pairMapSndTM`, `Turing.FinTM.pairMapSndTM_computes`,
`Turing.FinTM.pairMapSndTM_spaceUsed`. Removed: `Turing.transferTM_run`, `Turing.copyTM_run`,
`Turing.clearTM_run`, `Turing.compareTM_run`, `Turing.incrementTM_run_succ`,
`Turing.incrementTM_run_overflow`. Imports added: `Mathlib.Algebra.BigOperators.Fin`
(Simulation), `TCSlib.Complexity.TuringMachine.Build.Primitives` (Catalog). No others.

## Source citations used by the new proofs
Published API only: `computesInTime_iff`, `computesFunInTime_iff`, `computes_iff`,
`MultiTapeTM.step_of_some`, `runFrom_succ_eq_step(')`, `runFrom_add`, `runFrom_zero`,
`runFrom_of_halt`, `exists_first_halt`, `initCfg_eq`, `Cfg.init_*`, `Action.apply_*`,
`Cfg.inputSymbol_of_end`, `Cfg.workTapeSymbols_eq`, `Cfg.ofWords_*`, `spaceUsed_eq_sum`,
`spaceUsedByTape_eq_card`, `mem_visitedByTapeHead_iff`, `spaceUsedByTape_le_card_Icc`,
`spaceUsed_le_of_abs_le`, `workTapePos_runFrom_mem_Icc`, `ComputesInTime.spaceUsed_le`,
`timed_rewind`, `rewind_heads`, `controlAction_apply`, `VirtualTag_iff`, `tapeBlocks_*`, the
`_ofCfg` rows and `Cfg.ofWords_*_endpoint`; Mathlib `Fin.sum_univ_add`, `Fin.sum_univ_one`.
Historical gate-16 material (Loop overlay, Catalog part) was used as a route guide only.

## Original evidence vs fresh runs
Fresh on this host: everything under `evidence/` except what the packet supplied as data (gate-16
evidence, the maintainer's base screen — which our fresh base screen reproduces byte for byte).
No receipt is copied from the maintainer.

## NOT RUN / limits
- Open-PR name/shape search for `instDecidableEqFwdMapState` and the three exports: not run here
  (no fetch of other refs, per the brief); the packet's 104-ref search covers the three exports.
- The maintainer's current-campaign merged-tree replay (by design, the maintainer's).
