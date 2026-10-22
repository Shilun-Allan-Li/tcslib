# §13d G4 continuation 2 — final partial delivery

## Result and continuation boundary

**Phase 1 checkpoint 1 is complete:** `zr_rightPassContract` is one composed contract for the
entire positive-level right pass. The two frozen target rows remain open, each through its
original body only. There is no new admission, imported axiom, or new ground-rule escalation.
This is a partial delivery under the brief's continuation-budget provision, not a claim that
the extension or rebalance row has been filled.

| Checkpoint | Status |
|---|---|
| Phase 1.1: complete right pass for positive level | Complete, checked and committed |
| Phase 1.2: return-home contract | Open; no round contract or iteration claimed |
| Phase 1.3: left pass | Open; corrected displacement proved, machine not composed |
| Phase 1.4: zero-level finite-control branch | Open |
| Phase 1.5: ruler cleanup and home restoration | Open |
| Phase 1.6: exact endpoint/envelope assembly | Open |
| Phase 2: scan with both escapes | Open |
| Phase 2: guarded column moves, passes, home move, cleanup, assembly | Open |

Checkpoint archive: `fill-s13d-g4-cont2-cp1.zip`.
Final delivery archive: `fill-s13d-g4-cont2.zip` (same source commit, full final sweep).
No later checkpoint has been completed or claimed. No independent item is claimed blocked.
The return-home design was inspected, including the public `Cfg.workTapeSymbols_eq` and
`phaseHostTM_run`; neither reveals a missing API. No speculative return-loop source is shipped.

Base: `96d60278e4fde29b986ec1d0e59cd07f768fe28a`.
Final/checkpoint commit: `6fe3bf884ecbc0fd30a7f017665530e8a5dfdd7b`.
Branch: `fill/s13d-g4-cont2`.
The campaign branch was checked out first, at tip
`a2ed26945b173e18a36d2c56f57b8ced81723865`; the required ancestor test succeeded before
creating the fill branch exactly at the inputs commit. No rebase, merge, cherry-pick, push,
or PR was performed. Only the owned source is committed.

The attached brief's SHA-256 is
`3584091a9a29046cc71871c73bb4cf2395678a1bfa6a47ca32f86b72cd062a87`.
The attached addendum v2.3's SHA-256 is
`1ea7a37656f1fb76645673ae2dca68a00d12562b214f6dc36dac61a95dc13662`.
Both were verified. The campaign-tip repository brief matches the attachment after replacing
its `@ANCESTOR@` placeholder with the required base hash. The attachment's v2.3 overrides v2.

## Completed checklist

- [x] Preflight numbers and the addendum v2.3 procedure are recorded below.
- [x] Checkpoints, base, ancestor check, and checkpoint archives are identified above.
- [x] Every new/changed private is listed below; no private was removed; both status paragraphs
  are replaced by mathematical implementation-status text. No further leaf was introduced.
- [x] Left displacement option and the level-one sanity check are recorded below.
- [x] Scratch layout and adjusted-walk convention are recorded below.
- [x] Promotion candidates and escalations are recorded below.
- [x] External citations, expanded probe, seal list/result, rewrite arguments, and rule-11 grep
  are recorded below and in the bundled logs.
- [x] Both screens are bundled; every new in-file pair is justified below; new copies: none.
- [x] File size, verification tails, axiom checks, lint, and owned-region freeze are recorded.

These check marks attest that the reporting obligations are met; they do not mark the open
machine checkpoints as proved.

## Environment and resource compliance

Part 1 was run first, on the container's disk-backed overlay filesystem.

| Measurement | Initial preflight | Before cache |
|---|---:|---:|
| `nproc` | 9 | 9 |
| cgroup memory limit | 8,589,934,592 bytes | 8,589,934,592 bytes |
| anon used in headroom calculation | 135,479,296 bytes | 241,078,272 bytes |
| kernel used in headroom calculation | 18,190,336 bytes | 194,637,824 bytes |
| shmem | 0 | 0 |
| limit − (anon + kernel + shmem) | 8,436,264,960 bytes (7.856884 GiB) | 8,154,218,496 bytes (7.594208 GiB) |
| disk available | 31,966,261,248 bytes (29.770901 GiB) | 27,949,293,568 bytes (26.029808 GiB) |
| disk floor | 12 GiB | 8 GiB |
| memory headroom floor | 4 GiB | 4 GiB |
| OOM / OOM-kill counters | 0 / 0 | 0 / 0 |

The re-check's raw `memory.stat` and the final arithmetic are separate closely spaced samples;
the arithmetic uses the latter sample. Page cache was not counted as a shortage. No post-cache
disk-floor test or E-RES stop was imposed. Scratch, `/tmp`, and `/root` were checked as overlay;
all toolchain/cache/proof work stayed on that disk. Per-command timestamps, exit codes and
maximum RSS are in the logs. `/usr/bin/time` was unavailable, so a Python `os.wait4` wrapper
recorded the child process's `ru_maxrss`; it imposed no timeouts.

The 35 Mathlib roots were extracted from the order list's imports, then fetched once by:

```sh
TAR_OPTIONS=--no-same-owner lake exe cache get $(cat evidence/logs/mathlib-roots.txt)
```

967 cache files downloaded and unpacked successfully. No retry or cleaned retry was needed.
No unfiltered cache command and no `lake build` was run. Package pins and URLs matched the
manifest for every materialized package; the four inactive doc-generation packages were
not materialized. Empty dependency `.olean` scan: zero; narrowed-root probe: passed.

The unmodified official Lean 4.25.0 executable initially reported `failed to locate application`.
Part 2's authorized executable-path shim was compiled exactly as supplied. Its C source SHA-256
is `985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`.
`LD_PRELOAD` was scoped by shell wrappers to the Lean/Lake subprocesses only, alongside
`LEAN_SYSROOT` and `LAKE_HOME` pointing to the extracted official toolchain. No process outside
Lean/Lake inherited the preload. Neither Lean nor Lake nor any package source was patched.
The successful version is Lean 4.25.0, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
The exact subprocess environment was:

```text
LEAN_SYSROOT=/workspace/scratch/09494b8335b3/toolchain/lean-4.25.0-linux
LAKE_HOME=/workspace/scratch/09494b8335b3/toolchain/lean-4.25.0-linux
LD_PRELOAD=/workspace/scratch/09494b8335b3/evidence/runtime/executable-path.so
```

The compiled `.so` is not shipped. The exact shim source is included at
`evidence/runtime/executable-path.c`, as Part 2 requires, and reproduced in the appendix.

Mathlib roots:

```text
Mathlib.Algebra.BigOperators.Group.Finset.Basic
Mathlib.Algebra.Order.BigOperators.Group.Finset
Mathlib.Algebra.Order.Group.Abs
Mathlib.Algebra.Order.Group.Int
Mathlib.Computability.Language
Mathlib.Computability.TMToPartrec
Mathlib.Data.Finset.Dedup
Mathlib.Data.Finset.Max
Mathlib.Data.Fintype.Basic
Mathlib.Data.Fintype.EquivFin
Mathlib.Data.Fintype.Option
Mathlib.Data.Fintype.Pi
Mathlib.Data.Fintype.Prod
Mathlib.Data.Fintype.Sum
Mathlib.Data.Fintype.Vector
Mathlib.Data.Int.Interval
Mathlib.Data.List.FinRange
Mathlib.Data.List.Induction
Mathlib.Data.List.TakeDrop
Mathlib.Data.Nat.Bits
Mathlib.Data.Nat.Bitwise
Mathlib.Data.Nat.Digits.Defs
Mathlib.Data.Nat.Size
Mathlib.Data.Sigma.Basic
Mathlib.Data.Sign.Defs
Mathlib.Logic.Embedding.Basic
Mathlib.Logic.Equiv.Bool
Mathlib.Logic.Function.Basic
Mathlib.Order.Monotone.Basic
Mathlib.Order.Monotone.Defs
Mathlib.Tactic.DeriveFintype
Mathlib.Tactic.FinCases
Mathlib.Tactic.Linarith
Mathlib.Tactic.Ring
Mathlib.Tactic.SplitIfs
```

## Construction and remaining work

Write `ℓ = n + 1`, `m = zoneCapacity n = 2^ℓ`, `N = zoneStart ℓ`, and let `q` be the
entry scratch-head position. Tape 0 initially satisfies `zoneRowPre`; tape 1 is blank everywhere.
The ruler builder creates `m` copies of `.inl false` on scratch cells `[q,q+m)`, with blank
cells at `q−1` and `q+m`. The scratch head may start anywhere, including negative positions.
No counter tape, buffer column, or extra tape is introduced in this checkpoint.

The public rows are composed in precisely this order:

1. `seekEndTM` to `N` and `skipBackTM` to the last old right zone.
2. Constant mapped copy from that old zone onto scratch, then `skipTM` back to `N`.
3. Constant mapped copy from scratch to tape 0, storing virtual blanks on every track.
4. Advance the scratch head alone by one cell using the existing one-cell leaf, then
   `walkTM` on the ruler's tail. Tape 0 moves exactly `m`; scratch moves `m+1` in total.
5. `skipBackTM` rewinds scratch to `q`; the outer mapped copy writes empty slots on every track.

`zr_rightPass_pre` proves exactly the original positive-level `zoneRowPre`.
`zr_rightPass_time` proves the exact time `N + 10*m + 23`, including eight seam dispatches;
`zr_rightPass_time_le` proves the bound `32*(2^ℓ+1)`.
The contract retains the composed endpoint, cut, and head envelope supplied by the public
contracts. It does not assert the final extension's endpoint or `zoneRowLo`/`zoneRowHi` yet.
Scratch is intentionally left holding the ruler until cleanup. Its head has been restored;
tape 0's head is at the new outer half's beginning, `N+m`.

The left-route arithmetic is now the amended one: an unadjusted full-ruler walk moves
`m+1`, then an adjusted walk moves `m`. Starting at `2−zoneStart ℓ`, the result is
`1−zoneStart ℓ−zoneCapacity ℓ`. The checked level-one example gives `−8`, not `−7`.
Only the arithmetic is complete; neither left walk is claimed composed in this delivery.

For the next return-home contract, tape 0 first needs alignment beyond the new right zone
(for example by skipping the outer half). A backward-skip round can identify home by its
unique one-cell field and use `Round.iterate`/`round_iff`. Its anchor must be separate from
`skipBackTM`'s repeatedly visited run state. The second, leftward seek still needs the stated
local agreement precondition after the right write; the whole `zoneRowPre` is no longer true.
These are open proof obligations, not escalations or new API requests.

## Declaration inventory

34 new private declarations, one changed inherited private, none removed. The remaining
30 inherited privates are unchanged. Public declarations remain 18. No new machine leaf,
private iteration host, imported module, or public declaration was added.

| Declaration | Role |
|---|---|
| `zr_left_two_walks` | An unadjusted half-capacity walk followed by an adjusted one reaches the new left zone's outermost cell, including the separating blank. |
| `zr_RightData` | Positive-level data, indexed by the highest level already present. |
| `zr_rightFields` | The home followed by the existing right-zone words. |
| `zr_rightWord` | The final existing right zone, used to measure the next zone's half-capacity. |
| `zr_rightSeekContract` | Seeking the right end from a zoned input is a contract indexed by positive-level data. The segment constructor retains the seek row's exact time, endpoint, and envelope. |
| `zr_rightSeek_back_pre` | After seeking the right end, the last old zone satisfies the backward skip's premise. The zone-start recurrence identifies its two delimiters. |
| `zr_rightSeekBackContract` | The first two phases reach the last old right zone through one stationary seam. |
| `zr_rightSeekBack_post` | The seek-and-back composite preserves all tapes and leaves the zoned head at the old outermost zone's first cell. Its scratch head, input position, and output are unchanged. |
| `zr_rulerCopyContract` | Copying the old zone to scratch as a constant nonblank word makes the ruler. |
| `zr_rulerCopy_skip_pre` | The mapped ruler copy leaves its source word and both heads unchanged, so the source can immediately be skipped. |
| `zr_rulerSkipContract` | Copy the source zone to scratch as a ruler, then skip the source zone. The seam contributes one step beyond the two catalog rows. |
| `zr_rightSeekBack_ruler_pre` | The seek-and-back endpoint supplies the delimited old zone for the ruler copy. |
| `zr_rightRulerContract` | Seek the right end, return to the previous zone, copy its length to scratch, and skip back to the new zone's first cell. Every phase is a public row joined by stationary seams. |
| `zr_rightRuler_pre` | The ruler prefix requires exactly the original zoned input. |
| `zr_constantCopy_cell` | A constant mapped copy writes exactly its destination interval. This single formula covers the scratch ruler and both half-zone writes. |
| `zr_rightRuler_post` | The ruler prefix preserves the zoned tape, writes one constant ruler on scratch, and returns the zoned head to the new zone's first cell. |
| `zr_rulerStepContract` | Advance just the scratch head once along a nonempty rightward ruler. Restricting the existing leaf's verdict to its constant choice introduces no transition or new leaf. |
| `zr_rulerStep_walk_pre` | After the scratch-only advance, the tail of the ruler is the walk row's directed word. |
| `zr_adjustedWalkContract` | Advancing the ruler alone and walking its tail moves the zoned head by exactly the ruler length. The scratch head advances one cell farther, past the right delimiter. |
| `zr_adjustedWalk_post` | The adjusted walk preserves the tapes and has the two advertised head displacements. |
| `zr_adjustedWalk_back_pre` | The adjusted walk stops scratch exactly one blank beyond its ruler, ready for skip-back. |
| `zr_adjustedBackContract` | The adjusted walk followed by scratch rewind advances only the zoned head by one ruler length, restoring scratch to the beginning of its delimited word. |
| `zr_adjustedBack_post` | Rewinding scratch after the adjusted walk restores its head and keeps both tapes. Only the zoned head remains displaced, by the ruler length. |
| `zr_halfCopyContract` | A half-zone copy reads the scratch ruler and writes either stored virtual blanks or empty slots on every track of tape zero. |
| `zr_innerCopyContract` | The inner-half copy with a nonempty ruler, retaining the source word for the adjusted walk. Its fields and segment are those of the mapped-copy row. |
| `zr_innerCopy_adjusted_pre` | The inner copy preserves the nonempty scratch ruler needed by the adjusted walk. |
| `zr_adjustedBack_copy_pre` | After the adjusted walk and scratch rewind, the original ruler is ready for the outer-half mapped copy. |
| `zr_outerHalfContract` | Move from the inner to the outer half, rewind the ruler, and write the empty slots. |
| `zr_writeHalvesContract` | The two half-zone writes, separated by an adjusted walk and scratch rewind, as one contract. Scratch is preserved and its head is restored by the middle composite. |
| `zr_rulerWord` | The constant scratch word has the old zone's capacity, half that of the new zone. |
| `zr_rightRuler_write_pre` | The ruler prefix establishes the entire nonempty-word premise of the half-zone writer. |
| `zr_rightPassContract` | The complete right pass at positive level: build the ruler and write the new zone's inner and outer halves, using the adjusted walk and restoring the scratch head. |
| `zr_rightPass_pre` | The complete right pass has exactly the original zoned-input precondition. |
| `zr_rightPass_time` | The right pass's exact time includes all eight stationary seam transitions. It is the seek distance plus ten old-zone capacities and twenty-three control steps. |
| `zr_rightPass_time_le` | The right pass takes at most thirty-two times the new half-capacity plus one. |

The two public status paragraphs state the completed right-pass work and the still-open
machine phases without campaign labels, dates, record paths, or session narrative. Both
original target bodies and their literal `Proof sketch` text remain unchanged.

## Promotion candidates and escalations

- Existing one-cell leaf `zr_cellContract`: precondition `True`, time one, verdict from the
  scanned symbol, one optional write/move, and a head box between its two endpoints.
- Existing layout bridges `zr_zonedTape_right_fields` / `zr_zonedTape_left_fields` and
  `zr_fieldsTape_eq`: pointwise zoned/field-layout agreement. No new machine contract.
- `zr_rulerCopyContract` and `zr_rulerSkipContract`: delimited source word, constant mapped
  copy to scratch, optional source skip; no source change. `zr_rightRulerContract` adds the
  positive-level seeks and has the exact scratch interval formula `zr_rightRuler_post`.
- `zr_adjustedWalkContract` and `zr_adjustedBackContract`: nonempty delimited ruler, exact
  displacement by its length, and optional scratch-head restoration; both tapes preserved.
- `zr_writeHalvesContract`: one nonempty scratch ruler, two constant mapped copies separated
  by the adjusted-and-rewound walk. A possible generic constant-pair writer.
- The complete `zr_rightPassContract` is the private composed machine/contract candidate.
- Existing mirror `zr_mirror_tape`: pointwise negated-coordinate tape equality under
  `ZoneContents.swap`. No mirrored machine or duplicated directional implementation was added.

New escalations: **none**. The prior left-displacement issue is resolved arithmetically by the
brief's amended route. No host API or ground rule is claimed to block the remaining checkpoints.
No contiguous copy of the whole layout (the clock-writer hazard) was constructed.

## Rule 10 and public API audit

The seal copy wraps the private home in a temporary section and makes every reached non-type,
non-abbreviation TCSlib definition below locally irreducible, following the prior landing's
method. The frozen endpoint lemmas are outside that temporary section. The owned source
contains no such added section or attribute. Seal check: zero errors, only the two unchanged
target admissions. In particular, `Cfg.mapState` fields are read through their equations;
function equality uses `funext_iff` where needed. No foreign definition is an explicit
rewrite/simp/unfold argument.

Seal list:

```text
Turing.zoneCapacity
Turing.zoneStart
Turing.zonedTape
Turing.zoneCellAt
Turing.zoneCells
Turing.zoneOwner
Turing.zoneSlotOf
Turing.zoneShiftIndex
Turing.zoneRebalance
Turing.zoneShiftIn
Turing.zoneShiftOut
Turing.zoneCascadeRight
Turing.zoneStepPair
Turing.zoneMove
Turing.ZoneContents.words
Turing.ZoneContents.swap
Turing.ZoneContents.extend
Turing.fieldOffset
Turing.fieldsTape
Turing.joinFields
Turing.FinTM.bufferTape
Turing.tapeAction
Turing.inputMoveAction
Turing.moveInputPos
Turing.seekEndTM
Turing.seekStartTM
Turing.skipTM
Turing.skipBackTM
Turing.walkTM
Turing.copyMapTM
Turing.seekEndTM_contract
Turing.seekStartTM_contract
Turing.skipTM_contract
Turing.skipBackTM_contract
Turing.walkTM_contract
Turing.copyMapTM_contract
Turing.sweepContract
Turing.framedContract
Turing.seekPost
Turing.sweepPost
Turing.sweepMapWrite
Turing.Contract.ofSegment
Turing.Contract.seq
Turing.Segment
Turing.HeadBox
Turing.Cfg.mapState
Turing.Cfg.workTapeSymbols
Turing.seamCompTM
Turing.MultiTapeTM.step
Turing.MultiTapeTM.runFrom
Turing.Action.apply
```

The declaration citation inventory below is from the final changed source, resolved in Lean's
environment. It includes standard types/constructors and definitions occurring as terms;
definitions are used only via published equations. Own-file declarations are excluded.
Every citation is public at the base. The 338-name supplied probe was rerun, then a copy with
all additional named citations was checked. The exact expanded names and probe output are
included in the final verification log. No imports were added to the probe context.

```text
Bool type_or_constructor
Fin type_or_constructor
Function.update def
Function.update_of_ne theorem
Function.update_self theorem
List type_or_constructor
List.getElem?_eq_getElem theorem
List.getElem?_replicate theorem
List.length def
List.length_cons theorem
List.length_nil theorem
List.length_ofFn theorem
List.length_pos_iff_ne_nil theorem
List.length_replicate theorem
List.length_tail theorem
List.ofFn def
List.replicate def
List.tail def
Nat.cast_zero theorem
Nat.lt_succ_self theorem
Nat.sub_self theorem
Option type_or_constructor
Option.map_some theorem
Set.image_singleton theorem
Set.mem_singleton_iff theorem
SignType type_or_constructor
SignType.coe_one theorem
Sum.inl type_or_constructor
Sum.inr type_or_constructor
True type_or_constructor
Turing.Cfg type_or_constructor
Turing.Cfg.ext theorem
Turing.Cfg.mapState def
Turing.Cfg.mapState_inputPos theorem
Turing.Cfg.mapState_output theorem
Turing.Cfg.mapState_state theorem
Turing.Cfg.mapState_workTapePos theorem
Turing.Cfg.mapState_workTapes theorem
Turing.Contract type_or_constructor
Turing.Contract.exit_mem theorem
Turing.Contract.ofSegment def
Turing.Contract.ofSegment_post theorem
Turing.Contract.ofSegment_pre theorem
Turing.Contract.ofSegment_time theorem
Turing.Contract.segment theorem
Turing.Contract.seq def
Turing.Contract.seq_post theorem
Turing.Contract.seq_pre theorem
Turing.Contract.seq_time theorem
Turing.FinTM.bufferTape def
Turing.FinTM.bufferTape_eq theorem
Turing.FinTM.bufferTape_nat theorem
Turing.SeekPhase type_or_constructor
Turing.SeekPhase.done type_or_constructor
Turing.SeekPhase.run type_or_constructor
Turing.Segment.mono theorem
Turing.SweepPhase type_or_constructor
Turing.SweepPhase.sweep type_or_constructor
Turing.ZoneContents type_or_constructor
Turing.ZoneSym abbrev
Turing.copyMapTM_contract def
Turing.copyMapTM_contract_post theorem
Turing.copyMapTM_contract_post_workTapes theorem
Turing.copyMapTM_contract_pre theorem
Turing.copyMapTM_contract_time theorem
Turing.fieldOffset def
Turing.seamCompTM def
Turing.seekEndTM def
Turing.seekEndTM_contract def
Turing.seekEndTM_contract_post theorem
Turing.seekEndTM_contract_time theorem
Turing.seekPost def
Turing.seekPost_inputPos theorem
Turing.seekPost_output theorem
Turing.seekPost_state theorem
Turing.seekPost_workTapePos theorem
Turing.seekPost_workTapes theorem
Turing.skipBackTM def
Turing.skipBackTM_contract def
Turing.skipBackTM_contract_post theorem
Turing.skipBackTM_contract_pre theorem
Turing.skipBackTM_contract_time theorem
Turing.skipTM_contract def
Turing.skipTM_contract_post theorem
Turing.skipTM_contract_pre theorem
Turing.skipTM_contract_time theorem
Turing.sweepPost_inputPos theorem
Turing.sweepPost_output theorem
Turing.sweepPost_workTapePos theorem
Turing.sweepPost_workTapes theorem
Turing.walkTM def
Turing.walkTM_contract def
Turing.walkTM_contract_post theorem
Turing.walkTM_contract_pre theorem
Turing.walkTM_contract_time theorem
Turing.zoneCapacity def
Turing.zoneCapacity_eq theorem
Turing.zoneCells def
Turing.zoneCells_length theorem
Turing.zoneStart def
Turing.zoneStart_eq theorem
Turing.zoneStart_succ theorem
Turing.zonedTape_right_word theorem
add_zero theorem
congrArg theorem
false_and theorem
funext theorem
funext_iff theorem
if_false theorem
if_neg theorem
if_true theorem
le_rfl theorem
norm_num def
one_mul theorem
pow_succ theorem
trivial theorem
true_and theorem
zero_add theorem
```

Every explicit `rw`, `simp`, `simpa`, and `norm_num` argument list in the changed declarations
was inspected below. `unfold` and `delta` do not occur. Every unprefixed `zr_` name and
`zoneRowPre` is owned; every other resolved global rewrite argument is a published theorem.
Local hypotheses (`hp`, `hz`, `hj`, `hn`, `he`, `hpos`, etc.) and their projections are local
equalities, not foreign definitions. The `by decide` subterms establish only `0 ≠ 1` or `1 ≠ 0`
in `Fin 2`. The remaining `rfl` steps close constructor, record, or already-rewritten equalities;
the seal test guards against implicit TCSlib definitional closure.

| Source line | Complete argument-list inspection | Disposition |
|---:|---|---|
| 570 | `simp only [Nat.sub_self]` | Public equation lemmas and/or local equalities only. |
| 571 | `norm_num [zoneStart_eq]` | Public equation lemmas and/or local equalities only. |
| 572 | `rw [hz]` | Public equation lemmas and/or local equalities only. |
| 573 | `rw [zoneCapacity_eq]` | Public equation lemmas and/or local equalities only. |
| 671 | `simpa only [zr_rightSeekContract, Contract.ofSegment_pre]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 672 | `rw [skipBackTM_contract_pre]` | Public equation lemmas and/or local equalities only. |
| 674 | `simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, zr_rightSeekContract, Contract.ofSegment_post, seekEndTM_contract_post, seekPost_workTapes, seekPost_workTapePos, Function.update_self, zr_rightFields, zr_rightWord, List.length_cons, List.length_ofFn, zoneCells_length]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 678 | `rw [hz.1, hz.2.1, zero_add, zr_right_offset D.2 (D.1 + 1) le_rfl]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 682 | `rw [hpos]` | Public equation lemmas and/or local equalities only. |
| 693 | `simpa only [Set.image_singleton, Option.map_some]` | Public equation lemmas and/or local equalities only. |
| 695 | `simpa only [Set.image_singleton, Option.map_some]` | Public equation lemmas and/or local equalities only. |
| 708 | `simpa only [zr_rightSeekBackContract, Contract.ofSegment_pre, Contract.seq_pre, zr_rightSeekContract, Contract.ofSegment_pre, zoneRowPre, funext_iff, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 713 | `simp only [zr_rightSeekBackContract, Contract.ofSegment_post, Contract.seq_post, zr_rightSeekContract, seekEndTM_contract_post, skipBackTM_contract_post, zr_rightFields, zr_rightWord, List.length_cons, List.length_ofFn, zoneCells_length]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 717 | `simp only [Cfg.mapState_state, seekPost_state, Option.map_some]` | Public equation lemmas and/or local equalities only. |
| 718 | `simp only [Cfg.mapState_inputPos, seekPost_inputPos]` | Public equation lemmas and/or local equalities only. |
| 720 | `simp only [Cfg.mapState_workTapes, seekPost_workTapes]` | Public equation lemmas and/or local equalities only. |
| 722 | `simp only [Cfg.mapState_workTapePos, seekPost_workTapePos, Function.update_self]` | Public equation lemmas and/or local equalities only. |
| 725 | `simp only [Function.update_self, hz.2.1, zero_add, zr_right_offset D.2 (D.1 + 1) le_rfl]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 728 | `simp only [Function.update_of_ne hj, Cfg.mapState_workTapePos, seekPost_workTapePos]` | Public equation lemmas and/or local equalities only. |
| 729 | `simp only [Cfg.mapState_output, seekPost_output]` | Public equation lemmas and/or local equalities only. |
| 743 | `rw [zr_rulerCopyContract, copyMapTM_contract_pre]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 744 | `rw [skipTM_contract_pre]` | Public equation lemmas and/or local equalities only. |
| 746 | `simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, zr_rulerCopyContract, copyMapTM_contract_post, sweepPost_workTapePos]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 748 | `simp only [sweepPost_workTapes, show (0 : Fin 2) ≠ 1 by decide, false_and, if_false]` | Public equation lemmas and/or local equalities only. |
| 765 | `simpa only [zr_rightSeekBackContract, Contract.ofSegment_pre, Contract.seq_pre, zr_rightSeekContract, zoneRowPre, funext_iff, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 768 | `rw [zr_rulerSkipContract, Contract.seq_pre, zr_rulerCopyContract, copyMapTM_contract_pre]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 771 | `simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, zr_rightSeekBack_post D d hp, seekPost_workTapes, seekPost_workTapePos, Function.update_self, hz.1]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 775 | `simpa only [zr_rightWord, zoneCells_length]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 785 | `simpa only [Set.image_singleton, Option.map_some]` | Public equation lemmas and/or local equalities only. |
| 787 | `simpa only [Set.image_singleton, Option.map_some]` | Public equation lemmas and/or local equalities only. |
| 792 | `simp only [zr_rightRulerContract, Contract.ofSegment_pre, Contract.seq_pre, zr_rightSeekBackContract, zr_rightSeekContract, zoneRowPre, funext_iff, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 805 | `rw [copyMapTM_contract_post_workTapes]` | Public equation lemmas and/or local equalities only. |
| 810 | `simp only [hn, FinTM.bufferTape_nat, List.getElem?_eq_getElem hnlt, Option.map_some]` | Public equation lemmas and/or local equalities only. |
| 830 | `simpa only [zr_rightRulerContract, Contract.ofSegment_pre, Contract.seq_pre]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 831 | `rw [zr_rightRulerContract, Contract.ofSegment_post, Contract.seq_post, zr_rightSeekBack_post D _ hp0, zr_rulerSkipContract, Contract.seq_post, skipTM_contract_post]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 836 | `simp only [Cfg.mapState_state, seekPost_state, Option.map_some]` | Public equation lemmas and/or local equalities only. |
| 837 | `simp only [Cfg.mapState_inputPos, seekPost_inputPos, zr_rulerCopyContract, copyMapTM_contract_post, sweepPost_inputPos]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 840 | `simp only [Cfg.mapState_workTapes, seekPost_workTapes, zr_rulerCopyContract, zr_constantCopy_cell, Cfg.mapState_workTapePos, seekPost_workTapePos, zr_rightWord, zoneCells_length]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 845 | `simp only [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), Cfg.mapState_workTapePos]` | Public equation lemmas and/or local equalities only. |
| 847 | `simp only [hj, false_and, if_false]` | Public equation lemmas and/or local equalities only. |
| 849 | `simp only [Cfg.mapState_workTapePos, seekPost_workTapePos, zr_rulerCopyContract, copyMapTM_contract_post, sweepPost_workTapePos, zr_rightWord, zoneCells_length, Function.update_self]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 854 | `simp only [Function.update_self]` | Public equation lemmas and/or local equalities only. |
| 856 | `simp only [Function.update_of_ne hj, Cfg.mapState_workTapePos, seekPost_workTapePos, sweepPost_workTapePos]` | Public equation lemmas and/or local equalities only. |
| 858 | `simp only [Cfg.mapState_output, seekPost_output, zr_rulerCopyContract, copyMapTM_contract_post, sweepPost_output]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 885 | `rw [zr_rulerStepContract, Contract.ofSegment_pre]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 886 | `rw [walkTM_contract_pre]` | Public equation lemmas and/or local equalities only. |
| 892 | `simpa only [SignType.coe_one, one_mul]` | Public equation lemmas and/or local equalities only. |
| 894 | `simpa only [zr_rulerStepContract, Contract.ofSegment_post, zr_cellContract, zr_cellPost, Cfg.mapState_workTapes, Cfg.mapState_workTapePos, Function.update_self, FinTM.bufferTape_nat, SignType.coe_one, one_mul]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 909 | `simpa only [Set.image_singleton, Option.map_some]` | Public equation lemmas and/or local equalities only. |
| 911 | `simpa only [Set.image_singleton, Option.map_some]` | Public equation lemmas and/or local equalities only. |
| 926 | `rw [zr_adjustedWalkContract, Contract.ofSegment_pre, Contract.seq_pre, zr_rulerStepContract, Contract.ofSegment_pre]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 931 | `rw [List.length_tail]` | Public equation lemmas and/or local equalities only. |
| 933 | `simp only [zr_adjustedWalkContract, Contract.ofSegment_post, Contract.seq_post, zr_rulerStepContract, walkTM_contract_post, zr_cellContract, zr_cellPost]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 936 | `simp only [Cfg.mapState_state, Option.map_some]` | Public equation lemmas and/or local equalities only. |
| 937 | `simp only [Cfg.mapState_inputPos]` | Public equation lemmas and/or local equalities only. |
| 939 | `simp only [Cfg.mapState_workTapes]` | Public equation lemmas and/or local equalities only. |
| 941 | `simp only [Cfg.mapState_workTapePos, SignType.coe_one, one_mul, if_true]` | Public equation lemmas and/or local equalities only. |
| 944 | `simp only [Function.update_self, if_true]` | Public equation lemmas and/or local equalities only. |
| 946 | `simp only [Function.update_of_ne hj, Cfg.mapState_workTapePos, if_neg hj]` | Public equation lemmas and/or local equalities only. |
| 948 | `simp only [Cfg.mapState_output]` | Public equation lemmas and/or local equalities only. |
| 957 | `rw [zr_adjustedWalkContract, Contract.ofSegment_pre, Contract.seq_pre, zr_rulerStepContract, Contract.ofSegment_pre]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 959 | `rw [skipBackTM_contract_pre]` | Public equation lemmas and/or local equalities only. |
| 961 | `simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, zr_adjustedWalk_post w d hp, if_true]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 965 | `rw [he]` | Public equation lemmas and/or local equalities only. |
| 966 | `simpa only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]` | Public equation lemmas and/or local equalities only. |
| 976 | `simpa only [Set.image_singleton, Option.map_some]` | Public equation lemmas and/or local equalities only. |
| 978 | `simpa only [Set.image_singleton, Option.map_some]` | Public equation lemmas and/or local equalities only. |
| 991 | `simpa only [zr_adjustedBackContract, Contract.ofSegment_pre, Contract.seq_pre]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 992 | `rw [zr_adjustedBackContract, Contract.ofSegment_post, Contract.seq_post, zr_adjustedWalk_post w _ hp0, skipBackTM_contract_post]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 995 | `simp only [Cfg.mapState_state, seekPost_state, Option.map_some]` | Public equation lemmas and/or local equalities only. |
| 996 | `simp only [Cfg.mapState_inputPos, seekPost_inputPos]` | Public equation lemmas and/or local equalities only. |
| 998 | `simp only [Cfg.mapState_workTapes, seekPost_workTapes]` | Public equation lemmas and/or local equalities only. |
| 1002 | `simp only [Cfg.mapState_workTapePos, seekPost_workTapePos, Function.update_self, show (1 : Fin 2) ≠ 0 by decide, if_false, if_true, Nat.cast_zero, add_zero]` | Public equation lemmas and/or local equalities only. |
| 1007 | `simp only [Cfg.mapState_workTapePos, seekPost_workTapePos, Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1), show (0 : Fin 2) ≠ 1 by decide, if_false, if_true, add_zero]` | Public equation lemmas and/or local equalities only. |
| 1010 | `simp only [Cfg.mapState_output, seekPost_output]` | Public equation lemmas and/or local equalities only. |
| 1033 | `rw [zr_innerCopyContract, Contract.ofSegment_pre, zr_halfCopyContract, copyMapTM_contract_pre]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 1035 | `rw [zr_adjustedBackContract, Contract.ofSegment_pre, Contract.seq_pre, zr_adjustedWalkContract, Contract.ofSegment_pre, Contract.seq_pre, zr_rulerStepContract, Contract.ofSegment_pre]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 1040 | `simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, zr_innerCopyContract, Contract.ofSegment_post, zr_halfCopyContract, copyMapTM_contract_post, sweepPost_workTapePos, sweepPost_workTapes, show (1 : Fin 2) ≠ 0 by decide, false_and, if_false]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 1055 | `rw [zr_adjustedBackContract, Contract.ofSegment_pre, Contract.seq_pre, zr_adjustedWalkContract, Contract.ofSegment_pre, Contract.seq_pre, zr_rulerStepContract, Contract.ofSegment_pre]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 1058 | `rw [zr_halfCopyContract, copyMapTM_contract_pre]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 1060 | `simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, zr_adjustedBack_post w d hp, show (1 : Fin 2) ≠ 0 by decide, if_false, Nat.cast_zero, add_zero]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 1063 | `simpa only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos]` | Public equation lemmas and/or local equalities only. |
| 1075 | `simpa only [zr_outerHalfContract, Contract.seq_pre, zr_adjustedBackContract, Contract.ofSegment_pre, zr_adjustedWalkContract, zr_rulerStepContract, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 1094 | `rw [zr_writeHalvesContract, Contract.seq_pre, zr_innerCopyContract, Contract.ofSegment_pre, zr_halfCopyContract, copyMapTM_contract_pre]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 1100 | `simp only [zr_rulerWord, List.length_replicate, List.length_nil]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 1103 | `simp only [Cfg.mapState_workTapes, Cfg.mapState_workTapePos, zr_rightRuler_post D d hp, Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), zr_rulerWord, hz.2.2, true_and, FinTM.bufferTape_eq, List.getElem?_replicate]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 1118 | `rw [zr_rightPassContract, Contract.seq_pre, zr_rightRuler_pre]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 1119 | `simp only [zoneRowPre, funext_iff, Cfg.mapState_workTapes, Cfg.mapState_workTapePos]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 1126 | `simp only [zr_rightPassContract, Contract.seq_time, zr_rightRulerContract, Contract.ofSegment_time, zr_rightSeekBackContract, zr_rightSeekContract, seekEndTM_contract_time, skipBackTM_contract_time, zr_rulerSkipContract, zr_rulerCopyContract, copyMapTM_contract_time, skipTM_contract_time, zr_writeHalvesContract, zr_innerCopyContract, zr_halfCopyContract, zr_outerHalfContract, zr_adjustedBackContract, zr_adjustedWalkContract, zr_rulerStepContract, zr_cellContract, walkTM_contract_time, zr_rightFields, zr_rightWord, zr_rulerWord, List.length_cons, List.length_ofFn, List.length_replicate, List.length_tail, zoneCells_length, zr_right_offset D.2 (D.1 + 1) le_rfl]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |
| 1142 | `rw [zr_rightPass_time, zoneCapacity_eq, pow_succ]` | Owned definitions/lemmas, public equation lemmas, and local equalities only. |

Rule 11 grep of the added diff for `copyTM_run`, `transferTM_run`, `clearTM_run`,
`compareTM_run`, `incrementTM_run_succ`, and `incrementTM_run_overflow`: **zero hits**.
No private `Build/Catalog` declaration is cited. All new private names begin `zr_`.

## Duplication ledger

Screens ran sequentially, one at a time, under `nice -n 10`, using the prescribed ten-file
population and the declaration-keyed v3 script. Full outputs are bundled.

Before:

```text
declarations screened: 808; copy pairs (target reproduces >= half of source): 439; reproduced text: 127,994 chars
```

After:

```text
declarations screened: 838; copy pairs (target reproduces >= half of source): 478; reproduced text: 137,237 chars
```

No new cross-file pair involving the owned file. The initial screen exposed a rounded 90%
pair between the right-pass precondition and its ruler-link proof; that shared proof was
factored into `zr_rightRuler_pre`, and the screen rerun. The final new pairs are all below 90%.
The existing accepted `zr_pair_pass` / `zr_inPass_out` pair is unchanged.
**new copies: none**.

Each new in-file pair below compares distinct row endpoints or preconditions. The remaining
shared text consists of explicit public getter/equation applications or short contract
constructor adapters; no row trace, seam proof, loop host, or pure cascade proof is copied.

| New directed pair | One-line justification |
|---|---|
| `ZoneRebalance.lean::zr_rightRulerContract  reproduces  ZoneRebalance.lean::zr_rightSeekBackContract: 252/311 = 81%` | Distinct row compositions; shared singleton-exit normalization or constant mapped-copy interface. |
| `ZoneRebalance.lean::zr_halfCopyContract  reproduces  ZoneRebalance.lean::zr_rulerCopyContract: 66/82 = 80%` | Distinct row compositions; shared singleton-exit normalization or constant mapped-copy interface. |
| `ZoneRebalance.lean::zr_rightSeekBack_ruler_pre  reproduces  ZoneRebalance.lean::zr_rightRuler_pre: 140/189 = 74%` | Different link/precondition obligations; shared public word-preservation and configuration-field equations. |
| `ZoneRebalance.lean::zr_innerCopy_adjusted_pre  reproduces  ZoneRebalance.lean::zr_rulerCopy_skip_pre: 221/303 = 73%` | Different link/precondition obligations; shared public word-preservation and configuration-field equations. |
| `ZoneRebalance.lean::zr_rightSeekBack_ruler_pre  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 100/140 = 71%` | Different link/precondition obligations; shared public word-preservation and configuration-field equations. |
| `ZoneRebalance.lean::zr_adjustedBack_copy_pre  reproduces  ZoneRebalance.lean::zr_adjustedWalk_back_pre: 294/418 = 70%` | Different link/precondition obligations; shared public word-preservation and configuration-field equations. |
| `ZoneRebalance.lean::zr_rightSeekBack_post  reproduces  ZoneRebalance.lean::zr_rightRuler_pre: 132/189 = 70%` | Distinct endpoint equations; shared public configuration getters, with different displacements/footprints. |
| `ZoneRebalance.lean::zr_rightSeekBackContract  reproduces  ZoneRebalance.lean::zr_rightRulerContract: 252/367 = 69%` | Distinct row compositions; shared singleton-exit normalization or constant mapped-copy interface. |
| `ZoneRebalance.lean::zr_rightSeekBack_post  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 96/140 = 69%` | Distinct endpoint equations; shared public configuration getters, with different displacements/footprints. |
| `ZoneRebalance.lean::zr_rightRuler_pre  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 96/140 = 69%` | Different link/precondition obligations; shared public word-preservation and configuration-field equations. |
| `ZoneRebalance.lean::zr_adjustedBackContract  reproduces  ZoneRebalance.lean::zr_adjustedWalkContract: 216/329 = 66%` | Distinct row compositions; shared singleton-exit normalization or constant mapped-copy interface. |
| `ZoneRebalance.lean::zr_adjustedBackContract  reproduces  ZoneRebalance.lean::zr_rightSeekBackContract: 203/311 = 65%` | Distinct row compositions; shared singleton-exit normalization or constant mapped-copy interface. |
| `ZoneRebalance.lean::zr_innerCopy_adjusted_pre  reproduces  ZoneRebalance.lean::zr_adjustedBack_copy_pre: 297/467 = 64%` | Different link/precondition obligations; shared public word-preservation and configuration-field equations. |
| `ZoneRebalance.lean::zr_adjustedWalk_back_pre  reproduces  ZoneRebalance.lean::zr_adjustedBack_copy_pre: 294/467 = 63%` | Different link/precondition obligations; shared public word-preservation and configuration-field equations. |
| `ZoneRebalance.lean::zr_rightRuler_post  reproduces  ZoneRebalance.lean::zr_rightSeekBack_post: 609/977 = 62%` | Distinct endpoint equations; shared public configuration getters, with different displacements/footprints. |
| `ZoneRebalance.lean::zr_rightSeekBack_post  reproduces  ZoneRebalance.lean::zr_rightSeek_back_pre: 402/646 = 62%` | Distinct endpoint equations; shared public configuration getters, with different displacements/footprints. |
| `ZoneRebalance.lean::zr_adjustedWalkContract  reproduces  ZoneRebalance.lean::zr_adjustedBackContract: 216/352 = 61%` | Distinct row compositions; shared singleton-exit normalization or constant mapped-copy interface. |
| `ZoneRebalance.lean::zr_adjustedWalkContract  reproduces  ZoneRebalance.lean::zr_rightSeekBackContract: 190/311 = 61%` | Distinct row compositions; shared singleton-exit normalization or constant mapped-copy interface. |
| `ZoneRebalance.lean::zr_rightRulerContract  reproduces  ZoneRebalance.lean::zr_adjustedBackContract: 214/352 = 61%` | Distinct row compositions; shared singleton-exit normalization or constant mapped-copy interface. |
| `ZoneRebalance.lean::zr_rulerCopyContract  reproduces  ZoneRebalance.lean::zr_halfCopyContract: 66/110 = 60%` | Distinct row compositions; shared singleton-exit normalization or constant mapped-copy interface. |
| `ZoneRebalance.lean::zr_adjustedBackContract  reproduces  ZoneRebalance.lean::zr_rightRulerContract: 214/367 = 58%` | Distinct row compositions; shared singleton-exit normalization or constant mapped-copy interface. |
| `ZoneRebalance.lean::zr_rightSeekBack_post  reproduces  ZoneRebalance.lean::zr_adjustedBack_post: 493/850 = 58%` | Distinct endpoint equations; shared public configuration getters, with different displacements/footprints. |
| `ZoneRebalance.lean::zr_rightSeekBack_post  reproduces  ZoneRebalance.lean::zr_adjustedWalk_post: 445/769 = 58%` | Distinct endpoint equations; shared public configuration getters, with different displacements/footprints. |
| `ZoneRebalance.lean::zr_rightSeekBackContract  reproduces  ZoneRebalance.lean::zr_adjustedWalkContract: 190/329 = 58%` | Distinct row compositions; shared singleton-exit normalization or constant mapped-copy interface. |
| `ZoneRebalance.lean::zr_rightSeekBackContract  reproduces  ZoneRebalance.lean::zr_adjustedBackContract: 203/352 = 58%` | Distinct row compositions; shared singleton-exit normalization or constant mapped-copy interface. |
| `ZoneRebalance.lean::zr_rightRuler_post  reproduces  ZoneRebalance.lean::zr_adjustedBack_post: 478/850 = 56%` | Distinct endpoint equations; shared public configuration getters, with different displacements/footprints. |
| `ZoneRebalance.lean::zr_rightRuler_write_pre  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 77/140 = 55%` | Different link/precondition obligations; shared public word-preservation and configuration-field equations. |
| `ZoneRebalance.lean::zr_rightSeekBack_post  reproduces  ZoneRebalance.lean::zr_rightSeekBack_ruler_pre: 308/569 = 54%` | Distinct endpoint equations; shared public configuration getters, with different displacements/footprints. |
| `ZoneRebalance.lean::zr_rightRuler_post  reproduces  ZoneRebalance.lean::zr_adjustedWalk_post: 416/769 = 54%` | Distinct endpoint equations; shared public configuration getters, with different displacements/footprints. |
| `ZoneRebalance.lean::zr_rightSeek_back_pre  reproduces  ZoneRebalance.lean::zr_rightSeekBack_ruler_pre: 306/569 = 54%` | Different link/precondition obligations; shared public word-preservation and configuration-field equations. |
| `ZoneRebalance.lean::zr_adjustedBack_copy_pre  reproduces  ZoneRebalance.lean::zr_innerCopy_adjusted_pre: 297/554 = 54%` | Different link/precondition obligations; shared public word-preservation and configuration-field equations. |
| `ZoneRebalance.lean::zr_adjustedWalk_back_pre  reproduces  ZoneRebalance.lean::zr_rightRuler_pre: 101/189 = 53%` | Different link/precondition obligations; shared public word-preservation and configuration-field equations. |
| `ZoneRebalance.lean::zr_adjustedBack_copy_pre  reproduces  ZoneRebalance.lean::zr_rightRuler_pre: 101/189 = 53%` | Different link/precondition obligations; shared public word-preservation and configuration-field equations. |
| `ZoneRebalance.lean::zr_rightSeekBack_ruler_pre  reproduces  ZoneRebalance.lean::zr_adjustedBack_copy_pre: 249/467 = 53%` | Different link/precondition obligations; shared public word-preservation and configuration-field equations. |
| `ZoneRebalance.lean::zr_innerCopy_adjusted_pre  reproduces  ZoneRebalance.lean::zr_rightRuler_pre: 100/189 = 53%` | Different link/precondition obligations; shared public word-preservation and configuration-field equations. |
| `ZoneRebalance.lean::zr_rightRulerContract  reproduces  ZoneRebalance.lean::zr_adjustedWalkContract: 168/329 = 51%` | Distinct row compositions; shared singleton-exit normalization or constant mapped-copy interface. |
| `ZoneRebalance.lean::zr_rightPass_pre  reproduces  ZoneRebalance.lean::zr_rightRuler_pre: 96/189 = 51%` | Different link/precondition obligations; shared public word-preservation and configuration-field equations. |
| `ZoneRebalance.lean::zr_adjustedBack_post  reproduces  ZoneRebalance.lean::zr_rightSeekBack_post: 493/977 = 50%` | Distinct endpoint equations; shared public configuration getters, with different displacements/footprints. |
| `ZoneRebalance.lean::zr_rightRuler_post  reproduces  ZoneRebalance.lean::zr_rulerCopy_skip_pre: 152/303 = 50%` | Distinct endpoint equations; shared public configuration getters, with different displacements/footprints. |

## Verification and scope

All Lean checks used `scripts/lean_check_tree.sh`, including the scratch probes. No direct
build or alternate proof checker was used. Bootstrap: all 81 modules, zero errors.
The bootstrap ran the 22-module owned-file dependency closure first, then the remaining
59 modules. Each sublist preserves the supplied relative order; their concatenation is not
the original 81-module order. This scheduling deviation is recorded explicitly. Every module
was checked once during bootstrap; the final sweep then checked all 81 in the exact supplied
order. The bundled bootstrap log concatenates the two bootstrap runs.

Final sweep: all 81 modules in the supplied order, zero errors; 35 admission warnings in the
original 15 modules, unchanged by name. The 33 out-of-scope admissions are untouched.

All 65 private declarations were axiom-printed (including every new/changed private): only
`propext`, `Classical.choice`, and `Quot.sound`, or subsets. Both targets retain `sorryAx`.
The admission walk reaches each target's own original body only. No new helper has an admission.

The base admission set, by name:

```text
TuringMachine/Simulation: 1: branchTM_spaceUsed
TuringMachine/Encoding: 1: pairDiagTM_computes
ClassP/TimeConstructible: 2: _root_.Turing.FinTM.lengthBitsTM_computes, _root_.Turing.FinTM.lengthBitsTM_spaceUsed
TuringMachine/Composition: 3: idTM_computes, ifEqTM_computes, condTM_computes_iff
TuringMachine/Build/Wrappers: 2: timedCondTM_computes, timedCondTM_spaceUsed
TuringMachine/Build/Loop: 5: loopHostTM_contracts, loopHostTM_decides, loopHostTM_finds, loopHostTM_spaceUsed_le_budget, emitLoopTM_computes
TuringMachine/Build/Primitives: 3: polyUnaryTM_spaceUsed, unaryTokenTM_computes, appendBitTM_computes
TuringMachine/Build/InputDevice: 3: exists_rulerTestTM, exists_rulerDeviceTM, exists_rulerHostTM
TuringMachine/Build/InputWindow: 1: exists_inputWindowCopyTM
TuringMachine/Build/RecordTable: 4: exists_tableFindTM, exists_tableAppendTM, exists_recordValidTM, exists_recordNextTM
TuringMachine/Build/SeamLayout: 1: exists_seamLayoutTM
TuringMachine/Build/ZoneRebalance: 2: exists_zoneRebalanceTM, exists_zoneExtendTM
TuringMachine/CodeSimulator: 2: exists_canonGrammarStage [private], exists_uniformSimulator
TuringMachine/NDCodeSimulator: 2: exists_replayCanonizer, exists_ndInterpreterCore
TuringMachine/UniversalK: 3: exists_selfStartupTMK, exists_selfUniversalK, universalK
TOTAL 35
```

Freeze and hygiene:

```text
Freeze and source hygiene: PASS
Only tracked change: TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean
Prefix before private home byte-identical; endpoint suffix byte-identical.
Both target statements and sorry bodies byte-identical; status paragraphs changed as authorized.
Imports unchanged: four.
Public declarations: 18 (base 18); private: 65 (base 31).
New private declarations: 34; changed inherited private: zr_left_two_walks; removed: none.
Source lines: 1365; maximum width: 99.
Admissions: exactly two original targets, both with literal Proof sketch.
Six prohibited R3 rows in diff: zero hits.
New private names outside zr_: none; no added leaf or private host.
Rewrite-list inspection entries: 90.
Full frozen-region normalization: PASS; only private home and two status paragraphs differ.
```

Lint:

```text
style_lint: 0 FAIL, 31 WARN over 38 files
```

The one new warning is `ZoneRebalance.lean` exceeding 1,000 lines (base lint: 30 WARN).
Ground rule 8 explicitly imposes no size cap; ownership forbids moving this private home to
another module, and imports are frozen. No new declaration warning or line over 100 characters.

Verification tail:

```text

Hint: Omit it from the simp argument list.
  simp_all ̵[̵V̵i̵r̵t̵u̵a̵l̵T̵a̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
END TCSlib/Complexity/TuringMachine/Universal 2026-10-22T01:27:31.395837+00:00 status=0 elapsed=13.439s maximum_rss=2202724 KiB
START TCSlib/Complexity/TuringMachine 2026-10-22T01:27:31.395910+00:00
END TCSlib/Complexity/TuringMachine 2026-10-22T01:27:32.699842+00:00 status=0 elapsed=1.304s maximum_rss=2059144 KiB
```

The format-patch series reconstructs the committed source from the base, and the bundle has
exactly the base as its prerequisite. `SHA256SUMS` covers every archive member except itself.
No compiled library, cache, toolchain binary, or runtime `.so` is included.

## Appendix: exact authorized Part 2 shim source

```c
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <limits.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/auxv.h>
#include <unistd.h>
/* Supply the executable's actual path from ELF startup metadata when procfs
   cannot resolve it. No filesystem, network, or proof-checking rules change. */
ssize_t readlink(const char *path, char *buf, size_t cap) {
  static ssize_t (*real_readlink)(const char *, char *, size_t);
  if (!real_readlink) real_readlink = dlsym(RTLD_NEXT, "readlink");
  ssize_t n = real_readlink(path, buf, cap);
  char own[64];
  snprintf(own, sizeof own, "/proc/%ld/exe", (long)getpid());
  if (n >= 0 || (strcmp(path, "/proc/self/exe") && strcmp(path, own))) return n;
  const char *exe = (const char *)getauxval(AT_EXECFN);
  char absolute[PATH_MAX];
  if (!exe || !realpath(exe, absolute)) return n;
  size_t len = strlen(absolute);
  if (len > cap) len = cap;
  memcpy(buf, absolute, len);
  return (ssize_t)len;
}
```

## Archive integrity verification

```text
/workspace/scratch/09494b8335b3/packages/final/fill-s13d-g4-cont2.bundle is okay
The bundle contains this ref:
6fe3bf884ecbc0fd30a7f017665530e8a5dfdd7b refs/heads/fill/s13d-g4-cont2
The bundle requires this ref:
96d60278e4fde29b986ec1d0e59cd07f768fe28a 
The bundle uses this hash algorithm: sha1
Patch reconstruction: PASS, tree ca72bca6e0d7c2a274b5f390f33ca4f0e697b2d9
Source equals committed blob: PASS
Sole changed path: TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean
Sole parent/prerequisite: 96d60278e4fde29b986ec1d0e59cd07f768fe28a
```
