# Fill report: §13d G4, continuation 4 — the zone extension and rebalance rows (final)

**Complete delivery (`fill-s13d-g4-cont4.zip`).** Both targets are proved and free of `sorryAx`.
Each depends on exactly `[propext, Classical.choice, Quot.sound]`:

- **`Turing.exists_zoneExtendTM`**, with `C = 135` (zip 3; unchanged since);
- **`Turing.exists_zoneRebalanceTM`**, with `C = 2300`, in both directions (zip 7).

The owned module has no sorry and no warning. The 96-module sweep has **25 sorry warnings**,
which is the base's 27 minus the two targets. This zip is as of **`374337b0`**, the same commit
as checkpoint zip 7, and it supersedes every earlier zip, including the earlier final zip (as of
`f771d4ff`).

**Zips written** (each has its own `REPORT.md`, source, format-patch, bundle, logs, screens and
`SHA256SUMS`):

| zip | checkpoint | commit | SHA-256 |
|---|---|---|---|
| `fill-s13d-g4-cont4-cp1.zip` | 1.2 (the return home) | `b5247d00` | `596954622b0a9f43d7ae2e78b4ca5edbeb1ba8f4900c8ef237347e442ee5a514` |
| `fill-s13d-g4-cont4-cp2.zip` | 1.3 (the left pass) | `478124e9` | `5df91a81b3397d0b93f00fab2162b3d1fe345ecdb0b652ebcf5ddc3c1ca26b95` |
| `fill-s13d-g4-cont4-cp3.zip` | 1.5–1.6 (`exists_zoneExtendTM`) | `7fbf3c2e` | `2661cc2a3d8dd41cb9191ec8c582c395a5a1228f9a31f4e4d8defde24addc0b4` |
| `fill-s13d-g4-cont4-cp4.zip` | 2.1 (the scan with `short`, rightward) | `604d9404` | `abd8df6e80e0d2a8c86465e9455167869960f1a8d5307a3528ea609caf38fc78` |
| `fill-s13d-g4-cont4-cp5.zip` | 2.2 (one level's column moves, rightward) | `f771d4ff` | `5bbfe470da93524afc09663d4d4eee7370aa63469e013c4e77a45f0db7812843` |
| `fill-s13d-g4-cont4-cp6.zip` | 2.3 (the passes with the home move) and the rightward row | `06872fff` | `65f79a0694e75784c734270aa691488572d5611f89b66a5de05b2cc3d7ef69fd` |
| `fill-s13d-g4-cont4-cp7.zip` | 2.4–2.6 (the mirror, cleanup, assembly: `exists_zoneRebalanceTM`) | `374337b0` | in its `.sha256` |
| **`fill-s13d-g4-cont4.zip`** (this) | final: both targets | `374337b0` | in its `.sha256` |

- **Brief:** `campaign/fills/s13d/briefs/s13d-fill-g4-cont4.md`, SHA-256
  `852265b069a8a7a7a34a83931d44d6aa8088b3cd5ee93e768d636d271666052c`. Verified; the repository
  copy differs only in its three `@ANCESTOR@` placeholders.
- **Addendum v2.5:** SHA-256
  `90851511cf164dfa84ac9264cb5ba7acd54b7f551c823ae5d1000e43e233abf0`. Verified.
- **Base and branch:** the base is `f89c5c8da79997f4fb73bbfce04ed7f671afe206` on
  `complexity/arora-barak-ch3-4`.
  - **Ancestor check:** the branch `fill/s13d-g4-cont4` was created at exactly the base;
    `git rev-parse HEAD` printed the base, and the owned file's blob is
    `1abbb8716d0450ea9b7cc10ef15e6204ed920b4a`.
  - No rebase, merge or cherry-pick was done. **Nothing was pushed to the repository**, and no
    pull request was opened.
- **History:** 37 commits on the base, listed in order in `patches/` (a `git format-patch` series
  against the base) and in the bundle `fill-s13d-g4-cont4.bundle`.
  - The bundle's branch is `deliver/fill-s13d-g4-cont4`, and its only prerequisite is the base.
  - The commits since zip 6:
    - `4f8a01e5`: the leftward row through the mirror lockstep; **`exists_zoneRebalanceTM`
      proved**.
    - `374337b0`: the mirror lockstep's two box ends through one definition (`zr_mirB`). This
      removed a 98% pair the screen caught.

## Environment (addendum Part 1; logs in `logs/`)

- **Preflight** (`preflight.log`): 4 cores; cgroup v1 without an effective memory limit, so the
  headroom is `MemAvailable` = 15,906,124 kB (15 GiB ≥ 4 GiB), 221 MB in use, no OOM events;
  24 GiB free on the clone's filesystem (≥ 12 GiB), no tmpfs; toolchain
  `leanprover/lean4:v4.25.0`, installed by elan, no shim.
- **Cache** (`cache-store.log`, `cache-get.log`): `~/.cache/mathlib` did not exist before the
  fetch; the order list's **40 Mathlib roots** (`mathlib-roots.txt`) were fetched by
  `TAR_OPTIONS=--no-same-owner lake exe cache get <roots>`: 1,002 files downloaded and
  decompressed, "Completed successfully!", exit 0, no retry. The manifest check is clean
  (`manifest-check.log`); absent are `doc-gen4`, `UnicodeBasic`, `BibtexQuery` and `MD4Lean`,
  which no order-list module imports. No zero-size olean; the cache probe exited 0. **No
  `lake build`, no unfiltered `lake exe cache get`.**
- **Bootstrap** (`bootstrap.log`): the 96-module order list, one module at a time through
  `scripts/lean_check_tree.sh`: **96/96, exit 0**; peak RSS 2,900 MiB. The base sorry set by name
  (`bootstrap-sorries-by-name.txt`) has **27 names, identical** to
  `campaign/fills/s13d/logs/s13d-fill-g4-cont4-base-sorries.txt`.
- **Base blob check:** the owned file at the base is blob
  `1abbb8716d0450ea9b7cc10ef15e6204ed920b4a`.

## Checkpoints

- 1.1 (the right pass): done in earlier rounds; re-indexed to every level in zip 1.
- **1.2 (the return home): done** (zip 1).
- **1.3 (the left pass): done** (zip 2).
- 1.4 (the `ℓ = 0` branch): **subsumed** (zip 3): every phase is uniform in `ℓ`, so the machine
  has no zero-level branch. A route deviation, flagged.
- **1.5 (cleanup), 1.6 (assembly): done; `exists_zoneExtendTM` proved** (zip 3).
- **2.1 (the scan with `short`): done** (zip 4, rightward; the leftward scan is the mirror's).
- **2.2 (one level's guarded column move): done** (zip 5, the rightward cascade's two moves; the
  leftward ones are the mirror's).
- **2.3 (the passes with the home move): done** (zip 6), with the found path, its time bound and
  the rightward row.
- **2.4 (the mirror): done** (zip 7): the leftward row through the mirrored machine and the
  lockstep transport, rather than mirrored passes (the brief's first option).
- **2.5 (cleanup): done** (zip 7): the screen's pairs factored at each round, the seal clean.
- **2.6 (assembly): done; `exists_zoneRebalanceTM` proved** (zip 7).

## The extension row (`exists_zoneExtendTM`, zip 3; unchanged since)

**The machine** (four contracts through stationary seams, `zr_extendContract`):

1. **The right pass and the return home** (`zr_rightReturnContract`, zip 1): seek the right end;
   copy the last right field (the last zone, or the home at level zero; both of the new
   half-capacity `2^ℓ`) to scratch as the ruler `[q, q + 2^ℓ)`; write the new right zone's halves
   with an adjusted walk between; skip the outer half; the phase-host loop home (one round per
   field: `skipBackTM`, then the one-cell home test).
2. **The left pass** (`zr_leftPassContract`, zip 2): seek the left layout's outermost cell
   `2 − zoneStart ℓ`; one zoned step across the separator; two left moves by the ruler, the inner
   half written after the first and the outer half after the second. **Displacement: the second
   option** (two adjusted walks by `2^ℓ` and one step: `2 · 2^ℓ + 1`, `zr_left_reach`); **`ℓ = 1`
   checked: the outer end is cell `−8`** (`zr_leftPass_one`).
3. **The final return** (`zr_finalContract`): `seekEndTM` over the whole extended layout
   (`zr_wholeFields`) from its outermost left cell to its right end, then the return loop home at
   the extended data, then `clearTM_contract` on the ruler.
4. **The assembly** (`zr_rightLeftContract`, `zr_extendContract`), left-nested so that the seam
   into the final return is proved from the row's precondition.

**The row:** `C = 135`; `Contract.ofSegment` with precondition `zoneRowPre`, endpoint
`zoneExtendPost done`, envelopes `zoneRowLo`/`zoneRowHi` at `ℓ`; time at most `135 · (2^ℓ + 1)`
(`zr_extend_time_le`).

**The return home** (zip 1): the skip over the outer half, then the loop (`Round.iterate` over
`round_iff`-built rounds; the anchor distinct from `skipBackTM`'s run state). **The seam:**
`DecidableEq` given explicitly (`zr_decEqRP`, `inferInstance` under `set_option
synthInstance.maxSize 256 in` on that declaration only); `link D = (zr_outerWord D,
zoneExtendData D)`; `hlink` = `zr_rightReturn_link`, proved.

**Scratch layout and the walk convention** (both rows): the extension row keeps one ruler of
`2^ℓ` cells `inl false` at `[q, q + 2^ℓ)` from the scratch head's start `q`, written by the right
pass, used by both passes, cleared at the end; the walk reads its ruler along its direction from
its head (`walkTM_contract`'s convention), the rightward adjusted walk from the ruler's first
cell, the leftward one from its last (`zr_rulerTape_word`). The rebalance row keeps the scan's
**unary zone count** (`i₀ + 1` cells `inl false` from `q`) and, during the found path, a **count
stack** of marks above it (`zr_stk`); the column moves lay their copies out from the stack's top
as a field list (`zr_scr`, `fieldsTape`). Scratch is blank again at both rows' ends.

## The rebalance row (`exists_zoneRebalanceTM`)

**The row** (the theorem's body): `C = 2300`; for each `dir` and `t`, the state type is the
rightward row's (`zr_stOf (zr_rowC t [])`), with its `Fintype` and `DecidableEq` from
`zr_rowInst` (built part by part: `instFintypeSum`/`instDecidableEqSum` down the nested sums,
`zr_finHost`/`zr_decHost` at each loop host's dependent phase type, since the default instance
search gives up at that depth); the exits `done = zr_rowDone t` and `short = zr_rowShort t` are
distinct (`Sum.inl_ne_inr`).

- **`dir = true`:** the machine `zr_machineOf (zr_rowC t [])` and the contract `zr_rowR t 2300`
  with its fields `zr_rowR_spec`.
- **`dir = false`:** the mirrored machine `zr_mirTM (zr_machineOf (zr_rowC t []))` and the
  contract `zr_rowLeft t 2300` with its fields `zr_rowLeft_spec`.

### The rightward scan (zip 4)

The scan is `zr_homeSkipContract` (skip the home field) sequenced into the scan loop
`zr_scanLoopContract`, on the generic loop host (`zr_hostPh`, `zr_hostMachines`, `zr_hostRed`,
`zr_hostTM`, `zr_hostBodyContract`, `zr_round_of_body`; phase 1's return loop is its instance).
Its round marks scratch with one ruler cell and tests the zoned cell: a blank cell is the
**short** escape, an occupied track-`t` slot the **found** escape, an empty one skips the zone.
`zr_scan_fields`: the zoned head ends at zone `i₀`'s start (past the layout when short), with a
**unary zone count** of `i₀ + 1` ruler cells on scratch from its start `q`, in
`zoneStart i₀ + 8 i₀ + 9` steps (found) or `+ 7` (short). The short path (`zr_shortContract`) is
phase 1's return loop at the scanned data, then the count's clear (`zr_countClearContract`).

### One level's column moves (zip 5)

The two moves of the rightward cascade at level `i`, each one pinned segment (the frame:
`zr_pinned`, `zr_PinStep`, `zr_PinSeg`, `zr_seg`, `zr_segSeq`, and the pinned catalog rows
`zr_pinSkipContract`, `zr_pinBackContract`, `zr_pinCellContract`, `zr_pinWalkContract`,
`zr_pinCopyContract`, `zr_pinClearContract`):

- **the right inward shift** (`zr_inSeg`, `zr_inSeg_spec`; specification `zr_shiftIn_tape`):
  30 steps of the frame, `76 · 2^(i-1) + 77` machine steps;
- **the left outward shift** (`zr_outSeg`, `zr_outSeg_spec`; specification `zr_shiftOut_tape`):
  40 steps of the frame, `76 · 2^(i-1) + 107` machine steps.

Each copies the track-`t` column of the zones involved to scratch with the mapped copy
(`extract := zoneSlotOf t`), cuts the copies at offset `2^(i-1)` by one-cell blanks (the walk over
field `i - 1` of the zoned tape is the ruler), and writes the pieces back with the mapped copy
(`merge := zoneSlotSet t`), which keeps the other tracks. **Route deviation (flagged in zip 5):**
no re-pack by `scanTM_contract`; the copies are cut instead, so the column's cells are never
re-encoded. The guards are characterized at the cells their tests read (`zr_inGuard_iff`,
`zr_outFull_iff`, `zr_outRoom_iff`), and a disabled guard is the identity (`zr_shiftIn_off`,
`zr_shiftOut_off`, `zr_inZ_off`, `zr_outZ_off`), so a guarded move's endpoint is the moved tape
whichever way its branch goes.

### The passes and the home move (zip 6, checkpoint 2.3)

A **pass** is a pinned segment on the loop host whose body is one **round**: a pinned branch on a
one-cell test, re-run at the next index until the test escapes.

- **Rounds** (`zr_peekRound`, `zr_popRound`): a peek one cell beside the head
  (`zr_pinPeekContract`) or a pop (the count stack's cell below its top); on `true` stop at the
  anchor, otherwise run the arm. Steps `zr_peekRound_step`/`zr_popRound_step`, ways back
  `…_back`, escapes `zr_homeEsc`/`zr_popEsc`.
- **The loop** (`zr_pinRound`, `zr_pinLoop`, `zr_passContract`, `zr_pass_step`, `zr_passSeg`):
  rounds pinned from each anchor to the next index's, escaping after `n j` further rounds, run as
  one contract from the anchor to the escape, the time the rounds' sum, in one pass box.
- **The pass index** (`zr_Px`): the data, the anchor's field, and scratch as a **count stack**
  (`zr_stk`: a base tape blank from `b`, marks on `[b, s)`, the head at `s`;
  `zr_stk_push`/`zr_stk_pop`).
- **The rightward cascade's passes**, in the side-pass order of `zr_cascade_passes` (the pure
  cascade's reordering, checked for every guard and without a fullness assumption):
  `zr_p1Pass` (descending on the right, inward shifts at levels `i₀, …, 1`, a mark pushed per
  round, stopping at the home); `zr_woPass` (the walk out to the left, a mark popped per field);
  `zr_p2Pass` (descending on the left, outward shifts); **the home move** `zr_hmContract` (a
  column operation on left zone `0`, the home and right zone `0` through scratch, guarded by left
  zone `0`'s outer slot; `zoneMove_true`); a pop; `zr_p3Pass` (ascending on the right) with its
  return `zr_rbPass`; `zr_p4Pass` (ascending on the left) with its return `zr_lbPass`.

### The found path (zip 6)

`zr_fpSeg` chains the passes, the home move and the gaps between them (`zr_fpG0` … `zr_fpG10`)
in one `zr_segSeq` chain, through the stages `zr_fpS1` … `zr_fpS9` (`zr_fp1` … `zr_fp9`).

- **Data** (`zr_fp_data`): track `t` ends as `zoneCascadeRight i₀ (z t)`; every other track and
  the count are kept.
- **Box** (`zr_fpL`/`zr_fpU`): the zoned head within `zoneStart (i₀ + 1)` of home.
- **Time** (`zr_fpSeg_time`): at most `1000 · 2^(i₀ + 1) + 200`, from each round's bound by its
  level (`zr_p1Tau_le` … `zr_lbTau_le`) and the passes' geometric sums
  (`zr_time_desc`/`zr_time_asc`).

### The rightward row (zip 6)

Indexed by the data and the scratch start `q`; start pin `zr_rowT0` (the zoned tape, scratch
blank), endpoint pin `zr_rowT2` (the zoned tape of the rebalanced data, scratch blank), heads
back:

1. **the scan as a pinned test** (`zr_scanPin`, `zr_scanPin_step`, `zr_scan_verdict`), its two
   escapes restated (`zr_scan_exits`), ending at the count of `i₀ + 1` marks;
2. **the found arm** (`zr_foundSeg`): the found path from the scan's end (`zr_rowP0`), widened to
   the row's box (`zr_fpRow`), then the count's clear (`zr_ccPin`); its endpoint is the
   rebalanced data by `zr_fp_data`, `zoneRebalance_of_lt` and `zoneCascade_true`;
3. **the short arm** (`zr_shortPin`): the return home and the count's clear at `i₀ = ℓ`
   (`zr_short_eq`), the data unchanged (`zoneRebalance_of_le`);
4. **the branch** (`zr_rowC`, `zr_rowC_step`, `zr_rowC_back`, `zr_rowC_state`): `Contract.branch`
   through `zr_PinStep_branch` (which, with `zr_pin_blink` and `zr_BackIs_branch`, takes a test
   that moves its pin);
5. **on the data** (`zr_rowR`, `zr_rowR_spec`): at the start's own scratch start
   (`zr_rowPre_pin`), `Contract.ofSegment` with the target's precondition, endpoint and
   envelopes at `zoneRebalanceIndex true t` and `C`, for every `C ≥ 2300` (time `zr_rowC_time`:
   at most `2300 · (2^i₀ + 1)`; the box `zr_rowL`/`zr_rowU`: the zoned head within
   `zoneStart (i₀ + 1)` of home, scratch within `18 · 2^i₀ + i₀ + 13` of `q`).

### The leftward row: the mirror (checkpoint 2.4)

The brief's first option, **through `ZoneContents.swap` and `zr_mirror_tape`**:

- **The mirror** (`zr_mir`): tape `0` and its head reflected about home, tape `1` kept; an
  involution (`zr_mir_mir`).
- **The mirrored machine** (`zr_mirTM`): `M`'s transition table with tape `0`'s moves reversed.
  Its step is the mirrored step (`zr_mir_step`, through `MultiTapeTM.step_of_some`/`_of_halt`,
  `Action.apply_*` and `zr_inputSymbol_congr`, the input head reading the same cell).
- **The lockstep** (`zr_mir_lockstep`): a `Turing.Lockstep` of cost `1` with the same exits, so
  `Turing.Contract.lockstep` transports the rightward row along it. Its per-step box is
  `zr_mirB min`/`zr_mirB max` (the mirrored heads and, at a live step, the next ones;
  `zr_mir_box`).
- **The leftward row on the data** (`zr_rowLeft`, `zr_rowLeft_spec`): at the data with every
  track's sides exchanged (`zr_swapD`) and the mirrored start. Its precondition holds there
  (`zr_mir_pre`, the mirrored zoned tape being the exchanged data's, `zr_mirror_tape`); the
  scanned index is the leftward one (`zr_index_swap`); the transported endpoint, mirrored back, is
  `zoneRebalancePost false` (`zr_mir_post`, through `Turing.zoneRebalance_false`); the time is the
  rightward row's (the lockstep's sum of `1`s); the envelope is the rightward one reflected on
  tape `0` (`zr_mir_env`, `zr_mir_lohi`), the same since `zoneRowLo`/`zoneRowHi` are symmetric
  on tape `0`.

## Declarations (at `374337b0`; the base has 91, 18 public / 73 private)

**872 declarations, 18 public / 854 private; 14,887 lines** (the base has 1,572).

- **Since the base** (`logs/declchanges-cp7.txt`): 783 new, 2 removed (`zr_RightData`,
  `zr_left_two_walks`, both before zip 3), 38 changed. **Each of the 823 is listed with its kind
  and its role** (its docstring's first sentence) in `logs/declarations-roles-since-base.md`.
  Every new declaration has a docstring.
- **Since zip 6** (`logs/declchanges-since-prev-cp7.txt`, `logs/declarations-roles-since-cp6.md`):
  18 new privates, 0 removed, 1 changed.
  - **New:**
    - the mirror: `zr_mir`, `zr_mir_mir`, `zr_inputSymbol_congr`;
    - the mirrored machine and the lockstep: `zr_mirTM`, `zr_mir_step`, `zr_mir_lockstep`;
    - the lockstep's box: `zr_mirB`, `zr_mir_box`;
    - the exchanged data: `zr_swapD`, `zr_index_swap`;
    - the transported fields: `zr_mir_pre`, `zr_mir_post`, `zr_mir_env`, `zr_mir_lohi`;
    - the leftward row: `zr_rowLeft`, `zr_rowLeft_spec`;
    - the states' instances: `zr_finHost`, `zr_rowInst`.
  - **Changed:** `exists_zoneRebalanceTM`. Its body is now the proof (above). Its status
    paragraph, now headed `**Implementation.**`, describes the machine, the time and box bounds,
    the mirror and the constant, with no campaign labels.
- **The two status paragraphs:**
  - `exists_zoneExtendTM`'s `**Implementation.**` (zip 3, unchanged) gives:
    - the four contracts and their catalog rows;
    - the right pass, the return home, the left pass and the final return;
    - the bound `135 · (2^ℓ + 1)`.
  - `exists_zoneRebalanceTM`'s `**Implementation.**` gives:
    - the pinned branch on the scan;
    - the found path's passes, home move and pop, with its bound `1000 · 2^(i₀+1) + 200`;
    - the short path;
    - the row's bound `2300 · (2^i₀ + 1)` and its box;
    - the mirror for `dir = false`;
    - the constant `2300`.

  The statements and proof sketches are untouched.
- **Public:** nothing new or changed in statement.
- **Regions** (`logs/regions-cp7.txt`): only the owned regions changed. The prefix before the
  home (126 lines) is identical, and the rows section is identical outside regions (b) and (c):
  the two target bodies and their status paragraphs.
- **Further leaves:** none. The one-cell leaf (`zr_cellTM`) of the first round is the only leaf.
- **Promotion candidates** (notes only; each stated mathematically):
  1. **The one-cell leaf** (`zr_cellTM`, `zr_cellContract`, `zr_stepContract`): a machine that
     reads one cell, writes `f` of it, moves by `d` and exits at `choose` of it, as a contract with
     time `1`. Also the contract adapters `zr_singletonContract`, `zr_reindexContract`,
     `zr_exitsContract`, `zr_machineOf`/`zr_entryOf`, and `zr_bindState_eq` (zip 3).
  2. **The return loop** (`zr_loopContract`): from any field of a field layout, walk home in
     `O(the distance)`, as a row (zip 3).
  3. **The generic two-phase loop host** (`zr_hostTM`, `zr_hostBodyContract`, `zr_round_of_body`):
     a `Round.iterate` loop with any set of escapes, on the public phase host (zip 4).
  4. **The pinned-step frame** (`zr_PinStep`, `zr_PinSeg`, `zr_seg`, `zr_segSeq`,
     `zr_PinStep_branch`, and the pinned catalog rows): it chains contracts whose start and end
     configurations are given in closed form (a "pin"). A pinned branch's test may move its pin
     (zips 5–7).
  5. **The pinned loop** (`zr_pinRound`, `zr_pinLoop`, `zr_passContract`): a round contract
     iterated to its escape is one contract, whose time is the sum of the rounds' times and whose
     head box is the union of theirs (zip 6).
  6. **The count stack on scratch** (`zr_stk` with `zr_stk_push`/`zr_stk_pop`): a unary counter
     with push and pop in closed form (zip 6).
  7. **The mirror lockstep** (`zr_mir`, `zr_mirTM`, `zr_mir_step`, `zr_mir_lockstep`). For every
     two-tape machine `M` and configuration `c`,
     `(zr_mirTM M).step (zr_mir c) = zr_mir (M.step c)`, where `zr_mirTM` reverses tape `0`'s
     moves and `zr_mir` reflects tape `0` and its head about cell `0`. Hence, through
     `Turing.Contract.lockstep`, every contract of `M` transports to `zr_mirTM M`, with the same
     time and the envelope reflected on tape `0`. It does not depend on zones (zip 7).
- **Escalations:** none.

## Evidence (all as of `374337b0`)

- **Sweep** (`logs/sweep-cp7.log`): the owned module and the facade, exit 0.
  - The owned module takes 585.1 s, with a peak RSS of 4,496 MiB. It ran beside the screen;
    zip 6's 290.3 s was measured alone.
  - **It has no warning at all**: no sorry, and nothing added has a warning.
- **Axioms** (`logs/axioms-cp7.log`, all 872 declarations):
  - **`exists_zoneExtendTM`: `[propext, Classical.choice, Quot.sound]`**;
  - **`exists_zoneRebalanceTM`: `[propext, Classical.choice, Quot.sound]`**;
  - every other declaration is within the same three: 559 all three, 83
    `[propext, Quot.sound]`, 195 `[propext]`, 4 `[Quot.sound]`, 29 none.

  **`sorryAx` appears nowhere** (grep: 0 lines).
- **Probe** (`probe/G4C4ImportProbe-cp7.lean`): the brief's 448 checks plus the 53 names the
  elaborated-constant walk finds outside them: **501 checks of 490 names, 0 errors, 0 warnings**
  (`probe/probe-cp7.out`).
  - 24 of the 53 are new since zip 6, all public at the base or generated from base declarations:
    - the lockstep (`Build/Contract/Basic`): `Turing.Lockstep`, `Turing.Lockstep.mk`,
      `Turing.Contract.lockstep` and its `_pre`/`_post`/`_lo`/`_hi`;
    - the mirrored machine's step (`Configuration`, `Deterministic`, `Simulation`):
      `Turing.Action.mk` and its fields `state`/`inputTape`/`workTapes`/`output`, the
      `Turing.Action.apply_*` lemmas, `Turing.MultiTapeTM.q₀`,
      `Turing.MultiTapeTM.step_of_some`/`_of_halt`, `Turing.Cfg.workTapeSymbols_eq`;
    - the input head (`Configuration`): `Turing.Cfg.inputSymbol_of_zero`/`_of_end` and the lemma
      `Turing.inputSymbolInner`.
  - The walk (`logs/walk-cp7.txt`, 295 rows) lists every TCSlib constant the module mentions,
    with its module (below).
- **Seal** (rule 10; `seal/`): **75 names** sealed: zip 6's 74 plus `Turing.Contract.lockstep`,
  from the kind walk over the `zr_` declarations and both targets (`seal/walk2-cp7.txt`,
  `seal/seal-list-cp7.txt`). The commands are in `tools/cpev.sh` and `tools/seal.py`.
  - The sealed copy (`seal/ZRSeal-cp7.lean`) elaborates with **no error except the inside
    controls**, and with no sorry (`seal/seal-inside-cp7.out`, exit 1 from the controls only).
  - **Controls:** inside, 72 of 75 fail, as they must. Outside (`seal/ZRSealOutside-cp7.lean`,
    `seal/seal-outside-cp7.out`, exit 0), all 75 pass.
  - The three that pass inside are uninformative: zip 3's structure-literal instances
    `instFintypeSeekPhase` and `instFintypeSweepPhase`, and the generated
    `Contract._sizeOf_inst`.
  - Among the sealed names are the ones the mirror goes through: `Turing.Action.apply`,
    `Turing.Cfg.inputSymbol`, `Turing.ZoneContents.swap`, `Turing.zoneRebalance` and
    `Turing.Contract.lockstep`. The mirrored step is proved through `Action.apply_*`,
    `MultiTapeTM.step_of_some`/`_of_halt` and `Cfg.inputSymbol_of_zero`/`_of_end`, with
    `inputSymbolInner`; it never reduces `Action.apply` or `Cfg.inputSymbol`.
  - Nothing new was caught this round.
- **Inspection** (`inspection/`): 6,036 tactic-argument occurrences and 904 `show`/`change`
  terms on the diff's added lines (`inspection/inspection-args-cp7.tsv`), with **1,037 distinct
  identifiers**, each classified by Lean (`inspection/inspection-kinds-cp7.out`, 0 errors): 329
  theorems, 25 definitions, 5 inductives; the rest are own declarations, locals and tactic
  names.
  - The definitions with their positions are tabulated in
    `inspection/inspection-definitions-cp7.tsv` (`tools/inspcheck.py`).
  - The **other-file** definitions are `zonedTape`, `zoneStart`, `zoneCapacity`, `zoneShiftIn`,
    `zoneShiftOut`, `zoneShiftIndex`, `fieldOffset`, `joinFields`, and, new this round,
    `Action.apply` (5) and `zoneRebalance` (1). They occur **only in `show` statements or inside
    term arguments** (`rw [show … by …]`), **never as a rewrite or simp rule.**
  - Core and Mathlib (`Function.update`, `List.ofFn`, …) occur the same way. The one exception
    is the core simproc `reduceCtorEq`, a simp rule (rule 10 allows core).
  - **This file's own** row definitions (`zoneRowPre`, `zoneRowLo`, `zoneRowHi`,
    `zoneRebalanceIndex`, `zoneRebalancePost`, `zoneExtendData`, `zoneExtendPost`) are also
    `rw`/`simp` arguments. Rule 10 concerns other files' definitions only.
  - **Correction (repeated from zip 6) to zip 5's report:** it said every listed definition
    occurred only in `show` and term positions. In fact the same own-file definitions, and
    `reduceCtorEq`, were already simp and rewrite arguments there, which rule 10 allows.
- **Rule 11:** the cumulative diff (`git diff f89c5c8d 374337b0`) contains:
  - none of `copyTM_run`, `transferTM_run`, `clearTM_run`, `compareTM_run`,
    `incrementTM_run_succ`, `incrementTM_run_overflow`
    (`grep -nE 'copyTM_run|transferTM_run|clearTM_run|compareTM_run|incrementTM_run_succ|incrementTM_run_overflow'`:
    **0 lines**);
  - none of `Build/Catalog`'s 392 private names (each grepped as a word in the added lines:
    0 hits).

  Every new private is `zr_` (0 exceptions).
- **Lint** (`logs/lint-cp7.txt`): `style_lint: 0 FAIL, 33 WARN over 40 files`, as at the base. No line is
  over 100 characters.

## Declarations cited outside the file (rule 10; the elaborated-constant walk)

`logs/walk-cp7.txt` lists the **295 TCSlib constants** that the module's elaborated terms
mention. It covers every declaration, frozen and new alike, with its module. Of these, 53 are
outside the brief's probe list; they are appended to the probe, which was re-run (above). By
module (the `Turing.` prefix dropped):

- **`Build.Contract.Catalog`** (51): `clearTM_contract`, `clearTM_contract_hi`, `clearTM_contract_lo`, `clearTM_contract_post`, `clearTM_contract_pre`, `clearTM_contract_time`, `copyMapTM_contract`, `copyMapTM_contract_hi`, `copyMapTM_contract_lo`, `copyMapTM_contract_post`, `copyMapTM_contract_post_workTapes`, `copyMapTM_contract_pre`, `copyMapTM_contract_time`, `seekEndTM_contract`, `seekEndTM_contract_lo`, `seekEndTM_contract_post`, `seekEndTM_contract_pre`, `seekPost`, `seekPost_inputPos`, `seekPost_output`, `seekPost_workTapePos`, `seekPost_workTapes`, `seekStartTM_contract`, `seekStartTM_contract_hi`, `seekStartTM_contract_post`, `seekStartTM_contract_pre`, `seekStartTM_contract_time`, `skipBackTM_contract`, `skipBackTM_contract_hi`, `skipBackTM_contract_lo`, `skipBackTM_contract_post`, `skipBackTM_contract_pre`, `skipBackTM_contract_time`, `skipTM_contract`, `skipTM_contract_hi`, `skipTM_contract_lo`, `skipTM_contract_post`, `skipTM_contract_pre`, `skipTM_contract_time`, `sweepMapWrite`, `sweepPost`, `sweepPost_inputPos`, `sweepPost_output`, `sweepPost_workTapePos`, `sweepPost_workTapes`, `walkTM_contract`, `walkTM_contract_hi`, `walkTM_contract_lo`, `walkTM_contract_post`, `walkTM_contract_pre`, `walkTM_contract_time`.
- **`Build.Zone`** (51): `ZoneContents`, `ZoneContents.casesOn`, `ZoneContents.extend`, `ZoneContents.home`, `ZoneContents.left`, `ZoneContents.mk`, `ZoneContents.right`, `ZoneContents.right_le`, `ZoneContents.swap`, `ZoneContents.swap_right`, `ZoneContents.swap_swap`, `ZoneContents.words`, `ZoneContents.words_false`, `ZoneContents.words_le`, `ZoneContents.words_true`, `zoneCapacity`, `zoneCapacity_eq`, `zoneCascade`, `zoneCascadeRight`, `zoneCascadeRight_eq`, `zoneCascade_true`, `zoneMove`, `zoneMoveRight`, `zoneMoveRight_home`, `zoneMove_true`, `zoneRebalance`, `zoneRebalance_false`, `zoneRebalance_frame`, `zoneRebalance_of_le`, `zoneRebalance_of_lt`, `zoneShiftIn`, `zoneShiftInW`, `zoneShiftInW_eq`, `zoneShiftIn_home`, `zoneShiftIn_left`, `zoneShiftIn_right`, `zoneShiftIndex`, `zoneShiftIndex_empty`, `zoneShiftIndex_eq`, `zoneShiftIndex_eq_length_iff`, `zoneShiftIndex_extend`, `zoneShiftIndex_le`, `zoneShiftIndex_nonempty`, `zoneShiftOut`, `zoneShiftOutW`, `zoneShiftOutW_eq`, `zoneShiftOut_home`, `zoneShiftOut_left`, `zoneShiftOut_right`, `zoneStepPair`, `zoneStepPair_eq`.
- **`Build.Contract.Basic`** (43): `Cfg.SameOutside`, `Contract`, `Contract._sizeOf_inst`, `Contract.cut`, `Contract.env`, `Contract.exit_mem`, `Contract.hi`, `Contract.live`, `Contract.lo`, `Contract.lockstep`, `Contract.lockstep_hi`, `Contract.lockstep_lo`, `Contract.lockstep_post`, `Contract.lockstep_pre`, `Contract.mk`, `Contract.ofSegment`, `Contract.ofSegment_hi`, `Contract.ofSegment_lo`, `Contract.ofSegment_post`, `Contract.ofSegment_pre`, `Contract.ofSegment_time`, `Contract.post`, `Contract.pre`, `Contract.run`, `Contract.segment`, `Contract.time`, `HeadBox`, `Lockstep`, `Lockstep.mk`, `Round`, `Round.iterate`, `Round.segment`, `Segment`, `Segment.mono`, `Segment.trans`, `Segment.zero`, `headBox_iff`, `not_mem_roundStop`, `roundOrbit`, `roundOrbit_succ`, `roundOrbit_zero`, `roundStop`, `round_iff`.
- **`Build.Catalog`** (38): `SeekPhase`, `SeekPhase.back`, `SeekPhase.casesOn`, `SeekPhase.done`, `SeekPhase.gap`, `SeekPhase.run`, `SweepPhase`, `SweepPhase.done`, `SweepPhase.sweep`, `clearTM`, `copyMapTM`, `fieldOffset`, `fieldOffset_cons_succ`, `fieldOffset_succ`, `fieldOffset_zero`, `fieldsTape`, `fieldsTape_field`, `fieldsTape_nil`, `fieldsTape_of_length_le`, `fieldsTape_of_neg`, `fieldsTape_of_nonneg`, `inputMoveAction`, `instDecidableEqSeekPhase`, `instDecidableEqSweepPhase`, `instFintypeSeekPhase`, `instFintypeSweepPhase`, `joinFields`, `joinFields_cons_cons`, `joinFields_singleton`, `length_joinFields_add_one`, `seekEndTM`, `seekStartTM`, `skipBackTM`, `skipTM`, `step_of_tapeAction_move`, `step_of_tapeAction_write`, `tapeAction`, `walkTM`.
- **`Build.ZoneTape`** (35): `ZoneCell`, `ZoneContents.ext'`, `ZoneSym`, `two_le_zoneStart`, `zoneCellAt`, `zoneCellAt_eq`, `zoneCellOfCell`, `zoneCellOfCell_inr`, `zoneCells`, `zoneCells_eq`, `zoneCells_length`, `zoneOwner`, `zoneOwner_eq`, `zoneSlotOf`, `zoneSlotOf_inr`, `zoneSlotSet`, `zoneSlotSet_eq`, `zoneStart`, `zoneStart_add_lt`, `zoneStart_eq`, `zoneStart_mono`, `zoneStart_succ`, `zonedTape`, `zonedTape_blank_outside`, `zonedTape_extend`, `zonedTape_isSome`, `zonedTape_left`, `zonedTape_left_sep`, `zonedTape_left_word`, `zonedTape_of_neg`, `zonedTape_of_pos`, `zonedTape_right`, `zonedTape_right_sep`, `zonedTape_right_word`, `zonedTape_zero`.
- **`Configuration`** (27): `Action`, `Action.apply`, `Action.apply_inputPos`, `Action.apply_output`, `Action.apply_state`, `Action.apply_workTapePos`, `Action.inputTape`, `Action.mk`, `Action.output`, `Action.state`, `Action.workTapes`, `Cfg`, `Cfg.ext`, `Cfg.inputPos`, `Cfg.inputSymbol`, `Cfg.inputSymbol_of_end`, `Cfg.inputSymbol_of_zero`, `Cfg.mk`, `Cfg.output`, `Cfg.state`, `Cfg.workTapePos`, `Cfg.workTapeSymbols`, `Cfg.workTapeSymbols_eq`, `Cfg.workTapes`, `inputSymbolInner`, `moveInputPos`, `moveInputPos_zero`.
- **`Build.Contract.Seam`** (24): `Cfg.bindState`, `Cfg.bindState_inputPos`, `Cfg.bindState_output`, `Cfg.bindState_state`, `Cfg.bindState_workTapePos`, `Cfg.bindState_workTapes`, `Contract.branch`, `Contract.branch_hi`, `Contract.branch_lo`, `Contract.branch_post`, `Contract.branch_pre`, `Contract.branch_time`, `Contract.inPhase`, `Contract.inPhase_hi`, `Contract.inPhase_lo`, `Contract.inPhase_post`, `Contract.inPhase_pre`, `Contract.inPhase_time`, `Contract.seq`, `Contract.seq_hi`, `Contract.seq_lo`, `Contract.seq_post`, `Contract.seq_pre`, `Contract.seq_time`.
- **`Deterministic`** (11): `MultiTapeTM`, `MultiTapeTM.mk`, `MultiTapeTM.q₀`, `MultiTapeTM.runFrom`, `MultiTapeTM.runFrom_add`, `MultiTapeTM.runFrom_succ_eq_step'`, `MultiTapeTM.runFrom_zero`, `MultiTapeTM.step`, `MultiTapeTM.step_of_halt`, `MultiTapeTM.step_of_some`, `MultiTapeTM.tr`.
- **`Simulation`** (6): `Action.apply_workTapes`, `FinTM.bufferTape`, `FinTM.bufferTape_eq`, `FinTM.bufferTape_left`, `FinTM.bufferTape_nat`, `FinTM.bufferTape_nil`.
- **`StateRenaming`** (6): `Cfg.mapState`, `Cfg.mapState_inputPos`, `Cfg.mapState_output`, `Cfg.mapState_state`, `Cfg.mapState_workTapePos`, `Cfg.mapState_workTapes`.
- **`Build.Seam`** (3): `phaseHostTM`, `seamCompTM`, `seamCompTM₂`.

## Duplication (screen v3; `screens/`)

Both screens ran with the brief's commands over the 10-file population
(`screen-population.txt`), one run at a time under `nice -n 10`:

- **Before** (`screens/screen-before.txt`, at the base, 11 min 47 s): 847 declarations, 477
  pairs, 136,473 characters. This is identical to the campaign's
  `s13d-fill-g4-cont4-screen-base.txt`.
- **After** (`screens/screen-after-cp7.txt`, on a worktree pinned at `374337b0`, 18 min 21 s):
  **1,391 declarations, 970 pairs, 353,746 characters**.

The results:

- **Against the base** (`screens/screen-diff-cp7.txt`): 500 new pairs, 7 gone. There is **no new
  cross-file pair with an owned-file declaration on either side**. Every new pair is in-file and
  **below 90%**; the highest is 88%.
  - The 7 gone pairs are base pairs among continuation 3's rows (`zr_adjustedBackContract`,
    `zr_rightSeekBackContract`, `zr_rightRuler_post`, …). They have been gone since zips 2–3,
    when those rows were factored.
  - **Every one of the 500 is listed in `screens/screen-pairs-since-base-cp7.md`, with the zip
    whose screen first showed it and its justification.**
    - Zips 1–3 have 173 of them (47, 73 and 53). Their reports justified these by class: the
      contract layer's field scaffolding, that is, the `Cfg.ext` branches, the
      `seq_time`/`seq_lo` openings and the `zoneRowPre` readings.
    - From zip 4 on, each pair has its own line in that zip's `screen-pairs-justified-cpN.md`
      (zip 4: 76, zip 5: 45, zip 6: 198, zip 7: 8), repeated in the cumulative list.
  - **The top pairs, with their shared text:**
    - **88% `zr_fp8` reproduces `zr_fp6`** (418/477), and 87% the other way. These are the found
      path's two ascending-pass stage lemmas. Each runs `zr_upPass_end`, then `zr_Px_ext` with the
      same `show … Function.update_idem, Function.update_self` data step. They differ in the
      passes (`zr_p3Nxt`/`zr_p4Nxt`), the moves (`zoneShiftIn true`/`zoneShiftOut false`) and the
      stages.
    - **87% `zr_out2Test_step` reproduces `zr_out1Test_step`** (295/338). These are the one-cell
      tests' closing `zr_PinStep_congr (zr_pinTest_step _ 0 _ 0 _ _)`, with the stationary-move
      rewrites `SignType.coe_zero, add_zero, Function.update_eq_self, min_self`/`max_self`. The
      cells, verdicts and boxes differ.
    - **87% `zr_scan_fields` reproduces `zr_return_post`** (400/461). This is the five-branch
      `Cfg.ext` over a seek-family endpoint (`Cfg.mapState_state`, `Option.map_some`,
      `Cfg.mapState_inputPos`, `seekPost_inputPos`, `funext j q`, `Cfg.mapState_workTapes`,
      `seekPost_workTapes`, …, `Cfg.mapState_output`).
    - **86% `zr_p2Body_back` reproduces `zr_p1Body_back`** (91/106), and 85% the other way. These
      are the two descending passes' ways back, each one line through the shared
      `zr_peekBranch_back`, over the two sides' guards.
    - **86% `zr_scanLoopContract` reproduces `zr_scanLoopPost`** (120/140). The contract's
      endpoint and time fields restate the endpoint's expressions
      (`zoneRebalanceIndex true t D`, `zoneStart (zoneRebalanceIndex true t D)`, the escape's
      `if`).
    - **85% `zr_p4Arm`/`zr_p3Arm`** (188/220). Each is a lead seamed to the side's guarded shift
      (`zr_reLead` with `zr_grdIn`, `zr_ldLead` with `zr_grdOut`), with the shared guard
      `zr_upV P ∧ zr_popE P = false` and `zr_pin_hlink`.
    - **85% `zr_pinTestContract` reproduces `zr_wordTestContract`** (147/173). This is the
      one-cell leaf re-indexed under two different preconditions: a pin, and a word at the head.
    - **85% `zr_mir_post` reproduces `zr_mir_mir`** (200/236). This is the mirror's per-tape case
      split (`Cfg.ext`, `by_cases hj : j = 0`, `subst hj`,
      `simp only [zr_mir, if_true, neg_neg]`/`simp only [zr_mir, hj, if_false]`). The involution
      and the mirrored endpoint are different statements; the endpoint goes through
      `zr_index_swap`, `zr_mirror_tape` and `zoneRebalance_false`.
    - **85% `zr_pinBack_step` reproduces `zr_pinSkip_step`** (321/379). These are two catalog rows
      through the one generic `zr_pinRe_step`; the rows (`skipTM`, `skipBackTM`) and their boxes
      differ.

    Every other new pair is at most 84%.
- **Against zip 6** (`screens/screen-diff-since-cp6.txt`): 8 new pairs and 0 gone, all in-file,
  the highest 85%. **Each is justified in `screens/screen-pairs-justified-cp7.md`:**
  - `zr_mir_post`/`zr_mir_step` against `zr_mir_mir` (85%, 66%): the mirror's per-tape case split
    (above).
  - `zr_rowInst` against `zr_rowDec` (82%, 84/102): the deep-sum instance tactic
    `repeat' (first | refine @instDecidableEqSum _ _ ?_ ?_ | refine zr_decHost ?_ | exact inferInstance)`.
    Instance search fails at that depth.
  - `zr_decHost`/`zr_finHost` (80%, 75%): the loop host's `DecidableEq` and `Fintype` instances,
    by the same per-phase `match` (`false => Option Bool`, `true => h`). These are different
    classes, with no common statement.
  - `zr_rowR_spec`/`zr_rowLeft_spec` (69%, 56%): the two rows' field restatements over
    `Contract.ofSegment_pre`/`_post`/`_lo`/`_hi`. The time bounds come from different sources:
    the rightward one from `zr_rowC_step` and `zr_rowC_time`, the leftward one from the rightward
    spec through `zr_index_swap` and `zr_mir_pre`.
  - `zr_mir_box` against `zr_mir_lockstep` (60%): the one-step rewrite
    `MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, zr_mir_step`.
- **The mirror** (the brief's hazard): `dir = false` is derived through `ZoneContents.swap` and
  `zr_mirror_tape`, by one lockstep transport of the rightward row. It is not a second copy of
  the passes, and **no pair between the two directions reaches 90%**: the highest is
  `zr_rowR_spec`/`zr_rowLeft_spec` at 69%.
- **What the screen caught in the final round.** At `4f8a01e5` there was a **98% pair**,
  `zr_mirLo` reproducing `zr_mirHi` (98/100), the lockstep box's two ends. It was fixed in
  `374337b0`: both ends are now one definition, `zr_mirB op`, with `min` and `max`. The evidence
  is the owned-file screens at `06872fff` and `4f8a01e5` with their diff
  (`screens/screen-own-*`). For earlier rounds, see each zip's report (zip 6: 59 pairs at 90% or
  more at `61e33ef2`, and a 100% pair at `a6cf08df`; all factored).
- **New copies: none.**

## Final checks (at `374337b0`; `logs/final-sweep-374337b0.log`)

1. **`Build/ZoneRebalance`:** zero errors, **no sorry warning and no other warning**.
2. **The sweep:** the 96-module order list, one module at a time through
   `scripts/lean_check_tree.sh` (via `tools/timed_check.py`), on a clean tree at `374337b0`.
   - **96/96, exit 0, 0 errors**; peak RSS 4,506 MiB.
   - `Build/ZoneRebalance` took 622.7 s and printed **no diagnostic at all**.
   - The sweep wrote its oleans to a fresh directory (`TCSLIB_OLEANS`), so every module was
     re-checked from its imports.
   - **Sorry warnings: 25**, which is the base's 27 minus both targets, checked by name
     (`logs/final-sweep-sorries-by-name-374337b0.txt`). Its diff against the bootstrap's list
     (`logs/final-sweep-sorries-diff-374337b0.txt`) is the `ZoneRebalance` line and the total
     only.
   - The tail:

     ```
     == TIMING TCSlib/Complexity/TuringMachine/NDCodeSimulator: start 2026-10-25T01:13:50Z end 2026-10-25T01:16:48Z elapsed 177.2s maxrss 2645 MiB exit 0
     == MODULE TCSlib/Complexity/TuringMachine
     == TIMING TCSlib/Complexity/TuringMachine: start 2026-10-25T01:16:48Z end 2026-10-25T01:16:50Z elapsed 2.6s maxrss 1952 MiB exit 0
     exit 0
     ```
3. **Probe:** 501 checks of 490 names, 0 errors.
4. **Axiom prints:** both targets `[propext, Classical.choice, Quot.sound]`; every new or
   changed private is within those three; no `sorryAx` anywhere.
5. **Lint:** 0 FAIL, 33 WARN over 40 files.
6. **File size:** 14,887 lines (the base has 1,572), 872 declarations. No line is over 100
   characters.
7. **The diff touches only the owned regions** (`logs/regions-cp7.txt`).

## Open declarations

None. Both targets are proved.
