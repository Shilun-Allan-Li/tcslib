# Ch3–4 fill campaign — §13d G4, continuation 1: the zone rebalance and extension rows (`Turing.exists_zoneExtendTM`, `Turing.exists_zoneRebalanceTM`, `Build/ZoneRebalance.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **G4's partial, landed (PR #115):** the two authorized imports, 18 checked `private zr_`
    helpers (the slot guards, the scan-index facts, the mirror, the ruler tail, and the one-cell
    leaf with its time-one contract), and two partial appendices in your file;
  - **the three API PRs, the user's ruling on the partial's escalation E1** (no unfolding; a
    published lemma for every definition your route reads):
    - the specification API (PR #112): every row contract's and every combinator's field
      equations, and the field layout's base and boundary facts;
    - the core API (PR #116), with **the zone layer's equations**: every definition of
      `Build/Zone` and `Build/ZoneTape` now has lemmas covering every input;
    - the brief-inventory API (PR #118), whose second commit was made for this continuation: the
      contract layer's predicates as `_iff`s (`round_iff`, `segment_iff`, `headBox_iff`,
      `Cfg.sameOutside_iff`, `Contract.traj_iff`), `roundOrbit_zero`, the round-contract hull
      formulas and `Cfg.bindState`'s fields;
  - the G2–G4 statement gate's rulings, the walk gate's convention, and the hosts survey, as in
    the first brief (`briefs/s13d-fill-g4.md`);
  - the fill-agent environment addendum `briefs/fill-environment-addendum.md`, and the
    declaration-keyed copy-text screen v3 `audits/evidence/retrofit/copy-text-screen-v3.py`;
  - **this round's inputs** (`audits/evidence/s13d-g4-cont1/`): the pre-ship overlay and its
    generator, the import probe, and the screen population. Also the order list
    `briefs/orders/s13d-fill-g4-cont1.txt`, the base sorry set, the screen base and the pre-ship
    log (`audits/logs/s13d-fill-g4-cont1-*`).
- If Lean cannot start, follow `briefs/fill-environment-addendum.md` exactly.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/s13d-g4-cont1 @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-s13d-g4-cont1.zip`. It contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - the bootstrap and final sweep logs and the axiom log;
  - both screen outputs, and `SHA256SUMS`.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #118** (⟨BASE-LEAN⟩). The inputs commit
  adds no Lean change. Lines in this brief are those of that tree. `Build/ZoneRebalance.lean` is
  the partial's (571 lines; 18 public, 18 private). Every probe and measurement below was run
  there, against the olean snapshot of #118's replays (`oleans-lbapi2`).
- **In flight, merging after your base and invisible to it:**
  - U2-S (`UniversalK`), B6 F5 (`Build/InputDevice`), the B6 F3 continuation
    (`SpaceComplexity/WindowClock`), the canonizer's continuation 6 (`CodeSimulator`);
  - MIG-12 (`Build/CfgRecord`), if issued.

  Cite nothing these add.

## Parallel batches this round

None in `Build/ZoneRebalance.lean`. G5 (the simulation theorem) is stated after this fill.

## What this is

**G4's fill, continued: the two machine rows of the Hennie–Stearns zone layer** ([AB09] §1.7;
`machine-library-design.md` §13d, decisions 13d.2–13d.4).
- The first delivery (`fill-s13d-g4.zip`; review `audits/evidence/s13d-g4-fill/delivery-review.md`)
  proved a private kit and stopped on escalation E1: the row contracts' fields and the layout
  data could be read only by unfolding.
- **E1 is ruled (user, 2026-10-16): not by unfolding but by published lemmas**, which the three API
  PRs supply. **Ground rule 10 now forbids unfolding any other file's definition, the zone layer
  included.** The first brief's permission to unfold `Build/Zone`'s and `Build/ZoneTape`'s pure
  definitions is withdrawn: they have lemmas now.
- Two targets, as before:
  - **the extension row** `exists_zoneExtendTM`: lay out level `ℓ` on every track, half full of
    virtual blanks;
  - **the rebalance row** `exists_zoneRebalanceTM`: for a direction and a track, realize the
    total guarded cascade at the scanned index, or report `short`.

Both statements are frozen. They are two-tape machines over `Turing.ZoneSym k`: tape `0` is the
zoned tape, tape `1` a blank scratch tape (`Turing.zoneRowPre`). **No component may add a tape**
(the G2–G4 gate's obligation 3).

**User decisions that stand (2026-10-15):** one brief in two phases (the kit and the extension row,
then the rebalance row), continued by continuations; exactly the two imports already added.

**Read first:**
- both rows' docstrings: their fill plans bind where this brief does not refine them;
- the partial's kit (lines 127–350) and its two appendices;
- the first brief's §"The route", which this brief repeats below with the API's lemmas named;
- `Build/ZoneTape.lean` and `Build/Zone.lean` **through their lemmas**: the layout, inner packing,
  `zoneSlotOf`/`zoneSlotSet`, the word lemmas, `zonedTape_extend`, `zonedTape_zero`/`_of_pos`/`_of_neg`;
- in `Build/Contract/Basic`: `Contract.ofSegment`, `Segment`, `Round`, `Round.iterate`,
  `RoundContract.release`, with their `_iff`s and field equations.

**Pre-ship check** (maintainer, at the base, against `oleans-lbapi2`;
`audits/logs/s13d-fill-g4-cont1-preship.log`):
- **The overlay** (`audits/evidence/s13d-g4-cont1/ZoneRebalanceOverlay.lean.txt`, generator
  `tools/mkoverlay.py` with `tools/home.lean.txt`): `ZoneRebalance.lean` with the two recommended
  layout bridges at the home. **0 errors, 0 non-sorry warnings, 4 sorry warnings:** the two
  bridge stubs and the two rows. The generator pins both rows byte for byte and undoes its edit.
- **The import probe** (`G4C1ImportProbe.lean.txt`, 338 `#check`s): every public declaration this
  brief cites resolves from your file's context. 0 errors, 0 warnings. **Re-run it after your
  delivery.**
- **The inventory** (`audits/evidence/brief-api/`, PR #118's gate): every definition in the
  statements the probe lists has a published lemma, or is a primitive of the machine model, or is
  your file's own.

## Owned regions and targets (modify these and nothing else)

| # | File:line | Target | Phase |
|---|---|---|---|
| 1 | `Build/ZoneRebalance.lean:438` | `Turing.exists_zoneExtendTM` (frozen statement) | 1 |
| 2 | `Build/ZoneRebalance.lean:396` | `Turing.exists_zoneRebalanceTM` (frozen statement) | 2 |

Your regions:
- **(a) the home**, lines 127–350: after `Turing.zoneRowHi` and up to the section header
  `/-! ### The rows -/` (351). It holds the partial's 18 `zr_` declarations and your new
  `private` declarations.
  - You may **adjust the `zr_` helpers' statements or proofs, or remove them**: they are private,
    and none is used yet. Report each change.
  - **Four of them must be re-pointed** (ground rule 10; see below).
  - `private` only, and no `section`, `open` or `variable` that leaks past the home.
- **(b) the rebalance row's body**, the `sorry` on line 408, and its appendix paragraph
  (lines 391–395): rewrite it as **"Fill appendix (§13d G4)"** for the final state, before the
  docstring's closing ` -/`.
- **(c) the extension row's body**, the `sorry` on line 448, and its appendix paragraph
  (lines 431–437), likewise.

Everything else is frozen: the module header and imports, the data, endpoints and envelopes
(lines 68–126), both rows' statements and the docstring text before the appendices, the proved
endpoint lemmas (450–571), and every other file. The maintainer updates the module's status text
at integration.

### The partial's helpers that unfold another file's definition (re-point them)

Measured at the base (`audits/evidence/s13d-g4-cont1/repoint.md`, with the lines):

| Helper | What it unfolds | Re-point to |
|---|---|---|
| `zr_read_slot` | `zoneSlotOf`, by `rfl` | `Turing.zoneSlotOf_inr` |
| `zr_capacity_pos` | `zoneCapacity`, by elaboration (`Nat.mul_pos` on its body) | `Turing.zoneCapacity_eq` |
| `zr_ruler_length` | `zoneCapacity` (`simp only [zoneCapacity, …]`) | `Turing.zoneCapacity_eq` |
| `zr_mirror_tape` | `zonedTape` and `ZoneContents.swap` (`simp only [zonedTape, …]`, `rfl`) | `Turing.zonedTape_zero`, `zonedTape_of_pos`/`_of_neg`, `zoneCellAt_eq`, `ZoneContents.swap_left`/`_right`/`_home` |

`zr_zonePos`, `zr_cellTM`, `zr_cellPost` and `zr_cellContract` are your file's own, and may be
unfolded. `zr_cell_step`'s `rfl` is its own table's equation, which rule 10 allows for a leaf
defined in your file.

### The recommended layout bridges (Recommended shape; you may restate them)

`tools/home.lean.txt` holds two stubs, as in the first brief:
- **`zonedTape_right_fields`:** from home, the right side is the field layout
  `[home cell] :: List.ofFn (zoneCells true z)`.
- **`zonedTape_left_fields`:** the left zones read left to right
  (`List.ofFn fun i => (zoneCells false z i.rev).reverse`) end at cell `-2`, with the separator
  at `-1`.

They let the seek family's field-layout contracts run on the zoned tape:
- `seekEndTM_contract` from home stops at `zoneStart ℓ`, the new right zone's first cell;
- `seekStartTM_contract` from home stops at the left layout's first cell.

**They are provable without unfolding now:** the layout side by `fieldsTape_*`, `fieldOffset_zero`
and `joinFields_*` (#112); the zoned side by `zonedTape_right_word`/`_left_word`,
`zonedTape_right_sep`/`_left_sep`, `zonedTape_blank_outside` and `zoneCells_eq` (#116). **Insert
each only once proved** (as stated or restated). A partial never adds an open admission.

### The walk's convention (binding; walk gate, finding 1)

`walkTM` moves the moved heads `|w| + 1` cells: one past the ruler's delimiter. **For a
displacement `m ≥ 1`,** step the ruler head once alone (the one-cell leaf), then walk over the
ruler's tail, of length `m - 1` (`zr_ruler_tail` gives the walk's premise for it). The other heads
then move exactly `m`, monotonically. Displacement `0` is a separate stationary branch. Cost the
ruler's restoration and every control transition.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2; the survey's §2)

- **Iteration** over levels, zones or marks: **`Turing.Round.iterate`** (index-free, so the level
  may vary per round), or `Turing.RoundContract` where one index suffices, released into a
  contract by `Turing.RoundContract.release`. **No counter tape, no private loop host.**
  - Build each round by **`Turing.round_iff`** when it has more than one escape or a head
    relation (the rebalance scan has both). `Turing.Round.of_cut` covers only one escape with the
    trivial relation.
  - `Round.iterate` returns a `Turing.Segment`. Read it by `segment_iff` and weaken it by
    `Segment.mono`.
- **The rows' contracts.** Each target asks for a contract with prescribed `pre`, `post`, `lo`
  and `hi`. Build it by **`Turing.Contract.ofSegment`** at exactly those fields, from a segment
  family in the `HeadBox` of `zoneRowLo`/`zoneRowHi` (`headBox_iff`). Obtain the segments by
  composing contracts (`Contract.segment`, `Segment.trans`) and rounds.
- **Composition:** `Turing.Contract.seq`, `Contract.inPhase`, `Contract.branch`, `Contract.trans`,
  with `Contract.Traj.seq` and `Contract.Frames.seq`. Read every result through its field
  equations (`*_pre`, `*_time`, `*_post`, `*_lo`, `*_hi`); `inPhase`'s endpoint through
  `Cfg.bindState_*`. Never hand trace a whole row.
- **The rows** (all public and proved; read through their field equations):
  - the column moves, by the mapped copy and transfer as contracts (`copyMapTM_contract`,
    `transferMapTM_contract`), with `extract := zoneSlotOf t` and `merge := zoneSlotSet t`;
  - the ruler, `walkTM_contract`;
  - zone to zone, `skipTM_contract` and `skipBackTM_contract`;
  - the layout ends, `seekEndTM_contract` and `seekStartTM_contract`, through the bridges;
  - re-packing on scratch, `scanTM_contract` with `scanMap`/`scanShift`, read through
    `scanResult_map`, `scanResult_shiftRight`, `scanResult_shiftLeft`;
  - cleanup, `clearTM_contract`.
- **Leaves you may write:** the partial's one-cell leaf (`zr_cellTM`, `zr_cellContract`) covers
  the one-cell move, the one-slot guard test and the one-cell write. Write another leaf only if it
  does not, with a docstring saying why no public row serves it.
- **Promotion candidates** (list each with its contract in `REPORT.md`; notes only): the one-cell
  leaf, the layout bridges, any ruler builder, the mirror.

### The route (binding where it names a row; otherwise recommended)

As in the first brief, unchanged except that every fact about another file's definition is read
through its published lemma.

**The scratch tape.** It is blank at entry, with its head anywhere (`zoneRowPre`), and must be blank
again at the exit with its head back (both posts keep `d.workTapes 1` and every head).
- Lay out what you need as delimited words, separated by blanks: rulers, a buffer for a column, a
  unary zone count.
- Clear each with `clearTM_contract` before the exit.
- The tape-1 envelope is the time-implied one (`zoneRowHi`, ruling 8).

**Phase 1, the extension row** (`exists_zoneExtendTM`; time `O(2^ℓ + 1)`). Its endpoint is
`zonedTape_extend`: the two new zones each hold `inr (fun _ => some none)` (a stored virtual blank
on every track) in their inner `2^ℓ` slots, and `inr (fun _ => none)` (all `⊠`) in their outer
`2^ℓ` (`zr_extend_cell`).
1. **`ℓ = 0`:** finite control writes the two cells on each side (cells `±2`, `±3`;
   `zoneStart 0 = 2`), by the one-cell leaf.
2. **`ℓ ≥ 1`, the right side:**
   - `seekEndTM` from home to `zoneStart ℓ`, through the right bridge;
   - `skipBackTM` to zone `ℓ - 1`'s start;
   - a mapped copy of that zone onto scratch as a ruler of `cap(ℓ - 1) = 2^ℓ` cells
     (`zr_ruler_length`);
   - `skipTM` back to `zoneStart ℓ`;
   - the mapped copy from the ruler onto tape `0` with constant merge `inr (fun _ => some none)`,
     the inner half;
   - the adjusted walk by `2^ℓ`;
   - the ruler head back by `skipBackTM`;
   - the mapped copy with merge `inr (fun _ => none)`, the outer half.
3. **Return home.** Home is the **unique one-cell field** (every zone has `cap ≥ 2`). Either
   `skipBackTM` rounds, each ending in a one-slot test, as a `Round.iterate` loop that escapes at
   home; or keep the right side's distance on scratch and walk back with it.
4. **The left side**, the mirror: `seekStartTM` from home, through the left bridge, to the left
   layout's first cell. The new left zone's inner half is at `[-(zoneStart ℓ + 2^ℓ - 1), -zoneStart ℓ]`,
   its outer half further out. The mapped copies write rightward, so place the head at the outer
   end first: two adjusted walks left by `2^ℓ`. Write outer then inner.
5. **Clear the ruler and return home.** Each phase is `O(2^ℓ)` (`zr_extent_cost`). The frames come
   from `zoneExtendPost_frames`.

**Phase 2, the rebalance row** (`exists_zoneRebalanceTM`; time `O(2^{i₀} + 1)`, with
`i₀ = zoneShiftIndex dir (z t)`).
- **The specification is the pure cascade, exactly:** `zoneRebalance dir (z t)` on track `t`, every
  other track unchanged (`zonedTape_update_slot` keeps them).
- **The scan.** Walk outward on the feeding side (right for `dir = true`), zone by zone (`skipTM`).
  In each zone, test the innermost slot of track `t` (`zr_inner_empty_iff`). The first nonempty
  zone is `i₀` (`zr_scan_index`). Two consecutive blanks (the layout's end) mean `short`: rewind
  and exit, with the tape unchanged (`zr_scan_short`; the post's identity branch). This is a
  `Round.iterate` loop with **two escapes**: build its rounds by `round_iff`.
  - *Recommended:* record a **unary zone count** on scratch while scanning, one mark per zone
    crossed: a word of `i₀ + 1` cells, written contiguously by the one-cell leaf. That count, not
    a distance ruler, is how the other side finds level `i₀`.
- **The cascade** at `i₀` (`zoneCascadeRight_eq`, or for `dir = false` its mirror through
  `ZoneContents.swap` and `zr_mirror_tape`): the descending pairs `i₀, …, 1`, the home move, the
  ascending pairs `1, …, i₀`.
  - **The pair at level `i`** is `zoneStepPair i` (`zoneStepPair_eq`):
    - **`zoneShiftIn` on the right:** if `R_{i-1}` is empty on track `t`, move `R_i`'s first
      `2^(i-1)` stored cells into `R_{i-1}`;
    - **`zoneShiftOut` on the left:** if `L_{i-1}` is full (its outermost slot occupied,
      `zr_outer_full_iff`) and `L_i` has room for `2^(i-1)` more (`zr_room_iff`), move
      `L_{i-1}`'s outer half onto `L_i`'s inner end.

    Read both through `zoneShiftIn`'s and `zoneShiftOut`'s field equations and
    `zoneShiftInW_eq`/`zoneShiftOutW_eq`.
  - **Recommended reordering, proved pure first.** The right and left operations touch disjoint
    zones, with guards on their own sides. A pass can therefore do every right-side step of its
    levels, cross home once, and do the left-side steps, using the zone count to reach level `i₀`
    on the left.
    - Prove that the reordered composition equals `zoneCascadeRight` once, as a pure private
      lemma, before using it. Cite `Build/Zone`'s cascade lemmas; do not re-derive them.
    - The home move (`zoneMove_true`/`_false`) sits between the passes, with its guard on `L_0`'s
      room.
  - **A guard** reads one slot at an offset inside a zone: the innermost, the outermost, or
    `cap_i - 2^(i-1)` from the inner end. Reach the offset with the adjusted walk over a ruler,
    and test with the one-cell leaf.
  - **A move** is a column operation on the two zones concerned:
    - copy track `t`'s column to scratch (`copyMapTM_contract`, `extract := zoneSlotOf t`);
    - re-pack it there (`scanTM_contract`; the stored cells' new split);
    - copy it back (`merge := zoneSlotSet t`, `zoneSlotOf_slotSet_self`/`_ne`), which keeps the
      other tracks.

    `2^(i-1)` is `cap(i - 2)`, zone `i - 2`'s length, for `i ≥ 2` (a mapped copy of that zone is
    the ruler), and `1` at `i = 1`. Inner packing means "the first `m` stored cells" are the
    innermost `m` slots.
- **Cost.** Level `i` costs `O(2^i)`, the sum is `O(2^{i₀})` (`zoneCascade_cost_le`), and the scan
  is `O(2^{i₀})`.
- **The envelope.** The zoned head stays within `zoneStart (i₀ + 1)` of home (`zoneRowLo`/`Hi`);
  check the outermost slot reads and the separator after zone `i₀`.
- **The frames** come from `zoneRebalancePost_frames`.

### Phases (for a partial; ground rule 9)

0. Done in the first delivery: the kit (18 `zr_` helpers). **Re-point the four** before anything
   else.
1. **Phase 1:** the layout bridges (proved and inserted), any ruler builder, and
   `exists_zoneExtendTM` proved.
2. **Phase 2:** `exists_zoneRebalanceTM` proved. Within it, report which of these are done: the
   scan with `short`, the pair step at one level, the passes, the home move, the cleanup.

A partial may leave only targets open. **Add no new admission:** a helper is inserted only once
proved. The freeze check for a partial is the axiom walk: `sorryAx` reaches each row only through
its own open body.

## Gate guidance (binding)

- **The G2–G4 statement gate's rulings** stand (`audits/s13d-g24-statements-resolutions.md`):
  - existential rows now, named machines at fill (ruling 5): your machines are private and listed
    as promotion candidates;
  - the time-implied scratch envelope (ruling 8).
- **Obligation 3** is discharged: the survey identified the hosts, and the walk gate filled the one
  missing leaf. Do not write a private host.
- **The walk gate's carried note:** ruler construction and doubling, scratch-buffer coexistence,
  cleanup and the complete geometric cost are this fill's obligations, under the public round and
  composition hosts.

## Cited infrastructure (public and proved at the issue commit; all in `G4C1ImportProbe.lean.txt`)

The probe's 338 names, in four groups:
- G4's first-round probe (94 names): the rows' data, endpoints, envelopes and frames, the pure
  zone layer, the zoned carrier, the rows as contracts, composition and iteration;
- the names this brief cites;
- the field equations and layer lemmas the route reads (#112's contract and combinator fields
  and layout facts; #116's zone-layer equations);
- #118's lemmas and the composition bridges (`Contract.ofSegment` and its fields,
  `Contract.segment`, the step lemmas).

**Proved modulo, exactly:** none. A complete delivery has no `sorryAx` in either target.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(c) of `Build/ZoneRebalance.lean`. List every new
   or changed declaration with its role.
2. **Statement freeze** over both targets and every landed public declaration: no renames,
   re-signatures, restatements or attribution edits. The `zr_` helpers are private and may change
   (region (a)).
3. **No new public declaration.**
4. **Escalation** on anything unprovable as stated, including a cited row or bridge that does not
   compose as the route says: stop on that item, record the obstruction, and continue with the
   rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Unchanged (the two authorized in the first round are in). No TCSlib import may be
   added. A Mathlib import only if a needed lemma requires it; flag it.
7. **One proof per shared argument.** Never write a second seam, phase host, round iteration, trace
   or embedding transport. Never re-walk a row's trace: compose the contracts.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public and
   private declaration counts (base: 571 lines; 18 public, 18 private).
9. **Continuation budget.** A partial zip states the phase reached, the open declarations (each with a
   literal "Proof sketch"), and both targets' axiom walks. A partial is expected and fine; an
   unreported gap is not.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file**, `Build/Zone` and `Build/ZoneTape` included.
      Read every definition through its published lemmas: the specification API (#112), the core
      API with the zone layer (#116), the brief-inventory API (#118), and the landed lemmas the
      probe lists.
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`) are read through their existing lemmas. Unfold `step` and `Action.apply`
      only for a leaf defined in your own file.
    - Your own file's definitions may be unfolded (`zoneRowPre`, `zoneRebalancePost`, … and your
      privates).
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need.
    - List every declaration you cite outside your file in `REPORT.md`. If you cite more than the
      probe's list, add them to a copy of the probe and run it.
11. **MIG-1 compatibility.**
    - Cite none of the six R3 canonical rows (`copyTM_run`, `transferTM_run`, `clearTM_run`,
      `compareTM_run`, `incrementTM_run_succ`, `incrementTM_run_overflow`); use their framed or
      contract forms.
    - Cite no private declaration of `Build/Catalog`.
    - Keep your new privates under the `zr_` prefix.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`audits/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**).
- **The population** is the first brief's 10 files
  (`audits/evidence/s13d-g4-cont1/screen-population.txt`):
  - your file;
  - the files the route cites: `Build/Zone`, `Build/ZoneTape`, `Build/Catalog`,
    `Build/Contract/Catalog`, `Build/Contract/Basic`, `Build/Contract/Seam`, `Build/Seam`,
    `Simulation`;
  - the known hazard `Build/RecordTable`.
- **The screen** is the declaration-keyed `audits/evidence/retrofit/copy-text-screen-v3.py`, on the
  repository paths.
- **The base**, at the issue tree, is `audits/logs/s13d-fill-g4-cont1-screen-base.txt`:
  **795 declarations, 437 pairs, 127,810 characters** (MEASURED; about 5 minutes). The overlay's stubs have bodies under the 60-character floor.

```sh
P=audits/evidence/s13d-g4-cont1
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side. Nothing is
  pre-disclosed.
- **Known hazards:**
  - **`Build/RecordTable`'s field copy** (`exists_fieldsCopyTM`, outside your import context, and
    its private `rt_copyMachine`: copy, skip, recurse, skip back). Your layout walks have the same
    shape: cite the rows and compose, and do not transcribe it.
  - **B6 F3's clock writer** (in flight, private in `WindowClock`), if you build a contiguous copy
    of a layout's cells. It is not visible to you. Report such a helper as a promotion candidate;
    the maintainer reconciles the two.
  - `Build/Zone`'s pure cascade proofs (`zoneSide_cascadeRight` and its family): your pure
    reordering lemma cites them and does not re-derive them.
  - the mirror (`dir = false`): derive it through `ZoneContents.swap` and `zr_mirror_tape`, or
    factor it by a direction parameter. A 90% pair between the two directions is a copy.
  - **A screen artifact to expect:** the screen runs a declaration's text up to the next
    declaration, so a short lemma placed just before a `section` or `namespace` takes in its
    `variable` line. Such a pair is not a copy; show its shared text.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy: factor it.
  Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/s13d-fill-g4-cont1.txt` (**80 modules**: the upstream
  closure of your owned file and of every module downstream of it, without the root `TCSlib`; one
  module is downstream of it, the `TuringMachine` facade):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/s13d-fill-g4-cont1.txt )
  ```

  **The base sorry-warning set has 35 entries in 15 modules**
  (`audits/logs/s13d-fill-g4-cont1-base-sorries.txt`, one per declaration). Yours are
  `Build/ZoneRebalance`'s two. Record the base list by name first, and report any difference.
- **Final checks:**
  1. `Build/ZoneRebalance`: zero errors, no sorry warning (for a partial, exactly the open
     targets'), and no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's minus
     yours (**33** for a complete delivery).
  3. Re-run `G4C1ImportProbe.lean.txt`: 0 errors.
- **Axiom prints** (in a scratch copy of your module with `#print axioms` appended) for both targets
  and every new or changed private: within `[propext, Classical.choice, Quot.sound]`, no `sorryAx`
  for a complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`, 0 FAIL
  (base: 0 FAIL, 32 WARN over 37 files). No new line over 100 characters.

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your two targets:
- MIG-1 stage S's sorried specs (`Simulation`, `Composition`, `Build/Wrappers`, `Build/Loop`,
  `Encoding`, `ClassP/TimeConstructible`, `Build/Primitives`);
- `Build/NDHost`, `Build/InputWindow`, `Build/RecordTable`'s four rows;
- `CodeSimulator`, `NDCodeSimulator`, `UniversalK`, `Build/InputDevice` (rows in flight in other
  fills).

If a proof seems to *need* one of these beyond a named citation, that is an escalation, not a
license.

## REPORT.md checklist

- [ ] The phase reached; the base hash and the ancestor check.
- [ ] The four re-pointed helpers, each with the lemmas it now cites; every other changed or
      removed `zr_` helper.
- [ ] Every new declaration with its role; the bridges as recommended or restated; any further
      leaf with its reason; the flagged appendices.
- [ ] The scratch layout you used, and the walk convention as applied.
- [ ] Promotion candidates and escalations, or "none".
- [ ] Rule 10: the declarations cited outside your file, and the probe re-run; a grep of your diff
      for `unfold`, `delta`, `simp only [` and `rfl` on another file's definition, each hit
      explained. Rule 11: a grep of your diff for the six R3 rows.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line. The diff touches only your
      owned regions.

## Known pitfalls at this pin (hard-won)

- **Two blanks in a row mark the layout's end; one blank is a separator.** The home is the only
  one-cell field: every zone has `cap ≥ 2`. `zoneStart 0 = 2`, so the separators around home are
  at `±1`.
- **Inner packing:** stored cells sit at each zone's inner end, and `⊠` (`none` in a slot) fills the
  rest.
  - A zone is empty on a track exactly when its innermost slot is `⊠`, and full exactly when its
    outermost slot is occupied (the partial's `zr_inner_empty_iff`, `zr_outer_full_iff`).
  - A stored **virtual blank** is `some none`, not `⊠`.
- **The left side reads reversed** (`zonedTape_left_word`): the left zone `i`'s inner end is at
  `-zoneStart i`, its outer end at `-(zoneStart i + cap_i - 1)`. A rightward mapped copy writes
  from the outer end.
- **The mapped copy writes `merge (old destination cell) (extract source cell)`** and returns both
  heads (`2|w| + 2` steps). The walk moves `|w| + 1` (the convention above).
- **Contracts fix `Γ : Type`;** `ZoneSym k` is one. A `Contract`'s cut includes time `0`, so an
  entry is never an exit.
- **`Round.iterate`** takes a round-time function on configurations and a round hypothesis per
  orbit point; the level can be read off the configuration. Its round `0` is the start
  (`roundOrbit_zero`), and each next round starts where the last ended (`roundOrbit_succ`).
  `RoundContract`'s orbit lemmas fix one index.
- **`Contract.ofSegment`** wants each segment's relation to be exactly the `HeadBox` of the `lo`/`hi`
  you give it: weaken a composed segment's relation by `Segment.mono`, using `headBox_iff`.
- `Contract.inPhase`'s endpoint is a `Cfg.bindState`: read its fields by `Cfg.bindState_state` and
  the other four.
- `omega` with products and powers as atoms (`ring` first). `zoneStart_eq : zoneStart i =
  2^(i+1) + i`, `zoneStart_succ` and `zoneCapacity_eq : zoneCapacity i = 2 * 2^i` are the
  arithmetic. The linter needs a literal "Proof sketch" before every `sorry` (partial only).
