# Ch3–4 fill campaign — §13d G4, continuation 2: the zone rebalance and extension rows (`Turing.exists_zoneExtendTM`, `Turing.exists_zoneRebalanceTM`, `Build/ZoneRebalance.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **G4's two partials, landed:**
    - PR #115 (the first round): the two authorized imports and 18 checked `private zr_` helpers
      (the slot guards, the scan-index facts, the mirror, the ruler tail, and the one-cell leaf
      with its time-one contract);
    - PR #125 (continuation 1): the four inherited helpers re-pointed to published equations, and
      13 new private helpers: the two layout bridges (`zr_zonedTape_right_fields`,
      `zr_zonedTape_left_fields`), their offset formulas, the comparison lemma, both seek
      preconditions, the pure side-pass reordering `zr_cascade_passes`, and the left route's
      arithmetic `zr_left_two_walks`;
  - **the three API PRs** (the user's ruling of 2026-10-16: no unfolding; a published lemma for
    every definition your route reads): the specification API (PR #112), the core API with the
    zone layer's equations (PR #116), and the brief-inventory API (PR #118: the contract layer's
    `_iff`s, `roundOrbit_zero`, the round-contract hull formulas, `Cfg.bindState`'s fields);
  - the G2–G4 statement gate's rulings, the walk gate's convention, and the hosts survey, as in
    the first brief (`campaign/fills/s13d/briefs/s13d-fill-g4.md`);
  - **continuation 1's records:** the worker's report
    (`campaign/fills/s13d/reports/g4-cont1-REPORT.md`), the maintainer's review
    (`campaign/gates/44-s13d-g4-cont1-fill/evidence/REVIEW.md`) and the landing gate's findings,
    resolutions and review (`campaign/gates/44-s13d-g4-cont1-fill/`);
  - the fill-agent environment addendum `campaign/standards/fill-environment-addendum.md`
    (**v2**: Part 1, the resources and the cache, applies on every host), and the
    declaration-keyed copy-text screen v3 `scripts/copy-text-screen-v3.py`;
  - **this round's inputs** (`campaign/fills/s13d/inputs/s13d-fill-g4-cont2/`): the import probe and
    the screen population. Also the order list `campaign/fills/s13d/orders/s13d-fill-g4-cont2.txt`,
    the base sorry set, the screen base and the pre-ship log
    (`campaign/fills/s13d/logs/s13d-fill-g4-cont2-*`).
- **Before anything else, run Part 1 of `campaign/standards/fill-environment-addendum.md`**: the
  preflight, with its stop rule (E-RES). Continuation 1's final sweep ran out of disk at module 41.
  If Lean cannot start, follow Part 2 exactly.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/s13d-g4-cont2 @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-s13d-g4-cont2.zip`. It contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - the bootstrap and final sweep logs and the axiom log;
  - both screen outputs, and `SHA256SUMS`.
- **Checkpoint zips.** Each checkpoint below that you complete may land on its own. After each,
  commit it and write `fill-s13d-g4-cont2-cp<N>.zip` with the same contents as of that commit
  (the final sweep may be the owned file's check only), so that a lost workspace loses at most one
  checkpoint. Deliver the latest checkpoint zip if the session ends early.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #124** (`dac6b3b0`, #124's merge). The
  inputs commit adds no Lean change. Lines in this brief are those of that tree.
  `Build/ZoneRebalance.lean` is continuation 1's landing (861 lines; 18 public, 31 private). Every
  probe and measurement below was run there, against the olean snapshot of #124's replay
  (`oleans-lseam2`).
- **In flight, merging after your base and invisible to it:** #129
  (`Diagonalization/NTimeHierarchy`), #130 (`TuringMachine/UniversalK`), #131
  (`TuringMachine/CodeSimulator`), #132 (`Build/Primitives`, `Simulation`), and the ruler
  device's landing (`Build/InputDevice`). None touches your file; #132 changes `Simulation`,
  upstream of your file. Cite nothing they add.

## Parallel batches this round

None in `Build/ZoneRebalance.lean`. G5 (the simulation theorem) is stated after this fill.

## What this is

**G4's fill, continued: the two machine rows of the Hennie–Stearns zone layer** ([AB09] §1.7;
`machine-library-design.md` §13d, decisions 13d.2–13d.4). Two targets, as before:
- **the extension row** `exists_zoneExtendTM`: lay out level `ℓ` on every track, half full of
  virtual blanks;
- **the rebalance row** `exists_zoneRebalanceTM`: for a direction and a track, realize the total
  guarded cascade at the scanned index, or report `short`.

Both statements are frozen. They are two-tape machines over `Turing.ZoneSym k`: tape `0` is the
zoned tape, tape `1` a blank scratch tape (`Turing.zoneRowPre`). **No component may add a tape**
(the G2–G4 gate's obligation 3).

**Where the first two rounds stopped.** Both rounds produced pure-layer kit only: no machine has
been composed yet (no contract, round, ruler, scan or move). Continuation 1 proved the layout
bridges and both seek preconditions, and stopped the left route on an escalation (continuation
1's E1, renamed **cont1-E1** to avoid the first round's E1). **The review found it genuine and a
matter of route arithmetic, not of the specification** (review F2): the prescribed two
half-capacity walks stop one cell short of the new zone's outer end. This brief carries the
amendment below. **This round's first goal is a composed machine:** phase 1's contracts, in order,
each a checkpoint.

**User decisions that stand (2026-10-15):** one brief in two phases (the kit and the extension row,
then the rebalance row), continued by continuations; exactly the imports already added.

**Read first:**
- both rows' docstrings: their proof sketches bind where this brief does not refine them;
- the kit in the home (lines 127–637), and continuation 1's review (F2, and "Continuation 2
  should");
- the first brief's §"The route", which this brief repeats below with the amendments;
- `Build/ZoneTape.lean` and `Build/Zone.lean` **through their lemmas**: the layout, inner packing,
  `zoneSlotOf`/`zoneSlotSet`, the word lemmas, `zonedTape_extend`,
  `zonedTape_zero`/`_of_pos`/`_of_neg`;
- in `Build/Contract/Basic`: `Contract.ofSegment`, `Segment`, `Round`, `Round.iterate`,
  `RoundContract.release`, with their `_iff`s and field equations.

**Pre-ship check** (maintainer, at the base, against `oleans-lseam2`;
`campaign/fills/s13d/logs/s13d-fill-g4-cont2-preship.log`):
- **Your file** elaborates at the base with exactly the two targets' sorry warnings (lines 686
  and 728).
- **The import probe** (`G4C2ImportProbe.lean.txt`: continuation 1's 338 `#check`s, unchanged):
  every public declaration this brief cites resolves from your file's context. 0 errors,
  0 warnings. **Re-run it after your delivery.**
- **The inventory** (PR #118's gate, `campaign/gates/34-brief-api/evidence/inventory/`): every
  definition in the statements the probe lists has a published lemma, or is a primitive of the
  machine model, or is your file's own.

## Owned regions and targets (modify these and nothing else)

| # | File:line | Target | Phase |
|---|---|---|---|
| 1 | `Build/ZoneRebalance.lean:728` | `Turing.exists_zoneExtendTM` (frozen statement) | 1 |
| 2 | `Build/ZoneRebalance.lean:686` | `Turing.exists_zoneRebalanceTM` (frozen statement) | 2 |

Your regions:
- **(a) the home**, lines 127–637: after `Turing.zoneRowHi` and up to the blank lines before the
  section header `/-! ### The rows -/` (640). It holds the 31 `zr_` declarations and your new
  `private` declarations.
  - You may **adjust the `zr_` helpers' statements or proofs, or remove them**: they are private,
    and no public declaration uses them. Report each change. **Restate or remove
    `zr_left_two_walks`** under the amendment below.
  - `private` only, and no `section`, `open` or `variable` that leaks past the home.
- **(b) the rebalance row's body**, the `sorry` on line 698, and its status paragraph (lines
  680–685, now headed "Fill appendix (§13d G4)").
- **(c) the extension row's body**, the `sorry` on line 738, and its status paragraph (lines
  721–727), likewise.

**The two status paragraphs are public-facing library text** (gate 44, minor 3). Replace each
"Fill appendix (§13d G4)" paragraph:
- for a proved target, by a short paragraph headed `**Implementation.**` (the machine's phases and
  the rows they compose), or by nothing;
- for an open target, by a paragraph headed `**Implementation status.**` that states, in
  mathematical terms, what is proved and what is open.

Neither may carry campaign labels (brief, gate, finding or escalation names such as cont1-E1),
records paths, dates or session narrative; provenance goes in `REPORT.md`. The same holds for the
docstrings of your new declarations.

Everything else is frozen: the module header and imports, the data, endpoints and envelopes
(lines 68–126), both rows' statements and their docstring text before the status paragraphs, the
proved endpoint lemmas (740–860), and every other file. The maintainer updates the module's
status text at integration.

### The walk's convention (binding; walk gate, finding 1)

`walkTM` moves the moved heads `|w| + 1` cells: one past the ruler's delimiter. **For a
displacement `m ≥ 1`,** step the ruler head once alone (the one-cell leaf), then walk over the
ruler's tail, of length `m - 1` (`zr_ruler_tail` gives the walk's premise for it): the **adjusted
walk**. The other heads then move exactly `m`, monotonically. The **unadjusted walk** over a whole
ruler of length `|w|` moves them `|w| + 1`. Displacement `0` is a separate stationary branch. Cost
the ruler's restoration and every control transition.

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
- **Leaves you may write:** the one-cell leaf (`zr_cellTM`, `zr_cellContract`) covers the
  one-cell move, the one-slot guard test and the one-cell write. Write another leaf only if it
  does not, with a docstring saying why no public row serves it.
- **Promotion candidates** (list each with its contract in `REPORT.md`; notes only): the one-cell
  leaf, the layout bridges, any ruler builder, the mirror.

### The route (binding where it names a row; otherwise recommended)

As in the first brief, with continuation 1's review and gate 44 folded in. Every fact about another
file's definition is read through its published lemma.

**The scratch tape.** It is blank at entry, with its head anywhere (`zoneRowPre`), and must be blank
again at the exit with its head back (both posts keep `d.workTapes 1` and every head).
- Lay out what you need as delimited words, separated by blanks: rulers, a buffer for a column, a
  unary zone count.
- Clear each with `clearTM_contract` before the exit.
- The tape-1 envelope is the time-implied one (`zoneRowHi`, ruling 8).

**Phase 1, the extension row** (`exists_zoneExtendTM`; time `O(2^ℓ + 1)`). Its endpoint is
`zonedTape_extend`: the two new zones each hold `inr (fun _ => some none)` (a stored virtual blank
on every track) in their inner `2^ℓ` slots, and `inr (fun _ => none)` (all `⊠`) in their outer
`2^ℓ` (`zr_extend_cell`). **Build it in this order, as contracts; each numbered item is a
checkpoint that may land alone:**
1. **The right pass** (`ℓ ≥ 1`), one contract:
   - `seekEndTM` from home to `zoneStart ℓ`, the new right zone's first cell (through
     `zr_zonedTape_right_fields` and its seek precondition);
   - `skipBackTM` to zone `ℓ - 1`'s start;
   - a mapped copy of that zone onto scratch as a ruler of `cap(ℓ - 1) = 2^ℓ` cells
     (`zr_ruler_length`);
   - `skipTM` back to `zoneStart ℓ`;
   - the mapped copy from the ruler onto tape `0` with constant merge `inr (fun _ => some none)`,
     the inner half;
   - the adjusted walk by `2^ℓ`;
   - the ruler head back by `skipBackTM`;
   - the mapped copy with merge `inr (fun _ => none)`, the outer half.
2. **The return home**, one contract. Home is the **unique one-cell field** (every zone has
   `cap ≥ 2`). Either `skipBackTM` rounds, each ending in a one-slot test, as a `Round.iterate`
   loop built by `round_iff` that escapes at home; or keep the right pass's distance on scratch and
   walk back with it.
3. **The left pass, amended** (cont1-E1; the review's F2; gate 44's carried note):
   - `seekStartTM` from home, through `zr_zonedTape_left_fields`. Its endpoint is
     `pos − fieldOffset ws |ws|`, which with the proved left offset
     (`fieldOffset ws ℓ + 2 = zoneStart ℓ`) is **`2 − zoneStart ℓ`**: the outermost cell of zone
     `ℓ − 1`, not the new zone's first cell.
   - The new left zone occupies `[1 − zoneStart ℓ − cap ℓ, −zoneStart ℓ]` (outer end first), with
     the separator at `1 − zoneStart ℓ`. Its inner half is
     `[−(zoneStart ℓ + 2^ℓ − 1), −zoneStart ℓ]`. The mapped copies write rightward, so the head must
     first reach the outer end.
   - **The displacement from the seek's stop to the outer end is `2·2^ℓ + 1`** (one cell for the
     separator, then the zone's `2^{ℓ+1}` cells). Reach it **either** by one unadjusted walk over
     the full ruler of `2^ℓ` cells (`2^ℓ + 1`) and then one adjusted walk by `2^ℓ`, **or** by two
     adjusted walks by `2^ℓ` and one more left step of the one-cell leaf. Your choice; state it in
     `REPORT.md`.
   - **Sanity case `ℓ = 1`:** the outer end is cell `−8`. Stopping at `−7` and writing four cells
     from there would overwrite the separator at `−4`.
   - **The envelope:** the endpoint `−zoneStart (ℓ + 1) + 2` is inside `−zoneStart (ℓ + 1)`.
   - Then write outer, then inner. Prove the composition: the ruler's repositioning, the control
     cost, the cleanup and the head's restoration.
   - **The second seek** (whichever of the two seeks runs second; gate 44's note 9): state its
     precondition from the zoned head at home and from **agreement with `zonedTape z` on the cells
     it reads** (`[0, zoneStart ℓ]` on the right, `[−zoneStart ℓ, 0]` on the left), carried
     through the first pass's frame, instead of `zoneRowPre`. It needs no global scratch
     blankness.
4. **The `ℓ = 0` branch:** finite control writes the two cells on each side (cells `±2`, `±3`;
   `zoneStart 0 = 2`), by the one-cell leaf.
5. **Cleanup:** `clearTM_contract` on the ruler, and the return home.
6. **Assembly** by `Contract.ofSegment` in the `HeadBox` of `zoneRowLo`/`zoneRowHi`, with the
   frames from `zoneExtendPost_frames`. Each phase is `O(2^ℓ)` (`zr_extent_cost`).

**Phase 2, the rebalance row** (`exists_zoneRebalanceTM`; time `O(2^{i₀} + 1)`, with
`i₀ = zoneShiftIndex dir (z t)`), on the proved reordering `zr_cascade_passes`.
- **The specification is the pure cascade, exactly:** `zoneRebalance dir (z t)` on track `t`, every
  other track unchanged (`zonedTape_update_slot` keeps them).
- **The scan**, a checkpoint. Walk outward on the feeding side (right for `dir = true`), zone by
  zone (`skipTM`). In each zone, test the innermost slot of track `t` (`zr_inner_empty_iff`). The
  first nonempty zone is `i₀` (`zr_scan_index`). Two consecutive blanks (the layout's end) mean
  `short`: rewind and exit, with the tape unchanged (`zr_scan_short`; the post's identity branch).
  This is a `Round.iterate` loop with **two escapes**: build its rounds by `round_iff`.
  - *Recommended:* record a **unary zone count** on scratch while scanning, one mark per zone
    crossed: a word of `i₀ + 1` cells, written contiguously by the one-cell leaf. That count, not
    a distance ruler, is how the other side finds level `i₀`.
- **One level's guarded column move**, a checkpoint: a guard reads one slot at an offset inside a
  zone (the innermost, the outermost, or `cap_i - 2^(i-1)` from the inner end), reached by the
  adjusted walk over a ruler and tested with the one-cell leaf. A move is a column operation on
  the two zones concerned:
  - copy track `t`'s column to scratch (`copyMapTM_contract`, `extract := zoneSlotOf t`);
  - re-pack it there (`scanTM_contract`; the stored cells' new split);
  - copy it back (`merge := zoneSlotSet t`, `zoneSlotOf_slotSet_self`/`_ne`), which keeps the
    other tracks.

  `2^(i-1)` is `cap(i - 2)`, zone `i - 2`'s length, for `i ≥ 2` (a mapped copy of that zone is
  the ruler), and `1` at `i = 1`. Inner packing means "the first `m` stored cells" are the
  innermost `m` slots.
  - **The pair at level `i`** is `zoneStepPair i` (`zoneStepPair_eq`): **`zoneShiftIn` on the
    right** (if `R_{i-1}` is empty on track `t`, move `R_i`'s first `2^(i-1)` stored cells into
    `R_{i-1}`) and **`zoneShiftOut` on the left** (if `L_{i-1}` is full, `zr_outer_full_iff`, and
    `L_i` has room for `2^(i-1)` more, `zr_room_iff`, move `L_{i-1}`'s outer half onto `L_i`'s
    inner end). Read both through their field equations and `zoneShiftInW_eq`/`zoneShiftOutW_eq`.
- **The four side passes** of `zr_cascade_passes`, with the home move between them
  (`zoneMove_true`/`_false`, its guard on `L_0`'s room), using the zone count to reach level `i₀`
  on the other side. Cite `Build/Zone`'s cascade lemmas; do not re-derive them.
- **`dir = false`** through `zoneCascadeLeft_eq` and `zr_mirror_tape`, or by a direction
  parameter.
- **Cost.** Level `i` costs `O(2^i)`, the sum is `O(2^{i₀})` (`zoneCascade_cost_le`), and the scan
  is `O(2^{i₀})`.
- **The envelope.** The zoned head stays within `zoneStart (i₀ + 1)` of home (`zoneRowLo`/`Hi`);
  check the outermost slot reads and the separator after zone `i₀`.
- **The frames** come from `zoneRebalancePost_frames`.

### Phases and checkpoints (for a partial; ground rule 9)

0. Done in the first two rounds: the kit (31 `zr_` helpers). Restate or remove
   `zr_left_two_walks` under the amendment.
1. **Phase 1:** checkpoints 1–6 above, then `exists_zoneExtendTM` proved.
2. **Phase 2:** the scan with `short`; one level's guarded column move; the passes with the home
   move; the mirror; the cleanup; then `exists_zoneRebalanceTM` proved.

Report which checkpoints are done. A partial may leave only targets open. **Add no new
admission:** a helper is inserted only once proved. The freeze check for a partial is the axiom
walk: `sorryAx` reaches each row only through its own open body.

## Gate guidance (binding)

- **The G2–G4 statement gate's rulings** stand
  (`campaign/gates/22-s13d-g24-statements/resolutions.md`):
  - existential rows now, named machines at fill (ruling 5): your machines are private and listed
    as promotion candidates;
  - the time-implied scratch envelope (ruling 8).
- **Obligation 3** is discharged: the survey identified the hosts, and the walk gate filled the one
  missing leaf. Do not write a private host.
- **The walk gate's carried note:** ruler construction and doubling, scratch-buffer coexistence,
  cleanup and the complete geometric cost are this fill's obligations, under the public round and
  composition hosts.
- **Gate 44** (continuation 1's landing): the left route's amendment, the second seek's
  precondition, rule 10's two checks and the status paragraphs, all above.

## Cited infrastructure (public and proved at the issue commit; all in `G4C2ImportProbe.lean.txt`)

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
4. **Escalation, item by item.** On anything unprovable as stated, including a cited row or bridge
   that does not compose as the route says: stop **on that item only**, record the obstruction
   mathematically, and **continue with every item that does not depend on it**. Continuation 1
   stopped the left pass, but the right pass, the ruler builder and the return home did not depend
   on it and were not blocked. Two rounds have produced only pure-layer kit; this round's measure
   of progress is composed contracts.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** Unchanged. No TCSlib import may be added. A Mathlib import only if a needed lemma
   requires it; flag it.
7. **One proof per shared argument.** Never write a second seam, phase host, round iteration, trace
   or embedding transport. Never re-walk a row's trace: compose the contracts.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public and
   private declaration counts (base: 861 lines; 18 public, 31 private).
9. **Continuation budget.** A partial zip states the checkpoints reached, the open declarations
   (each with a literal "Proof sketch"), and both targets' axiom walks. A partial is expected and
   fine; an unreported gap is not.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file**, `Build/Zone`, `Build/ZoneTape` and
      `FinTM.bufferTape` included. Read every definition through its published lemmas: the
      specification API (#112), the core API with the zone layer (#116), the brief-inventory API
      (#118), and the landed lemmas the probe lists.
    - **No definitional closure either:** a `rfl`, `exact`, `show`, `decide` or `simp` step that
      closes only because another file's definition reduces counts as unfolding (continuation 1's
      F1 was one).
    - **The machine model's primitives** (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
      `Cfg.mapState`) are read through their existing lemmas. Unfold `step` and `Action.apply`
      only for a leaf defined in your own file.
    - Your own file's definitions may be unfolded (`zoneRowPre`, `zoneRebalancePost`, … and your
      privates).
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need.
    - **Self-check by both methods** (neither alone is complete): a **seal test** (a scratch copy
      of your module with `attribute [local irreducible]` on every other-file definition your
      proofs mention, which must still elaborate), and an **inspection** of every
      `rw`/`simp`/`simpa`/`unfold` argument in your diff for another file's definition.
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
(`campaign/standards/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**).
- **The population** is the first brief's 10 files
  (`campaign/fills/s13d/inputs/s13d-fill-g4-cont2/screen-population.txt`):
  - your file;
  - the files the route cites: `Build/Zone`, `Build/ZoneTape`, `Build/Catalog`,
    `Build/Contract/Catalog`, `Build/Contract/Basic`, `Build/Contract/Seam`, `Build/Seam`,
    `Simulation`;
  - the known hazard `Build/RecordTable`.
- **The screen** is the declaration-keyed `scripts/copy-text-screen-v3.py`, on the repository
  paths.
- **The base**, at the issue tree, is `campaign/fills/s13d/logs/s13d-fill-g4-cont2-screen-base.txt`:
  **808 declarations, 439 pairs, 127,994 characters** (MEASURED; about 5 minutes).

```sh
P=campaign/fills/s13d/inputs/s13d-fill-g4-cont2
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I scripts/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side. Nothing is
  pre-disclosed. **Already accepted, in-file:** `zr_pair_pass` against `zr_inPass_out` (72% and
  62%, the shared list-induction scaffold; gate 44). It needs no factoring.
- **Known hazards:**
  - **`Build/RecordTable`'s field copy** (`exists_fieldsCopyTM`, outside your import context, and
    its private `rt_copyMachine`: copy, skip, recurse, skip back). Your layout walks have the same
    shape: cite the rows and compose, and do not transcribe it.
  - **B6 F3's clock writer** (private in `SpaceComplexity/WindowClock`, not visible to you), if
    you build a contiguous copy of a layout's cells. Report such a helper as a promotion
    candidate; the maintainer reconciles the two.
  - `Build/Zone`'s pure cascade proofs (`zoneSide_cascadeRight` and its family): your proofs cite
    them and do not re-derive them.
  - the mirror (`dir = false`): derive it through `ZoneContents.swap` and `zr_mirror_tape`, or
    factor it by a direction parameter. A 90% pair between the two directions is a copy.
  - the two seek passes: factor the right and left passes through one parametrized lemma where
    their proofs coincide, rather than two near-copies.
  - **A screen artifact to expect:** the screen runs a declaration's text up to the next
    declaration, so a short lemma placed just before a `section` or `namespace` takes in its
    `variable` line. Such a pair is not a copy; show its shared text.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy: factor it.
  Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `campaign/fills/s13d/orders/s13d-fill-g4-cont2.txt` (**81 modules**: the
  upstream closure of your owned file and of every module downstream of it, without the root
  `TCSlib`; one module is downstream of it, the `TuringMachine` facade):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < campaign/fills/s13d/orders/s13d-fill-g4-cont2.txt )
  ```

  **The base sorry-warning set has 35 entries in 15 modules**
  (`campaign/fills/s13d/logs/s13d-fill-g4-cont2-base-sorries.txt`, one per declaration). Yours are
  `Build/ZoneRebalance`'s two. Record the base list by name first, and report any difference.
- **Final checks:**
  1. `Build/ZoneRebalance`: zero errors, no sorry warning (for a partial, exactly the open
     targets'), and no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's minus
     yours (**33** for a complete delivery).
  3. Re-run `G4C2ImportProbe.lean.txt`: 0 errors.
- **Axiom prints** (in a scratch copy of your module with `#print axioms` appended) for both targets
  and every new or changed private: within `[propext, Classical.choice, Quot.sound]`, no `sorryAx`
  for a complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`, 0
  FAIL (base: 0 FAIL, 30 WARN over 38 files). No new line over 100 characters.

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your two targets:
- MIG-1 stage S's sorried specs (`Simulation`, `Composition`, `Build/Wrappers`, `Build/Loop`,
  `Encoding`, `ClassP/TimeConstructible`, `Build/Primitives`);
- `Build/InputWindow`, `Build/RecordTable`'s four rows, `Build/SeamLayout`;
- `CodeSimulator`, `NDCodeSimulator`, `UniversalK`, `Build/InputDevice` (rows in other fills).

If a proof seems to *need* one of these beyond a named citation, that is an escalation, not a
license.

## REPORT.md checklist

- [ ] The preflight's numbers (addendum v2, Part 1).
- [ ] The checkpoints reached; the base hash and the ancestor check; the checkpoint zips written.
- [ ] Every new, changed or removed `zr_` declaration with its role; `zr_left_two_walks` restated
      or removed; any further leaf with its reason; the two status paragraphs.
- [ ] The left pass: the displacement option chosen, and the `ℓ = 1` case checked.
- [ ] The scratch layout you used, and the walk convention as applied.
- [ ] Promotion candidates and escalations (each stated mathematically), or "none".
- [ ] Rule 10: the declarations cited outside your file, and the probe re-run; the seal test's
      list and result; the argument inspection, each hit explained. Rule 11: a grep of your diff
      for the six R3 rows.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line. The diff touches only your
      owned regions.

## Known pitfalls at this pin (hard-won)

- **Two blanks in a row mark the layout's end; one blank is a separator.** The home is the only
  one-cell field: every zone has `cap ≥ 2`. `zoneStart 0 = 2`, so the separators around home are
  at `±1`.
- **The two seeks stop differently.** `seekEndTM` from home stops at `zoneStart ℓ`, the new right
  zone's first cell, past the separator. `seekStartTM` stops at `2 − zoneStart ℓ`, inside the
  layout (zone `ℓ − 1`'s outermost cell), so the left side needs the extra `2^ℓ + 1` above.
- **Inner packing:** stored cells sit at each zone's inner end, and `⊠` (`none` in a slot) fills the
  rest.
  - A zone is empty on a track exactly when its innermost slot is `⊠`, and full exactly when its
    outermost slot is occupied (`zr_inner_empty_iff`, `zr_outer_full_iff`).
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
- **`Contract.ofSegment`** wants each segment's relation to be exactly the `HeadBox` of the
  `lo`/`hi` you give it: weaken a composed segment's relation by `Segment.mono`, using
  `headBox_iff`.
- `Contract.inPhase`'s endpoint is a `Cfg.bindState`: read its fields by `Cfg.bindState_state` and
  the other four.
- `omega` with products and powers as atoms (`ring` first). `zoneStart_eq : zoneStart i =
  2^(i+1) + i`, `zoneStart_succ` and `zoneCapacity_eq : zoneCapacity i = 2 * 2^i` are the
  arithmetic. The linter needs a literal "Proof sketch" before every `sorry` (partial only).
