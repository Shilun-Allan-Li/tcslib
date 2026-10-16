# Ch3–4 fill campaign — §13d G4: the zone rebalance and extension rows (`Turing.exists_zoneExtendTM`, `Turing.exists_zoneRebalanceTM`, `Build/ZoneRebalance.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **the §13d zone layer:**
    - G1 (the alphabet-generic library);
    - G2's mapped sweeps, filled (PR #108);
    - G3's zoned carrier `Build/ZoneTape` (PR #106);
    - **your two rows as gated statements** (`Build/ZoneRebalance`, PR #106; the G2–G4 statement
      gate `audits/s13d-g24-statements-findings.md`, PASS 0/0/5).
  - **G4's ruler and contract wrappers** (PR #109): the lockstep walk `Turing.walkTM` with its
    framed row, `Turing.framedContract`, and the walk, skip, skip-back, seek-end, seek-start and
    scan contracts in `Build/Contract/Catalog`.
    - Their gate, `audits/s13d-walk-statements-findings.md` (PASS 0/0/2), carries one convention
      adjustment into this brief (§"The walk's convention").
  - **the hosts survey** `audits/evidence/s13d/g4-hosts/G4-HOSTS-SURVEY.md`;
  - the fill-agent environment addendum `briefs/fill-environment-addendum.md`, and the
    declaration-keyed copy-text screen v3 `audits/evidence/retrofit/copy-text-screen-v3.py`;
  - **this round's inputs** (`audits/evidence/s13d-g4-fill/`): the pre-ship overlay and its
    generator, the import probe, and the screen population. Also the order list
    `briefs/orders/s13d-fill-g4.txt`, the base sorry set, the screen base and the pre-ship log
    (`audits/logs/s13d-fill-g4-*`).
- If Lean cannot start, follow `briefs/fill-environment-addendum.md` exactly.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/s13d-g4 @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-s13d-g4.zip`. It contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - the bootstrap and final sweep logs and the axiom log;
  - both screen outputs, and `SHA256SUMS`.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #109** (`e5fcd8ee`). The inputs commit adds
  no Lean change. Lines in this brief are those of that tree. `Build/ZoneRebalance.lean` is
  unchanged since #106 (331 lines). Every probe and measurement below was run there, against the
  olean snapshot of #109's replay.
- **In flight, merging after your base and invisible to it:**
  - B6 F3 (`SpaceComplexity/WindowClock`): its private clock writer is a known neighbour of any
    "copy a field layout's cells contiguously" helper you write (§Duplication);
  - the canonizer's continuation 5 (`CodeSimulator`);
  - MIG-1's batches F-A to F-D.

  Cite nothing these add.

## Parallel batches this round

None in `Build/ZoneRebalance.lean`. G5 (the simulation theorem) is stated after this fill.

## What this is

**G4's fill: the two machine rows of the Hennie–Stearns zone layer** ([AB09] §1.7;
`machine-library-design.md` §13d, decisions 13d.2–13d.4):
- **the extension row** `exists_zoneExtendTM`: lay out level `ℓ` on every track, half full of
  virtual blanks;
- **the rebalance row** `exists_zoneRebalanceTM`: for a direction and a track, realize the total
  guarded cascade at the scanned index, or report `short`.

Both statements are frozen. They are two-tape machines over `Turing.ZoneSym k`: tape `0` is the
zoned tape, tape `1` a blank scratch tape (`Turing.zoneRowPre`). The tape count is fixed by the
statements, so **no component may add a tape**. A tape-adding counter loop cannot stand in for
the level loops (the G2–G4 gate's obligation 3).

**User decisions (2026-10-15):**
1. **One brief, two phases:** phase 1 is the shared kit and the extension row, phase 2 the
   rebalance row. Partial deliveries continue as continuations.
2. **Exactly two imports are authorized**, as your first edit: `Build/Contract/Catalog` and
   `Build/Contract/Seam`. Without them the hosts the survey named are out of reach. The pre-ship
   overlay elaborates with them; they make no cycle, since only the `TuringMachine` facade
   imports your file.

**Read first:**
- both rows' docstrings: their fill plans bind where this brief does not refine them;
- the survey (`G4-HOSTS-SURVEY.md`) and the walk gate's findings (finding 1 and its "Fit for G4"
  section);
- `Build/ZoneTape.lean` in full: the layout, inner packing, `zoneSlotOf` and `zoneSlotSet`, the
  word lemmas, `zonedTape_extend`;
- in `Build/Zone.lean`: `zoneShiftInW`, `zoneShiftOutW`, `zoneStepPair`, `zoneMove`,
  `zoneCascadeRight` and `zoneCascadeLeft`, `zoneShiftIndex`, `zoneRebalance`,
  `zoneCascade_cost_le`.

**Pre-ship check** (maintainer, at the base, against `oleans-lwalk`;
`audits/logs/s13d-fill-g4-preship.log`):
- **The overlay** (`audits/evidence/s13d-g4-fill/ZoneRebalanceOverlay.lean.txt`, generator
  `tools/mkoverlay.py` with `tools/home.lean.txt`): `ZoneRebalance.lean` with the two imports and
  the two recommended layout bridges at the home. **0 errors, 0 non-sorry warnings, 4 sorry
  warnings:** the two bridge stubs and the two rows. The generator undoes its edits and leaves
  the rows' statements untouched.
- **The import probe** (`G4ImportProbe.lean.txt`, 94 `#check`s): every public declaration this
  brief cites resolves from your file's context with the two imports. 0 errors, 0 warnings.
  **Re-run it after your delivery.**

## Owned regions and targets (modify these and nothing else)

| # | File:line | Target | Phase |
|---|---|---|---|
| 1 | `Build/ZoneRebalance.lean:198` | `Turing.exists_zoneExtendTM` (frozen statement) | 1 |
| 2 | `Build/ZoneRebalance.lean:164` | `Turing.exists_zoneRebalanceTM` (frozen statement) | 2 |

Your regions:
- **(a) the imports:** add exactly `import TCSlib.Complexity.TuringMachine.Build.Contract.Catalog`
  and `import TCSlib.Complexity.TuringMachine.Build.Contract.Seam` after line 7, as the overlay
  does;
- **(b) the home**, before the section header `/-! ### The rows -/` (line 125): your `private`
  declarations. `private` only, and no `section`, `open` or `variable` that leaks past it;
- **(c) the extension row's body**, the `sorry` on line 208, and a flagged **"Fill appendix
  (§13d G4)"** paragraph before its docstring's closing ` -/` (line 197);
- **(d) the rebalance row's body**, the `sorry` on line 176, and a flagged appendix paragraph
  (line 163).

Everything else is frozen:
- the module header;
- the data, endpoints and envelopes (lines 66–123);
- both rows' statements;
- the proved endpoint lemmas (210–330);
- every other file.

The maintainer updates the module's status text at integration.

### The recommended layout bridges (Recommended shape; you may restate them)

`tools/home.lean.txt` holds two stubs:
- **`zonedTape_right_fields`:** from home, the right side is the field layout
  `[home cell] :: List.ofFn (zoneCells true z)`.
- **`zonedTape_left_fields`:** the left zones read left to right
  (`List.ofFn fun i => (zoneCells false z i.rev).reverse`) end at cell `-2`, with the separator
  at `-1`.

They let the seek family's field-layout contracts run on the zoned tape:
- `seekEndTM_contract` from home stops at `zoneStart ℓ`, the new right zone's first cell;
- `seekStartTM_contract` from home stops at the left layout's first cell.

**Insert each only once proved** (as stated or restated). A partial never adds an open admission.

### The walk's convention (binding; walk gate, finding 1)

`walkTM` moves the moved heads `|w| + 1` cells: one past the ruler's delimiter. The survey's
"`m` cells for a length-`m` ruler" was off by one. **For a displacement `m ≥ 1`,** step the
ruler head once alone (a `tapeAction` step in fixed control), then walk over the ruler's tail,
of length `m - 1`. The other heads then move exactly `m`, monotonically. Displacement `0` is a
separate stationary branch. Cost the ruler's restoration and every control transition.

### Hosts (binding; the host-first rule, `policy.md` §1, `workflow.md` §2; the survey's §2)

- **Iteration** over levels, zones or marks: **`Turing.Round.iterate`** (index-free, so the level
  may vary per round), or `Turing.RoundContract` where one index suffices, released into a
  contract by `Turing.RoundContract.release`. **No counter tape, no private loop host.**
- **Composition:** `Turing.Contract.seq`, `Contract.inPhase`, `Contract.branch`, `Contract.trans`,
  with `Traj.seq` and `Frames.seq`. Your rows are stated as contracts: build them by these, never
  by a hand trace of a whole row.
- **The rows** (all public and proved):
  - the column moves, by the mapped copy and transfer as contracts (`copyMapTM_contract`,
    `transferMapTM_contract`), with `extract := zoneSlotOf t` and `merge := zoneSlotSet t`;
  - the ruler, `walkTM_contract`;
  - zone to zone, `skipTM_contract` and `skipBackTM_contract`;
  - the layout ends, `seekEndTM_contract` and `seekStartTM_contract`, through the bridges;
  - re-packing on scratch, `scanTM_contract` (`scanMap`, `scanShift`);
  - cleanup, `clearTM_contract`.
- **Leaves you may write** (small finite controllers, each with a docstring saying why no public
  row serves it):
  - a one-cell move on one tape (the walk adjustment);
  - a one-slot guard test (read the scanned cell's track-`t` slot, branch on `⊠`);
  - a one-cell write.
- **Promotion candidates** (list each with its contract in `REPORT.md`; notes only): any generic
  helper, in particular the layout bridges and any ruler builder.

### The route (binding where it names a row; otherwise recommended)

**The scratch tape.** It is blank at entry, with its head anywhere (`zoneRowPre`), and must be
blank again at the exit with its head back (both posts keep `d.workTapes 1` and every head).
- Lay out what you need as delimited words, separated by blanks: rulers, a buffer for a column,
  a unary zone count.
- Clear each with `clearTM_contract` before the exit.
- The tape-1 envelope is the time-implied one (`zoneRowHi`, ruling 8).

**Phase 1, the extension row** (`exists_zoneExtendTM`; time `O(2^ℓ + 1)`). Its endpoint is
`zonedTape_extend`: the two new zones each hold `inr (fun _ => some none)` (a stored virtual
blank on every track) in their inner `2^ℓ` slots, and `inr (fun _ => none)` (all `⊠`) in their
outer `2^ℓ`.
1. **`ℓ = 0`:** finite control writes the two cells on each side (cells `±2`, `±3`; `zoneStart 0 = 2`).
2. **`ℓ ≥ 1`, the right side:**
   - `seekEndTM` from home to `zoneStart ℓ`, through the right bridge;
   - `skipBackTM` to zone `ℓ - 1`'s start;
   - a mapped copy of that zone onto scratch as a ruler of `cap(ℓ - 1) = 2^ℓ` cells;
   - `skipTM` back to `zoneStart ℓ`;
   - the mapped copy from the ruler onto tape `0` with constant merge `inr (fun _ => some none)`,
     the inner half;
   - the adjusted walk by `2^ℓ`;
   - the ruler head back by `skipBackTM`;
   - the mapped copy with merge `inr (fun _ => none)`, the outer half.
3. **Return home.** Home is the **unique one-cell field** (every zone has `cap ≥ 2`). So
   `skipBackTM` rounds, each ending in a test "is the cell after this field's first cell blank?",
   reach it as a `Round.iterate` loop that escapes at home. Alternatively, keep the right side's
   distance on scratch and walk back with it.
4. **The left side**, the mirror: `seekStartTM` from home, through the left bridge, to the left
   layout's first cell. The new left zone's inner half is at `[-(zoneStart ℓ + 2^ℓ - 1), -zoneStart ℓ]`,
   its outer half further out. The mapped copies write rightward, so place the head at the outer
   end first: two adjusted walks left by `2^ℓ`. Write outer then inner.
5. **Clear the ruler and return home.** Each phase is `O(2^ℓ)`. The frames come from
   `zoneExtendPost_frames`.

**Phase 2, the rebalance row** (`exists_zoneRebalanceTM`; time `O(2^{i₀} + 1)`, with
`i₀ = zoneShiftIndex dir (z t)`).
- **The specification is the pure cascade, exactly:** `zoneRebalance dir (z t)` on track `t`,
  every other track unchanged (`zonedTape_update_slot` keeps them).
- **The scan.** Walk outward on the feeding side (right for `dir = true`), zone by zone
  (`skipTM`). In each zone, test the innermost slot of track `t`: zone `i` is nonempty exactly
  when that slot is not `⊠`. The first nonempty zone is `i₀`. Two consecutive blanks (the
  layout's end) mean `short`: rewind and exit, with the tape unchanged (the post's identity
  branch). This is a `Round.iterate` loop with two escapes.
  - *Recommended:* record a **unary zone count** on scratch while scanning, one mark per zone
    crossed. A word of `i₀ + 1` cells, written contiguously by the one-cell writer and a one-cell
    move. That count, not a distance ruler, is how the other side finds level `i₀`.
- **The cascade** at `i₀` (`zoneCascadeRight`, or for `dir = false` its mirror through
  `ZoneContents.swap`): the descending pairs `i₀, …, 1`, the home move, the ascending pairs
  `1, …, i₀`.
  - **The pair at level `i`** is `zoneStepPair i = zoneShiftOut false i ∘ zoneShiftIn true i`:
    - **`zoneShiftIn` on the right:** if `R_{i-1}` is empty on track `t`, move `R_i`'s first
      `2^(i-1)` stored cells into `R_{i-1}`;
    - **`zoneShiftOut` on the left:** if `L_{i-1}` is full (its outermost slot occupied) and
      `L_i` has room for `2^(i-1)` more (its slot at offset `cap_i - 2^(i-1)` is `⊠`), move
      `L_{i-1}`'s outer half onto `L_i`'s inner end.
  - **Recommended reordering, proved pure first.** The right and left operations touch disjoint
    zones, with guards on their own sides. A pass can therefore do every right-side step of its
    levels, cross home once, and do the left-side steps, using the zone count to reach level `i₀`
    on the left.
    - Prove that the reordered composition equals `zoneCascadeRight` once, as a pure private
      lemma, before using it.
    - The home move (`zoneMove`) sits between the passes, with its guard on `L_0`'s room.
  - **A guard** reads one slot at an offset inside a zone: the innermost, the outermost, or
    `cap_i - 2^(i-1)` from the inner end. Reach the offset with the adjusted walk over a ruler,
    and test with the one-slot leaf.
  - **A move** is a column operation on the two zones concerned:
    - copy track `t`'s column to scratch (`copyMapTM_contract`, `extract := zoneSlotOf t`);
    - re-pack it there (the stored cells' new split);
    - copy it back (`merge := zoneSlotSet t`), which keeps the other tracks.

    `2^(i-1)` is `cap(i - 2)`, zone `i - 2`'s length, for `i ≥ 2` (a mapped copy of that zone is
    the ruler), and `1` at `i = 1`. Inner packing means "the first `m` stored cells" are the
    innermost `m` slots.
- **Cost.** Level `i` costs `O(2^i)`, the sum is `O(2^{i₀})` (`zoneCascade_cost_le`), and the
  scan is `O(2^{i₀})`.
- **The envelope.** The zoned head stays within `zoneStart (i₀ + 1)` of home (`zoneRowLo`/`Hi`);
  check the outermost slot reads and the separator after zone `i₀`.
- **The frames** come from `zoneRebalancePost_frames`.

### Phases (for a partial; ground rule 9)

1. **Phase 1:** the two imports, the layout bridges (proved and inserted), the ruler and
   one-cell helpers, and `exists_zoneExtendTM` proved.
2. **Phase 2:** `exists_zoneRebalanceTM` proved. Within it, report which of these are done: the
   scan with `short`, the pair step at one level, the passes, the home move, the cleanup.

A partial may leave only targets open. **Add no new admission:** a helper is inserted only once
proved. The freeze check for a partial is the axiom walk: `sorryAx` reaches each row only through
its own open body.

## Gate guidance (binding)

- **The G2–G4 statement gate's rulings** stand (`audits/s13d-g24-statements-resolutions.md`):
  - existential rows now, named machines at fill (ruling 5): your machines are private and
    listed as promotion candidates;
  - the time-implied scratch envelope (ruling 8).
- **Obligation 3** is discharged: the survey identified the hosts, and the walk gate filled the
  one missing leaf. Do not write a private host.
- **The walk gate's carried note:** ruler construction and doubling, scratch-buffer
  coexistence, cleanup and the complete geometric cost are this fill's obligations, under the
  public round and composition hosts.

## Cited infrastructure (public and proved at the issue commit; all in `G4ImportProbe.lean.txt`)

The probe's 94 names, in five groups:
- the rows' data, endpoints, envelopes and frames;
- the pure zone layer;
- the zoned carrier;
- the rows as contracts;
- composition and iteration.

**Proved modulo, exactly:** none. A complete delivery has no `sorryAx` in either target.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(d) of `Build/ZoneRebalance.lean`. List every
   new declaration with its role.
2. **Statement freeze** over both targets and every landed declaration: no renames,
   re-signatures, restatements or attribution edits.
3. **No new public declaration.**
4. **Escalation** on anything unprovable as stated, including a cited row or bridge that does not
   compose as the route says: stop on that item, record the obstruction, and continue with the
   rest.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports:** exactly the two above, added first. No other TCSlib import. A Mathlib import only
   if a needed lemma requires it; flag it.
7. **One proof per shared argument.** Never write a second seam, phase host, round iteration,
   trace or embedding transport. Never re-walk a row's trace: compose the contracts.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public and
   private declaration counts (base: 331 lines; 18 public, 0 private).
9. **Continuation budget.** A partial zip states the phase reached, the open declarations (each with
   a literal "Proof sketch"), and both targets' axiom walks. A partial is expected and fine; an
   unreported gap is not.
10. **The pinned base.**
    - Cite only declarations public at your base, and your file's own privates.
    - Do not rely on unfolding the body of any definition in `Build/Catalog`,
      `Build/Contract/*` or `Build/Seam`; use their contracts. Unfolding `Build/Zone`'s and
      `Build/ZoneTape`'s pure definitions is expected.
    - List every declaration you cite outside your file. If you cite more than the probe's list,
      add them to a copy of the probe and run it.
11. **MIG-1 compatibility.**
    - Cite none of the six R3 canonical rows; use their framed or contract forms.
    - Cite no private declaration of `Build/Catalog`.
    - Keep your new privates under the `zr_` prefix.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`audits/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**).
- **The population** is 10 files (`audits/evidence/s13d-g4-fill/screen-population.txt`):
  - your file;
  - the files the route cites: `Build/Zone`, `Build/ZoneTape`, `Build/Catalog`,
    `Build/Contract/Catalog`, `Build/Contract/Basic`, `Build/Contract/Seam`, `Build/Seam`,
    `Simulation`;
  - the known hazard `Build/RecordTable`.
- **The screen** is the declaration-keyed `audits/evidence/retrofit/copy-text-screen-v3.py`, on
  the repository paths.
- **The base**, at the issue tree, is `audits/logs/s13d-fill-g4-screen-base.txt`:
  **763 declarations, 429 pairs, 126,953 characters** (MEASURED; about 5 minutes). The overlay's stubs have bodies under the 60-character floor.

```sh
P=audits/evidence/s13d-g4-fill
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side. Nothing is
  pre-disclosed.
- **Known hazards:**
  - **`Build/RecordTable`'s field copy** (`exists_fieldsCopyTM`, its private `rt_copyMachine`:
    copy, skip, recurse, skip back). Your layout walks have the same shape: cite the rows and
    compose, and do not transcribe it.
  - **B6 F3's clock writer** (in flight, private in `WindowClock`), if you build a contiguous copy
    of a layout's cells. It is not visible to you. Report such a helper as a promotion candidate;
    the maintainer reconciles the two.
  - `Build/Zone`'s pure cascade proofs (`zoneSide_cascadeRight` and its family): your pure
    reordering lemma cites them and does not re-derive them.
  - the mirror (`dir = false`): derive it through `ZoneContents.swap` and the swapped tape
    (13d: "never copied"), or factor it by a direction parameter. A 90% pair between the two
    directions is a copy.
- List every new in-file pair with a one-line justification. At 90% or more it is a copy: factor
  it. Quote both outputs in `REPORT.md`, which carries **"new copies: none"** (or lists each
  pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/s13d-fill-g4.txt` (**79 modules**: the upstream closure,
  with the two imports, of your owned file and of every module downstream of it, without the root
  `TCSlib`; one module is downstream of it, the `TuringMachine` facade):

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/s13d-fill-g4.txt )
  ```

  Bootstrap after adding the two imports (the order list includes their closure).

  **The base sorry-warning set has 37 entries in 16 modules**
  (`audits/logs/s13d-fill-g4-base-sorries.txt`, one per declaration). Yours are
  `Build/ZoneRebalance`'s two. Record the base list by name first, and report any difference.
- **Final checks:**
  1. `Build/ZoneRebalance`: zero errors, no sorry warning (for a partial, exactly the open
     targets'), and no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's
     minus yours (**35** for a complete delivery).
  3. Re-run `G4ImportProbe.lean.txt`: 0 errors.
- **Axiom prints** (in a scratch copy of your module with `#print axioms` appended) for both
  targets and every new private: within `[propext, Classical.choice, Quot.sound]`, no `sorryAx`
  for a complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`,
  0 FAIL (base: 0 FAIL, 14 WARN over 36 files). No new line over 100 characters.

## Out-of-scope sorries you will see (leave every one untouched)

Everything in the base sorry set except your two targets:
- MIG-1 stage S's sorried specs;
- `Build/RecordTable`, `Build/NDHost`, `Build/StepBlockForward`, `Build/InputWindow`,
  `Build/InputDevice`;
- `CodeSimulator`, `NDCodeSimulator`, `UniversalK`.

If a proof seems to *need* one of these beyond a named citation, that is an escalation, not a
license.

## REPORT.md checklist

- [ ] The phase reached; the base hash and the ancestor check; the two imports as the first
      edit.
- [ ] Every new declaration with its role; the bridges as recommended or restated; each leaf
      with its reason; the flagged appendices.
- [ ] The scratch layout you used, and the walk convention as applied.
- [ ] Promotion candidates and escalations, or "none".
- [ ] Rule 10: the declarations cited outside your file, and the probe re-run. Rule 11: a grep of
      your diff for the six R3 rows.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints; the lint line. The diff touches only your
      owned regions.

## Known pitfalls at this pin (hard-won)

- **Two blanks in a row mark the layout's end; one blank is a separator.** The home is the only
  one-cell field: every zone has `cap ≥ 2`. `zoneStart 0 = 2`, so the separators around home
  are at `±1`.
- **Inner packing:** stored cells sit at each zone's inner end, and `⊠` (`none` in a slot) fills
  the rest.
  - A zone is empty on a track exactly when its innermost slot is `⊠`, and full exactly when its
    outermost slot is occupied.
  - A stored **virtual blank** is `some none`, not `⊠`.
- **The left side reads reversed** (`zonedTape_left_word`): the left zone `i`'s inner end is at
  `-zoneStart i`, its outer end at `-(zoneStart i + cap_i - 1)`. A rightward mapped copy writes
  from the outer end.
- **The mapped copy writes `merge (old destination cell) (extract source cell)`** and returns
  both heads (`2|w| + 2` steps). The walk moves `|w| + 1` (the convention above).
- **Contracts fix `Γ : Type`;** `ZoneSym k` is one. A `Contract`'s cut includes time `0`,
  so an entry is never an exit.
- **`Round.iterate`** takes a round-time function on configurations and a round hypothesis per
  orbit point; the level can be read off the configuration. `RoundContract`'s orbit lemmas fix one
  index.
- `omega` with products and powers as atoms (`ring` first). `zoneStart_eq : zoneStart i =
  2^(i+1) + i` and `zoneStart_succ` are the arithmetic. The linter needs a literal "Proof
  sketch" before every `sorry` (partial only).
