# Review — §13d G4, continuation 1 (`Build/ZoneRebalance.lean`), delivery `fill-s13d-g4-cont1.zip`

**Verdict: partial (0/2), landable as a partial.** Both rows keep their original `sorry` bodies.
The delivery:
- re-points the four helpers phase 0 named;
- adds 13 checked `private zr_` helpers: the two recommended layout bridges as recommended, their
  offset formulas, the two seek preconditions, a field-layout comparison lemma, and the total
  cascade's pure side-pass reordering;
- adds an arithmetic witness for a new route escalation (called "E1" in the delivery).

What passes:
- every integrity, ownership, freeze and hygiene check;
- elaboration, at the base and at the current tip;
- the axiom and admission walks;
- the import probe, lint and the v3 screen (two in-file pairs at 62% and 72%, justified).

Three findings:
- **F1 (minor, rule 10).** One step of the new right bridge closes by definitional unfolding of
  another file's definition, `FinTM.bufferTape` (`Simulation.lean`), at the literal `1 : ℤ`.
  The worker's rule-10 grep missed it, because it is a defeq closure, not a named unfold. A
  two-line re-pointing through the published `FinTM.bufferTape_nat` is verified below.
- **F2.** The delivery's escalation is genuine. The brief's left-pass arithmetic is off by one
  cell: it ignores the separator between the old layout and the new zone. The rows already
  permit the fix, so the maintainer can amend the route.
- **F3 (progress).** No machine was composed: no contract, round, ruler, scan or move. The escalation (F2)
  blocks only the left pass, yet the right pass, the ruler builder and the return home stayed unbuilt.

## Inputs

| Input | Identity |
|---|---|
| Zip | `infra_local/fill-s13d-g4-cont1.zip`, SHA-256 `8797c711…f8267b` (`zip-sha.txt`); 11 entries |
| Extraction | `$S/incoming/g4-cont1/`: every member byte-equal to the zip, no unsafe entries, CRC OK (`zip-vs-extracted.txt`, script `scripts/zipcmp.py`) |
| Brief | `infra_local/fill-dispatches/s13d-fill-g4-cont1.md`, `cd1809a7…c3102d`; base `briefs/s13d-fill-g4-cont1.md` with `@ANCESTOR@` → base is byte-equal (`brief-check.txt`) |
| Addendum | `fill-environment-addendum.md`, `a25474c5…8d2928`, byte-equal to the base copy (`brief-check.txt`) |
| Base | `94b986d4db7167ab2a8b20d38d4385f11e60be0e`; TCSlib tree `11fcef24` = `531b98a2`'s (#118) (`trees.txt`) |
| Snapshots | `oleans-lbapi4` (base), `oleans-lndnf` (tip) |
| Campaign tip | `origin/complexity/arora-barak-ch3-4` = `5de427ed`, TCSlib tree `d066c4b6` = `6d18902f`'s (`tip.txt`). `wt-hk` is at `5de427ed`. The local branch ref is stale (`3462c1b4`) |
| Review ref and worktrees | `refs/review/g4-cont1` (fetched from the bundle). Detached worktrees under this folder: `wt-base` (base), `wt-head` (head), `wt-tipd` (tip plus the delivered file). Each has the `.lake/packages` link |

Every path below is relative to `$S/review/g4-cont1-fill/`. Lean ran only through
`tools/leanelab.sh`, one elaboration at a time. Screens ran one at a time under `nice -n 10`. No
build command was run, and the shim `evidence/runtime/executable-path.c` (`985924ad…4fba7`) was
neither compiled nor run.

## (a) Integrity and scope

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | `SHA256SUMS` | PASS: 10/10 OK; covers every member except itself | `sha256sums-check.txt` |
| 2 | Bundle | PASS: `verify` okay; sole prerequisite `94b986d4…`; head `fill/s13d-g4-cont1` = `66765b0c7f0a52ef9352233dd4e99e64ce33ca7b` | `bundle-verify.txt` |
| 3 | Head commit | PASS: one commit; sole parent exactly the base; the hash matches REPORT ("Final commit: `66765b0c…`"); changes only `Build/ZoneRebalance.lean` (+316/−27) | `head-commit.txt` |
| 4 | Patch | PASS: `0001-…patch` applied to a temporary index at the base reproduces the head tree `2a3a8918` exactly | `patch-check.txt` |
| 5 | Delivered file | PASS: byte-equal to the head blob `bae3aac8` (SHA-256 `3ce8a324…`) | `file-agreement.txt` |
| 6 | Owned regions | PASS: 27 removed and 316 added lines, all inside (a) the home (base 127–350, inserted before `/-! ### The rows -/`), (b) the rebalance appendix (391–395) or (c) the extension appendix (431–437); 0 outside | `regions.txt`, `worker.diff` |
| 7 | Freeze (`declfreeze.py`) | PASS: public 18 → 18, none added or removed, no `STATEMENT CHANGED`. The two targets change in their appendices only ("authorized body change") | `declfreeze.txt` |
| 8 | Private statements (`privstmt.py`) | PASS: `STATEMENT CHANGED: []`. Body-only changes: the two targets (appendices) and the four re-pointed helpers | `privstmt.txt` |
| 9 | Code lines (`stmtcheck.py`) | PASS: of the base's 313 code lines, the only 14 missing are the four re-pointed proofs' old tactic lines | `stmtcheck.txt` |
| 10 | Hygiene (added lines) | PASS: no `sorry`/`admit`/`axiom`/`unfold`/`delta`/`set_option`/`open`/`section`/`variable`/attributes/`native_decide`. One `by decide` on a numeral. `rfl` appears only as `rcases`/`obtain` patterns | `hygiene.txt` |
| 11 | Rule 11 | PASS: 0 hits for the six R3 rows; all new privates are `zr_`; no external private is reached (row 15) | `hygiene.txt`, `ax-head.out` |
| 12 | Imports | PASS: unchanged (the four lines, 6–9) | `worker.diff` |
| 13 | Widths | PASS: added lines at most 99 characters; whole file at most 99 | `hygiene.txt` (`scripts/widths.py`) |

**New private helpers (13)** (head line numbers; `decl-lines.txt`):
- `zr_fieldsTape_eq` (354): a generic field-layout comparison;
- `zr_right_offset` (392) and `zr_zonedTape_right_fields` (412): the right bridge, exactly the
  recommended statement;
- `zr_left_offset` (461) and `zr_zonedTape_left_fields` (481): the left bridge, as recommended;
- `zr_zoneCells_ne_nil` (518);
- `zr_seekEnd_pre` (525) and `zr_seekStart_pre` (543): the seek contracts' `pre` from
  `zoneRowPre`;
- `zr_left_two_walks` (566): the escalation's arithmetic;
- `zr_shift_commute` (583), `zr_inPass_out` (602), `zr_pair_pass` (615) and
  `zr_cascade_passes` (629): the pure reordering.

**The four re-pointings (phase 0)**: verified. Each statement is unchanged (`privstmt.txt`), and
each replacement dependency is a public theorem at the base (`kinds.out`):

| Helper | Now cites | Module of the cited lemmas |
|---|---|---|
| `zr_read_slot` | `zoneSlotOf_inr` (with `Option.map_some`) | `Build/ZoneTape` |
| `zr_capacity_pos` | `zoneCapacity_eq`, then `Nat.mul_pos`/`Nat.two_pow_pos` | `Build/Zone` |
| `zr_ruler_length` | `zoneCapacity_eq` (was `simp only [zoneCapacity, …]`) | `Build/Zone` |
| `zr_mirror_tape` | `zonedTape_zero`/`_of_pos`/`_of_neg`, `zoneCellAt_eq` (`Build/ZoneTape`); `ZoneContents.words_true`/`_false`, `ZoneContents.swap_home`/`_left`/`_right` (`Build/Zone`) | `Build/ZoneTape`, `Build/Zone` |

Re-pointing `zr_mirror_tape` also uses `words_true`/`words_false`, which the brief's table does
not list. They are published `rfl` lemmas of `Build/Zone` and are fine.

**Rule-10 check by sealing** (new method; `scripts/mkseal.py`):
- **Method.** The home is wrapped in a section that makes 30 other-file TCSlib definitions
  `local irreducible`. That covers every non-type, non-abbrev definition the helpers reach:
  `zoneCapacity`, `zoneStart`, `zonedTape`, `zoneCellAt`, `zoneCells`, `zoneOwner`,
  `zoneSlotOf`, `fieldOffset`, `fieldsTape`, `joinFields`, `FinTM.bufferTape`, `ZoneContents.*`,
  the shift and cascade functions, the seek contracts and machines, `tapeAction`, … The list is
  in `kinds.out`.
- **Why.** Proof constants cannot show a definitional unfolding: `rfl` and `rfl`-lemmas leave no
  trace (`ax-base.out` shows the base's four helpers with no equation lemmas either).
- **Control, the base.** It fails at exactly the four helpers phase 0 named: base lines 142, 146,
  230, 235 and 237 (`seal-Base.out`). These are `repoint.md`'s lines.
- **The head.** The four pass. Exactly one new error remains (`seal-Head.out`, and identically at
  the tip, `seal-Head-tip.out`).
- **F1.** The error is in `zr_zonedTape_right_fields`, the home separator case, head lines
  440–441:
  ```lean
        simpa only [Nat.cast_zero, zero_add, FinTM.bufferTape_nat,
          List.getElem?_cons_succ, List.getElem?_nil] using hsep
  ```
  - After simplification the goal still reads `FinTM.bufferTape [home] 1` at a literal
    `1 : ℤ`. `bufferTape_nat` needs a cast `((i : ℕ) : ℤ)`, so it does not fire, and
    `simpa`'s closing step unfolds `bufferTape` by defeq.
  - Sealing only `FinTM.bufferTape` reproduces the error (`seal-onlyBufferTape.out`).
- **Verified fix** (`suggested-fix.diff`):
  ```lean
        rw [Nat.cast_zero, zero_add, ← Nat.cast_one, FinTM.bufferTape_nat]
        simpa only [Nat.cast_one, List.getElem?_cons_succ, List.getElem?_nil] using hsep
  ```
  - With the full seal: 0 errors at the base snapshot and at the tip (`seal-HeadFix.out`,
    `seal-HeadFix-tip.out`).
  - Unsealed: 0 errors and the same two sorry warnings (`elab-fix-unsealed.out`).
- **Severity.** Minor: a private helper and a `rfl`-level fact, and a published lemma exists. But
  it is a literal breach of the binding rule 10. REPORT's claim that its grep categories "account
  for every hit" is therefore incomplete.
- **The other rewrite arguments.** All 84 identifiers in the added `rw`/`simp`/`simpa`/`norm_num`
  argument lists are theorems, locals or the file's own privates. No definition is passed (`rwargs.txt`, `kinds.out`).

## (b) Elaboration and axioms

| # | Check | Result | Evidence |
|---|---|---|---|
| 14 | Head against `oleans-lbapi4` | PASS: exit 0, 0 errors; warnings only `:686:8` and `:727:8` `declaration uses 'sorry'` (the two targets) | `elab-head-lbapi4.out` |
| 15 | Base baseline | exit 0; `:396:8`, `:438:8` sorry (the same two targets) | `elab-base-lbapi4.out` |
| 16 | Sorry count, module | 2 → 2, the same declarations; no other warning | 14, 15 |
| 17 | Axioms (scratch copy with `#print axioms`, 31 privates and 2 targets) | PASS (partial): both targets `[propext, sorryAx, Classical.choice, Quot.sound]`; every private within `[propext, Classical.choice, Quot.sound]` (`zr_cellTM`: none). Agrees name by name with the worker's `axioms.log` | `ax-head.out`, `ax-mine-norm.txt` = `ax-worker-norm.txt` |
| 18 | Admission walks | PASS: `exists_zoneExtendTM: [Turing.exists_zoneExtendTM]`; `exists_zoneRebalanceTM: [Turing.exists_zoneRebalanceTM]` | `ax-head.out` |
| 19 | External privates and equation lemmas | none reached from any of the 31 helpers (closure walk through own-module constants) | `ax-head.out` (`EXT` lines) |
| 20 | Import probe (`G4C1ImportProbe.lean.txt` appended to the delivered module) | PASS: 0 errors, 338/338 outputs; only the two target sorry warnings | `importprobe-head.out` |
| 21 | Cited beyond the probe | 30 TCSlib constants reached are not among the probe's 338. Lemmas: `FinTM.bufferTape_nat`, `ZoneContents.ext'`, `length_joinFields_add_one`. The rest are types, constructors, projections and primitives. All are public at the base. The worker's extended 658-check probe is not in the zip | `extlist-not-in-probe.txt`, `kinds.out` |
| 22 | Worker's sweep logs | consistent: bootstrap and final sweep both cover the 80-module order list in order. 35 sorry warnings in 15 modules, equal per module to `audits/logs/s13d-fill-g4-cont1-base-sorries.txt`. The REPORT's list is byte-equal to that file. The ZoneRebalance warnings are at 686 and 727. Not reproducible here (no build) | `final-sweep-sorries.txt`, `report-base-sorries.txt` |

## (c) Progress (against the brief's phases)

| Phase / obligation | State | Notes |
|---|---|---|
| 0: re-point the four | **complete** | verified by seal and freeze (above) |
| 1: layout bridges, proved and inserted | **complete** | as recommended (statements equal `tools/home.lean.txt`'s stubs, renamed `zr_`), plus the offset formulas |
| 1: seek preconditions | **complete (pure)** | `zr_seekEnd_pre`/`zr_seekStart_pre` discharge `seekEndTM_contract_pre`/`seekStartTM_contract_pre` from `zoneRowPre` |
| 1: ruler builder | open | none |
| 1: `exists_zoneExtendTM` (right pass, return home, left pass, cleanup, assembly, `ℓ = 0` branch) | open | no contract composed |
| 2: pure reordering | **complete** | `zr_cascade_passes`: `zoneCascadeRight j = L↑(R↑(zoneMove true (L↓(R↓ z))))`; total (no guard assumption); cites `zoneCascadeRight_eq`, `zoneStepPair_eq`, the shift field equations; `dir = false` follows by `zoneCascadeLeft_eq` (swap) |
| 2: scan with `short` | open (pure facts only, inherited `zr_scan_index`/`zr_scan_short`) | |
| 2: pair step at one level, passes, home move, cleanup | open | |
| 2: `exists_zoneRebalanceTM` | open | |

**On route and reusable?**
- The bridges, the offsets, `zr_fieldsTape_eq` (generic over `Γ` and `fs`) and
  `zr_cascade_passes` are on the brief's route and reusable as they stand.
- **Caveat for the next continuation:**
  - `zr_seekEnd_pre` and `zr_seekStart_pre` take the whole `zoneRowPre`, i.e.
    `tape 0 = zonedTape z`.
  - The extension's second seek runs on a tape the first side's pass has already changed. One of
    them must therefore be restated from agreement with `zonedTape z` on the cells it reads:
    `[0, zoneStart ℓ]` for the end seek, `[-zoneStart ℓ, 0]` for the start seek, through the
    frames.
  - The bridges themselves are pointwise and need no change.
- `zr_left_two_walks` exists only as evidence for the escalation. The next continuation should
  restate it to the amended arithmetic, or remove it.
- No other file's definition is unfolded except at F1, and no other file's private is used.
- The proved pieces add no host, leaf, tape or loop.

**The escalation, verified (F2).**
- `seekStartTM_contract`'s endpoint is `pos − fieldOffset ws |ws|` (`Contract/Catalog.lean`
  426–437). With the proved left offset (`fieldOffset ws ℓ + 2 = zoneStart ℓ`), it stops at
  `2 − zoneStart ℓ`, the outermost cell of zone `ℓ − 1`.
- The new zone's outer end is `1 − zoneStart ℓ − zoneCapacity ℓ`. The displacement is therefore
  `zoneCapacity ℓ + 1 = 2^{ℓ+1} + 1`: the separator at `1 − zoneStart ℓ`, then the zone.
- The brief's "two adjusted walks left by `2^ℓ`" cover `2^{ℓ+1}`, one cell short. At `ℓ = 1` the
  walks reach −7 instead of −8, and a four-cell rightward write from −7 would overwrite the
  separator at −4. `zr_left_two_walks` checks the general identity in Lean.
- The right side has no such offset: `seekEndTM_contract` stops at `fieldOffset fs (ℓ+1) =
  zoneStart ℓ`, the new zone's first cell, past the separator.
- **Disposition: route arithmetic, not a specification problem.** Two fixes exist inside the
  permitted rows and leaves:
  - one extra leftward step of the one-cell leaf (`zr_cellContract`, no write);
  - or making the first leftward walk the **unadjusted** walk over the whole ruler (the walk's
    native `|w| + 1 = 2^ℓ + 1`), then one adjusted walk.

  The envelope still holds: `−(zoneStart ℓ + cap ℓ − 1) ≥ −zoneStart (ℓ + 1)`.
- **Label collision.** The delivery calls this "E1", which collides with the first round's E1
  (the no-unfolding ruling of 2026-10-16). Rename it, for example "cont1-E1", in the records and
  in the extension appendix.
- **E2 (runtime) is not a Lean matter.** See (e).

**Size:** 571 → 860 lines; 18/18 → 18 public / 31 private (`lint-tm-head.out` INFO line).

## (d) Duplication and lint

| # | Check | Result | Evidence |
|---|---|---|---|
| 23 | Screen v3 script | SHA-256 `f4feac91…f878f181`, the same at base, head and tip | `screen-script-sha.txt` |
| 24 | Before (base, 10-file population) | `declarations screened: 795; copy pairs …: 437; reproduced text: 127,810 chars` (exit 0, 288 s). Byte-equal to `audits/logs/s13d-fill-g4-cont1-screen-base.txt` minus its comments, and to the worker's `screen-before.txt` | `screen-before.txt`, `screen-compare.txt` |
| 25 | After (head) | `808; 439; 127,994 chars` (exit 0, 292 s); byte-equal to the worker's `screen-after.txt` | `screen-after.txt` |
| 26 | New pairs (`pairdiff.py`, by name, vs before and vs the repo base log) | **2, both in-file, no cross-file pair**: `zr_pair_pass` reproduces `zr_inPass_out` 92/127 = 72%; the reverse 92/149 = 62%. The shared tile is the list-induction scaffold (`induction is generalizing z with \| nil => simp only [List.foldl_nil] \| cons … rw [List.foldl_cons, …`). Under 90%: not a copy. The worker's justification matches. 0 pairs removed | `screen-compare.txt` |
| 27 | Known hazards | No pair with `rt_copyMachine`/`exists_fieldsCopyTM`, with `zoneSide_cascadeRight` and its family, or between mirror directions. `Build/Zone` has no commutation or pass lemma, so the reordering is new mathematics, not a re-derivation (grep in `Zone.lean`). No contiguous layout-copy helper, so nothing overlaps F3's clock writer | `screen-after.txt`; Zone lemma list |
| 28 | Lint, `TuringMachine` | base and head `style_lint: 0 FAIL, 67 WARN over 79 files`. The only difference is ZoneRebalance's INFO lines (`860 lines > target 600`; `18 public / 31 private`) | `lint-tm-base.out`, `lint-tm-head.out` |
| 29 | Lint, `TuringMachine/Build` (the brief's scope) | `0 FAIL, 32 WARN over 37 files`, the same at base and head and equal to the worker's | `lint-build-*.out` |
| 30 | Docstrings and sketches | All 13 new helpers have docstrings. Ten carry a "Proof sketch". The three without are short (`zr_zoneCells_ne_nil`; `zr_seekEnd_pre`/`zr_seekStart_pre`, about 15 lines, under policy §3's ~20-line threshold). Cosmetic: the two longest proofs (`zr_zonedTape_right_fields`, `_left_fields`, 35–50 lines) have no step comments, and there are two double blank lines (before `zr_shift_commute` and before `/-! ### The rows -/`) | `decl-lines.txt` |

## (e) Landability on the current tip

- **The owned file is unchanged base → tip.** `ZoneRebalance.lean`'s blob is `9deb85fb` at the
  base, at `531b98a2`, at `6d18902f` and at `5de427ed` (`tip-changes.txt`). The patch applies
  cleanly at `5de427ed`, and the result carries the head blob `bae3aac8` (`patch-at-tip.txt`).
- **Upstream changes since the base.** Twelve `.lean` files changed in `531b98a2..6d18902f`
  (#119, #120), and none in `6d18902f..5de427ed`. Of the 21 upstream TCSlib modules
  (`closure-tip.txt`, the same as at the base), only `Build/Convention` changed, and only by
  addition: four new `Cfg.ofWords_*` theorems, no removals.
- **Elaboration at the tip** (`wt-tipd` = `5de427ed` plus the delivered file, against
  `oleans-lndnf`): exit 0, 0 errors, only `:686`/`:727` sorry warnings (`elab-tipd-lndnf.out`).
  - The tip's own file has the baseline `:396`/`:438` (`elab-tipfile-lndnf.out`).
  - The axiom, admission and dependency probe at the tip is identical to the base-snapshot run
    (`ax-tipd-lndnf.out`).
  - The import probe at the tip: 0 errors, 338/338 (`importprobe-tipd-lndnf.out`).
- **Replay closure at the tip:** `TCSlib/Complexity/TuringMachine/Build/ZoneRebalance`, then the
  `TCSlib/Complexity/TuringMachine` facade (2 modules, `closure-tip.txt`). Replay into a copy of
  `oleans-lndnf`: all 71 facade imports are present there (`facade-imports.txt`). The facade could
  not be elaborated here (no olean for the delivered module). It changes no public declaration.
- **Expected sorry count after landing:** unchanged. 35 over the 80-module order at the base; the
  campaign total does not change. This partial removes none and adds none.
- **Environment (REPORT "Runtime"; summary).**
  - **Startup.** Lean failed ("failed to locate application") and was started with the
    addendum's shim (hash as authorized). The cache tarballs needed `--no-same-owner`.
  - **E2.** The prescribed `lake exe cache get` internally runs `lake -v build
    proofwidgets:release`. The worker therefore cannot attest that no Lake `build` ran inside the
    cache step. No TCSlib build was run.
  - **The final sweep.** A transport disconnect at module 15 (resumed). ENOSPC at module 41 (OS
    error 28): disposable caches were deleted, outputs moved to `/dev/shm` with byte checks, and
    two dependency-path attempts failed and were fixed (`ImportGraph.Imports`,
    `Aesop.Rule.Name`). After 54 sequential checks, the remaining 26 ran with up to four in
    parallel, each after its imports passed.
  - **Consistency.** The final counts agree with the base list. Nothing here affects the Lean
    result, which my elaboration confirms for the owned file.
  - **Suggestions for the addendum.** Note the proofwidgets sub-build as expected. Add a
    free-disk precheck, and recommend `TCSLIB_OLEANS`/`TMPDIR` placement.

## (f) Recommendation

**Not yet clear to merge**: the landing PR is still to be opened and replayed. Clear once the
PR's replay passes and its gate is recorded.

**Land as a partial: yes**, by a maintainer PR like the first G4 partial's. Points for the PR body:
- **Commit.** Cherry-pick `66765b0c7f0a52ef9352233dd4e99e64ce33ca7b` from the verified bundle.
  Its prerequisite is `94b986d4`. It touches only `Build/ZoneRebalance.lean`, which is unchanged
  base → tip.
- **A maintainer commit on top** (recommended, as with #115's reword `464c5038`):
  1. **F1 fix**, the verified two lines in `suggested-fix.diff`, re-pointing the separator step
     through `FinTM.bufferTape_nat`. Alternatively, land unchanged and list F1 as the first item
     of continuation 2's re-point table.
  2. **Appendix wording.**
     - Rename the extension appendix's "escalation E1" to the new label.
     - Point it to this review's archived path (`audits/evidence/s13d-g4-cont1-fill/…`), not to
       a delivery `REPORT.md`.
     - Reword "the left route is stopped under ground rule 4" once the route amendment is ruled.

  After the commit: re-elaborate (expect 0 errors and the two sorry warnings), re-lint, and
  re-run the v3 screen (the fix changes two lines of one private body).
- **What it adds:**
  - the four helpers re-pointed;
  - 13 private helpers: the two bridges as recommended, the offsets, the comparison lemma, both
    seek preconditions, the pure side-pass reordering `zr_cascade_passes`, and the escalation's
    arithmetic `zr_left_two_walks`;
  - no public declaration and no admission;
  - 571 → 860 lines, 18 public / 31 private.
- **Review table:**
  - integrity (10/10 sums, bundle, patch);
  - scope (owned regions only; no statement changed);
  - tip elaboration (0 errors, two target sorries);
  - axiom and admission walks (own bodies only);
  - import probe 338/338;
  - lint 0 FAIL, 32 WARN (Build) and 67 WARN (TuringMachine);
  - v3 screen 795 → 808 declarations, 437 → 439 pairs, the 2 new in-file at 62% and 72%,
    justified;
  - the rule-10 seal test (F1).
- **Replay:** `Build/ZoneRebalance`, then the `TuringMachine` facade, into a copy of
  `oleans-lndnf`. The sorry count is unchanged.

**Continuation 2 (G4 cont2) should:**
1. **Carry the escalation's ruling as a route amendment** (step 4 of phase 1). From
   `seekStartTM`'s stop at `2 − zoneStart ℓ`, reach the outer end with displacement
   `2^{ℓ+1} + 1`: one unadjusted walk over the full `2^ℓ` ruler plus one adjusted walk, or two
   adjusted walks plus one leaf step. Restate or remove `zr_left_two_walks` accordingly.
2. **Re-point F1** if it is not fixed at landing. Add "no defeq closure on another file's
   definition (including `FinTM.bufferTape`)" to rule 10's grep list, and suggest the seal test
   as a self-check.
3. **Build phase 1's machine in order, as contracts**, each a checkpoint that may land alone:
   - the right pass: `seekEnd` → `skipBack` → `copyMap` (zone `ℓ−1` to the scratch ruler) →
     `skip` → `copyMap` with constant merge (inner half) → adjusted walk → `skipBack` (ruler) →
     `copyMap` with `⊠` merge (outer half);
   - the return home (`Round.iterate` built by `round_iff`, or the ruler of distance);
   - the left pass, with the amendment;
   - the `ℓ = 0` branch by the leaf;
   - `clearTM_contract`;
   - assembly by `Contract.ofSegment` in the `HeadBox` of `zoneRowLo`/`zoneRowHi`, with frames
     from `zoneExtendPost_frames`.
4. **Restate one seek precondition** (whichever seek runs second) from agreement with
   `zonedTape z` on the cells it reads, instead of `zoneRowPre`.
5. **Tighten ground rule 4's wording.** Stopping on an item does not stop independent items:
   here the right pass, the ruler builder and the return home were not blocked. Two rounds have
   now produced only pure-layer kit.
6. **Then phase 2 on `zr_cascade_passes`:**
   - the two-exit scan by `round_iff`/`Round.iterate`, with the unary count;
   - one level's guarded column move (`copyMap` with `zoneSlotOf t`, `scanTM`, `copyMap` with
     `zoneSlotSet t`);
   - the four side passes, with the home move between them;
   - `dir = false` through `zoneCascadeLeft_eq` and `zr_mirror_tape`.
7. **Keep the brief's inputs** (probe, population, order list) at the landing commit. The base
   sorry count stays at 35, and the screen base becomes this review's `screen-after.txt` plus the
   F1 fix's re-screen.
