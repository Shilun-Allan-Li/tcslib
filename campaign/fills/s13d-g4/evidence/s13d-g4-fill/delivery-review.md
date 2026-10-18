# Review — §13d G4 fill (`Turing.exists_zoneExtendTM`, `Turing.exists_zoneRebalanceTM`), delivery `fill-s13d-g4.zip`

**Verdict: partial (0/2). It lands now (screens clean); the continuation is blocked on the
maintainer API PR (E1, ruled 2026-10-16).** Both rows keep their original
`sorry` bodies. The delivery adds:
- the two authorized imports;
- 18 checked `private zr_` helpers (slot guards, the scan-index facts, the mirror, the
  ruler-tail lemma, and one factored one-cell leaf with a time-one `Contract`);
- two flagged appendices.

Every integrity, ownership, freeze, hygiene, elaboration, probe, axiom, lint and screen check
passes at the current tip. Escalation E1 is genuine, the same rule-10 class as B6 F3's:
- Ground rule 10 forbids unfolding any definition in `Build/Catalog`, `Build/Contract/*` and
  `Build/Seam`.
- The field layout (`fieldsTape`, `fieldOffset`) is a set of defs in `Build/Catalog`.
- Every mandated row contract is a `def` in `Build/Contract/Catalog` whose
  `pre`/`time`/`post`/envelope fields are given only in its body, through `framedContract`.

I confirmed that no public field-equation lemmas exist. So under the literal rule, neither the
recommended bridges nor any contract composition can be proved.

**Ruled (user, 2026-10-16):**
- No unfolding. A maintainer API PR first adds public equation lemmas.
- The partial lands once its screens come back clean.
- Phase 1 resumes after the API PR (see "What the landing PR needs").

Review conditions:
- Campaign tip at review: `8b383e0bfcf69c1a036cba366caf7ae434e59429`. Its Lean content is
  `e5fcd8ee`, the same as the base (0 `.lean` files differ in `e5fcd8ee..1299799c` and in
  `1299799c..8b383e0b`).
- Since then the tip moved to `c2897d7f` (#110, #111). Those PRs changed only `UniversalStartup`
  and `WindowClock`, neither of which is in the delivered `ZoneRebalance`'s upstream closure
  (22 TCSlib modules, with its two new imports). `ZoneRebalance` is unchanged, and graph2 at
  `c2897d7f` gives the same 2-module replay list. My results therefore hold at `c2897d7f`.
- Snapshot: `oleans-lwalk`.
- Worktrees (detached): `review/g4/wt-tip`, `review/g4/wt-tipd` (tip plus the delivered
  file), `review/g4/wt-base` (`1299799c`, reset after the patch check).

## Checks

| # | Check | Result | Key output |
|---|---|---|---|
| 1 | Zip SHA-256 | PASS | `31b1ce63c16f413dfa2be7d3932ac684e41f1adcd45eb87c68ad1e18e4c628c6` |
| 2 | Extraction | PASS | `python3 -I review/scripts/safe_extract.py` into the new empty `review/g4/x`: 40 entries, CRC OK, no symlink or path-escape entries |
| 3 | `SHA256SUMS` | PASS | 39/39 OK; covers every file except itself |
| 4 | Shim and scripts | PASS | `evidence/runtime/executable-path.c` = `985924ad…4fba7`, not compiled or run. `evidence/probes/verify_delivery.py` and `compare_screens.py` were not run |
| 5 | Brief and dispatch | PASS | tip `briefs/s13d-fill-g4.md` with `@ANCESTOR@`→`1299799c…` is byte-equal to `infra_local/fill-dispatches/s13d-fill-g4.md` (`21c3c31f…6a4e081`) |
| 6 | Base | PASS | REPORT base `1299799ce2b5f5717f915f000dfe7ca5baa17436`, an ancestor of the tip; Lean content `e5fcd8ee` |
| 7 | Bundle | PASS | verify okay; sole prerequisite `1299799c`; `fill/s13d-g4` = `1038632b0e742d10f7e274fb2f3c29a91cc751df` (parent `1299799c`), changes only `Build/ZoneRebalance.lean` (+241/−2); bundle file byte-equal to the delivered file |
| 8 | Format-patch | PASS | `0001-Add-checked-private-G4-slot-ruler-and-one-cell-kit.patch` applies at the base and reproduces the delivered file byte for byte |
| 9 | Ownership | PASS | (a) exactly the two imports, added after line 7 (`first-edit.diff` shows them as the first edit); (b) 224 lines inserted before `/-! ### The rows -/`; (c), (d) both docstrings' last lines keep their text and gain a "**Fill appendix (§13d G4).**" paragraph (+6 and +7 lines). Everything else is byte-identical: header, data (66–123), both statements, both `sorry` bodies, the endpoint lemmas 210–330 |
| 10 | Freeze (`declfreeze.py`, `privstmt.py`) | PASS | `public before/after: 18 18`, none added or removed; `STATEMENT CHANGED: []`; the two targets change in docstring only; 18 privates added |
| 11 | Hygiene (241 added lines) | PASS | none of `#eval`/`run_cmd`/`IO`/`unsafe`/`implemented_by`/`extern`/`native_decide`/`syntax`/`macro`/`elab`/`axiom`/`admit`/`sorry`/`set_option`/`open`/`section`/`variable`/attributes; only `by decide` on numerals |
| 12 | Widths | PASS | added lines at most 95 characters; no line of the file over 100 |
| 13 | Rule 11 | PASS | no R3 row cited; all 18 privates `zr_`; no private Catalog name (the module elaborates, and the worker's constant list has none) |
| 14 | Elaboration at tip, delivered file | PASS | exit 0, 0 errors; warnings only `ZoneRebalance.lean:396:8` and `:437:8` `declaration uses 'sorry'` (the two targets) |
| 15 | Elaboration at tip, tip's own file | baseline | exit 0; `:164:8`, `:198:8` sorry warnings |
| 16 | New warnings (`warndiff.py`) | PASS | `warnings base/new: 2 2`, `new warnings: 0` |
| 17 | Axiom prints (`mkaxprobe` + 18 privates) | PASS (partial) | 36 prints. `sorryAx` only in `exists_zoneRebalanceTM` and `exists_zoneExtendTM` (`[propext, sorryAx, Classical.choice, Quot.sound]`); every private is within `[propext, Classical.choice, Quot.sound]` (`zr_cellTM`: none) |
| 18 | Admission walks (`#sorry_sources`) | PASS (partial) | `Turing.exists_zoneExtendTM: [Turing.exists_zoneExtendTM]`; `Turing.exists_zoneRebalanceTM: [Turing.exists_zoneRebalanceTM]`, i.e. each row's own open body only |
| 19 | `G4ImportProbe` at tip (as is) | PASS | exit 0, 0 errors, 0 warnings, 94/94 outputs |
| 20 | `G4ImportProbe` on the delivered module | PASS | probe body (import header dropped) appended to a copy of the delivered module: exit 0, 0 errors, 94/94 outputs, only the two target sorry warnings |
| 21 | The worker's extended probe (415 checks) on the delivered module | PASS | exit 0, 0 errors, 415/415 outputs. Warnings: the two target sorries, plus 2 Mathlib deprecations (`Int.ofNat_mul`, `Int.ofNat_nonneg`) from the worker's extra `#check`s, which are not in the source |
| 22 | Order list | PASS | `briefs/orders/s13d-fill-g4.txt`: 79 modules; `Build/Contract/Seam` (21) and `Build/Contract/Catalog` (39) precede `Build/ZoneRebalance` (43); facade last; byte-equal to the worker's `module-order.txt` |
| 23 | Sorry set | PASS (by the worker's sweep) | base `audits/logs/s13d-fill-g4-base-sorries.txt`: 37 in 16 modules, byte-equal to the worker's copy; the worker's final set has the same 37 names (modulo namespace spelling for `FinTM.lengthBitsTM_*`). A complete delivery would leave 35; this partial leaves 37. I could not re-sweep (no oleans of the delivered module); my own elaboration shows exactly the two owned warnings |
| 24 | Lint | PASS | `campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build` in `wt-tipd`: `0 FAIL, 14 WARN over 36 files`, identical to the worker's log; differs from the tip only in ZoneRebalance's INFO line (570 lines; 18 public / 18 private) |
| 25 | Downstream (graph2) | PASS | `downstream closure: 2 modules`: `Build/ZoneRebalance`, then the `TuringMachine` facade. The two new imports' oleans are present, and there is no cycle |
| 26 | Screen, before (tip) | done | script SHA `f4feac91…f878f181` verified; 10-file population byte-equal to the worker's; `declarations screened: 763; copy pairs …: 429; reproduced text: 126,953 chars` (exit 0, 296 s); byte-equal to `audits/logs/s13d-fill-g4-screen-base.txt` minus its comment lines |
| 27 | Screen, after (tip + delivery) | PASS | `declarations screened: 778; copy pairs …: 429; reproduced text: 126,953 chars` (exit 0, 300 s); `pairdiff after before`: `new at head 0; earlier-only 0`. No pair names a `zr_` declaration or any `ZoneRebalance` declaration. +15 screened declarations (3 of the 18 are under the 60-character floor) |
| 28 | Screen vs `audits/logs/s13d-fill-g4-screen-base.txt` (by name) | PASS | after vs base: `new at head 0; earlier-only 0`. My after is byte-equal to the worker's `screen-after.txt`, and my before to the worker's before |
| 29 | Size | report | 331 → 570 lines; 18 public / 0 private → 18 / 18 |

## Delivered declarations (REPORT cross-checked against the diff)

All 18 are `private`, in namespace `Turing`, and in the home. None is used by either target yet.

| Declaration | Kind | Role (REPORT; checked against the source) |
|---|---|---|
| `zr_zonePos` | def | directed slot coordinate, parameterized by side |
| `zr_read_slot` | lemma | reads a slot through the public `zonedTape_left`/`zonedTape_right` |
| `zr_capacity_pos` | lemma | `0 < zoneCapacity i` |
| `zr_slot_empty_iff` | lemma | under inner packing, slot `⊠` ⇔ length ≤ offset |
| `zr_inner_empty_iff` | lemma | innermost slot `⊠` ⇔ zone empty |
| `zr_outer_full_iff` | lemma | outermost slot occupied ⇔ zone full |
| `zr_room_iff` | lemma | slot at `cap − m` is `⊠` ⇔ room for `m` |
| `zr_scan_index` | lemma | the physical scan identifies `zoneShiftIndex` (cites the public `zoneShiftIndex_eq`) |
| `zr_scan_short` | lemma | all scanned slots empty ⇒ `zoneRebalance` is the identity (`zoneRebalance_of_le`, `zoneShiftIndex_eq_length_iff`) |
| `zr_ruler_length` | lemma | `zoneCapacity (i−1) = 2^i` for `i ≥ 1` |
| `zr_extent_cost` | lemma | `zoneStart (i+1) ≤ 6(2^i + 1)` |
| `zr_mirror_tape` | lemma | swapping sides reflects `zonedTape` about home (proved once; the mirror route the brief prescribes) |
| `zr_extend_cell` | lemma | `zonedTape_extend` specialized to the new zones' cells |
| `zr_ruler_tail` | lemma | after one ruler-head step, the tail satisfies the walk's word premise |
| `zr_cellTM` | def | the permitted one-cell leaf, factoring the three leaves (move / slot guard / write); its docstring says why no public row serves |
| `zr_cellPost` | def | the leaf's exact endpoint |
| `zr_cell_step` | lemma | its one step, by the public `step_of_tapeAction_move`/`_write` |
| `zr_cellContract` | def | the leaf as a `Contract` (time 1, two verdict exits, cut at 0, endpoint-hull envelope); built directly, since the exit set is not a singleton |

No bridge, ruler builder, column move, scan loop or host is present. In particular there is no
contiguous layout-copy helper, so there is no overlap with F3's (unwritten) clock writer.

**Phase reached:** none complete. Phase 1 is only partly done: the imports, the one-cell leaves
and part of the kit are in; the bridges and `exists_zoneExtendTM` are not. Phase 2 has not
started; only the pure scan/guard semantics are proved. REPORT's "Phase 1 reached the
independently proved shared kit" should be read in that sense.

## E1 assessment (verified)

- **Layout.** `fieldsTape` and `fieldOffset` are plain defs (`Build/Catalog.lean:11691`,
  `:11699`). The public lemmas are `fieldOffset_succ`, `fieldOffset_cons_succ`,
  `length_joinFields_add_one`, `fieldOffset_add_length_le`, `fieldsTape_field` and
  `fieldsTape_cons_shift`. None gives:
  - `fieldOffset fs 0 = 0`;
  - `fieldsTape fs p = none` for `p < 0` or past the layout;
  - `fieldsTape [] p`.

  `fieldsTape_field` is relative to the unknown `fieldOffset fs j` and covers only one cell on
  either side of a field. The maintainer's recommended bridges (`tools/home.lean.txt`, stubs in
  the pre-ship overlay) need exactly these facts, so they cannot be proved without unfolding
  Catalog defs.
- **Contracts.** `seekEndTM_contract`, `seekStartTM_contract`, `skipTM_contract`,
  `skipBackTM_contract`, `walkTM_contract`, `copyMapTM_contract`, `scanTM_contract` and
  `clearTM_contract` are `def … : Contract … := framedContract …` (or built directly). Their
  `pre`/`time`/`post` are visible only by unfolding the def and `framedContract`.
  - The only public facts about them are `*_frames` and `*_traj` (for clear, copyMap,
    transferMap and sweep).
  - There is no `@[simp]` field-equation lemma.
  - The same holds for `Contract.seq`/`inPhase`/`branch`/`trans` in `Contract/Basic`.

  So the brief's mandate ("your rows are stated as contracts: build them by these") cannot
  meet the literal rule 10.
- The walk gate's own record shows that `tapeAction`-unfolding proofs (`skipTM_eq_walkTM` by
  `rfl`) are normal inside Catalog. The rule's evident intent is to forbid re-walking machine
  transition tables, not to make specification data unreadable.

**Ruling options** (as analysed; **the user ruled (b) on 2026-10-16**, see "What the landing PR
needs"):
- (a) Extend rule 10's carve-out. Allow definitional reduction (`rfl`/`dsimp only`/`simp only`
  on the def names) of the layout data (`joinFields`, `fieldsTape`, `fieldOffset`), of
  `framedContract`, `seekPost`, `sweepPost`, the `*_contract` defs and the `Contract`
  combinators' fields. Keep the ban on machine definitions and transition tables
  (`tapeAction`, the row machines, `Seam` hosts).
- (b) Pre-land public field-equation lemmas for each contract used, plus layout base/boundary
  lemmas. This is a separate PR into `Build/Catalog` and `Build/Contract/*`, with their replay
  closure.

The user chose (b), with F3's three facts folded into the same API PR. One PR therefore
unblocks both G4 and the F3 continuation.

## Walk convention

Applied correctly in the kit and in REPORT:
- `zr_ruler_tail` takes the walk's word premise at head `q` for a nonempty `w` to the premise
  at `q + dir` for `w.tail`, in exactly `walkTM_contract`'s `pre` shape
  (`∀ p : ℕ, p ≤ |w| → tape (pos + dir·p) = bufferTape w p`).
- So one leaf step on the ruler head, then a walk over the tail of length `m − 1`, moves the
  other heads `(m−1)+1 = m` cells and the ruler head `m + 1`.
- REPORT states this, including the one-cell ruler (empty tail) and that displacement 0 needs
  a stationary branch.
- No walk is instantiated yet. Applying the lemma will itself need `walkTM_contract`'s `pre`,
  which is E1 again.

## Discrepancies between REPORT.md and my measurements

- None in hashes, commits, tree content, counts (570 lines; 18/18), axiom prints, admission
  walks, probe counts (94; 415) or lint.
- REPORT's final sweep and bootstrap (79/79, 37 sorries) were not reproducible here (no
  `lake build`). It openly records interrupted attempts (bus errors while the cache was being
  rewritten) and counts only the resumed and fresh runs. That is acceptable but should be noted.
  My single-module elaboration at the tip agrees for the owned file.
- The phase wording, as noted above.
- Observation: the worker's 415-check probe uses two deprecated Mathlib names
  (`Int.ofNat_mul`, `Int.ofNat_nonneg`). These are only in its probe; the delivered source has
  no warning.

## Duplication

- New pairs: **none** (by name, after vs before and after vs the brief's base; 429 = 429).
  No cross-file or in-file pair involves an owned-file declaration.
- The known hazards show no pair with the kit: `rt_copyMachine`/`exists_fieldsCopyTM`,
  `zoneSide_cascadeRight` and family, and the mirror. The mirror is proved once
  (`zr_mirror_tape`), and the guards are side-parameterized.
- No contiguous layout-copy helper exists, so there is nothing to reconcile with F3's writer.
- "new copies: none" is confirmed.

## What the landing PR needs

- **E1 is ruled (user, 2026-10-16): no unfolding (option (b)).** This is also the rule for
  future briefs.
  - Before the G4 continuation, a maintainer API PR adds public equation lemmas for:
    - the row contracts (`pre`, `time`, `post`, `lo`/`hi` of `seekEndTM_contract`,
      `seekStartTM_contract`, `skipTM_contract`, `skipBackTM_contract`, `walkTM_contract`,
      `copyMapTM_contract`, `transferMapTM_contract`, `scanTM_contract`, `clearTM_contract`,
      through `framedContract`);
    - the `Contract` combinators' fields (`Contract.seq`, `inPhase`, `branch`, `trans`, and
      the `release` adapters);
    - the layout's base and boundary facts (`fieldOffset fs 0 = 0`, `fieldsTape [] p = none`,
      `fieldsTape fs p = none` for `p < 0` and past the layout end);
    - F3's three facts (a `RecordAt` eliminator/introduction, `recordLength`'s formula,
      `n + 2 ≤ 2 ^ posWidth n`).
  - The continuation brief then cites those lemmas. Rule 10 stays as written.
  - With those lemmas, the two recommended layout bridges become provable without unfolding
    `Build/Catalog`. The kit's `zr_ruler_tail` already has `walkTM_contract`'s `pre` shape.
- **This partial lands now, once the screens are clean** (user, 2026-10-16). It adds no
  admission and changes no statement.
- **Commit:** `1038632b0e742d10f7e274fb2f3c29a91cc751df` (one commit on `1299799c`), from
  `fill-s13d-g4.bundle` or the patch. It touches only
  `TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean`, which is unchanged
  `1299799c`→tip, so it applies cleanly.
- **Replay list:** `TCSlib/Complexity/TuringMachine/Build/ZoneRebalance`, then
  `TCSlib/Complexity/TuringMachine`. The two new imports are upstream and already in the
  snapshot. The facade imports `UniversalStartup` (changed by #110), so replay against
  `oleans-lf3p`. `ZoneRebalance` itself elaborates identically against either snapshot.
- **Status text:**
  - The module header's statement-gate status stays accurate: both rows are open.
  - Both appendices say that contract assembly or bridges are blocked "under ground rule 10"
    and cite "escalation E1 in `REPORT.md`". After the ruling, reword them, or have the
    continuation do it.
  - A library docstring pointing to a delivery `REPORT.md` is not resolvable in the
    repository. Consider replacing it with the audit path where the report is archived.
- **The 18 helpers are unused until the continuation** (no warning results).
  - Promotion candidates per REPORT: `zr_cellTM`/`zr_cellContract` (a generic one-cell
    Catalog leaf), `zr_ruler_tail`, `zr_mirror_tape`, the slot characterizations, and the
    two (unwritten) bridges.
- **Expected sorry count after landing:** unchanged (37 over the 79-module order; the campaign
  total is unchanged).
