# Review — §13d G4, continuation 2 (`Build/ZoneRebalance.lean`), delivery `fill-s13d-g4-cont2.zip`

**Verdict: partial (0/2), landable as a partial.** Both rows keep their original `sorry` bodies.
The delivery is the first composed machine of the zone layer: `zr_rightPassContract`, one
contract for the whole positive-level right pass of the extension row, built only from public rows
joined by the public seam (`Contract.seq`) and re-wrapped by `Contract.ofSegment`. It comes with
its exact precondition (`zoneRowPre`), its exact time `zoneStart ℓ + 10·2^ℓ + 23` and the bound
`32·(2^ℓ + 1)`. `zr_left_two_walks` is restated to the amended left route.

What passes:
- every integrity, ownership, freeze and hygiene check;
- elaboration at the base, at the tip of the dispatch (`397763c8`) and at the current tip
  (`64e2dd9e`, after #140);
- the axiom and admission walks (`sorryAx` only through the two targets' own bodies);
- the rule-10 seal test (56 other-file definitions sealed, with failing controls) and the
  rewrite-argument inspection; rule 11;
- the import probe (338 + 101 names), the 81-module sweep record, lint, and the v3 screen;
- **the environment test: addendum v2.3's narrowed cache step succeeded on its first use** (35 roots,
  967 files, no failure, no retry, no E-RES).

Three findings, none blocking:
- **F1 (progress; claim precision).** Checkpoint 1.1 is *composed*, not *characterized*. No lemma
  states the right pass's endpoint (which cells it writes, where the heads end) or bounds its
  envelope: `zr_rightPassContract`, `zr_writeHalvesContract` and `zr_outerHalfContract` have no
  `post`, `lo` or `hi` lemma. The report's body says so ("does not assert the final extension's
  endpoint or `zoneRowLo`/`zoneRowHi` yet"); its headline "complete" overstates it. Checkpoints
  1.2, 1.3 and 1.6 all need that endpoint. The two statements are written out and elaborate
  (`out/cont3-targets.out`); by hand from the field equations they hold.
- **F2 (public-facing text, cosmetic).** The extension's status paragraph says "The corrected left
  displacement…": "corrected" is session narrative. A rewording is below. No campaign label, path
  or date was added anywhere.
- **F3 (cosmetic).** Two double blank lines (head 636–637 and 1144–1145). `zr_adjustedBack_post`
  (a 21-line proof) has no literal "Proof sketch". The report's "checked level-one example" has no
  shipped Lean artifact. I checked it (`out/levelone.out`).

## Inputs

| Input | Identity |
|---|---|
| Zip (final) | `exchange/inbox/fill-s13d-g4-cont2.zip`, SHA-256 `d6f9dedb…ed4281dd`; 11 members (`zip-sha.txt`, `zip-list.txt`) |
| Zip (checkpoint) | `exchange/inbox/fill-s13d-g4-cont2-cp1.zip`, `64278319…5048932f4`. **Identical** Lean file, bundle, patch, axiom and bootstrap logs, screens and shim. Only `REPORT.md` (title and 3 lines), `final-sweep.log` (7 runs, against the final's 85) and `SHA256SUMS` differ (`cp1-vs-final.txt`). Reviewed: the final only |
| Extraction | `$S/inbox-g4c2/fill-s13d-g4-cont2/`: every member byte-equal to the zip, no unsafe entry, CRC OK (`zip-vs-extracted.txt`) |
| Brief | `exchange/outbox/fills/s13d-fill-g4-cont2.md`, `3584091a…`. Equal to `campaign/fills/s13d/briefs/s13d-fill-g4-cont2.md` (at the base and at the tip) with its three `@ANCESTOR@` replaced by the base (`brief-check.txt`) |
| Addendum | `exchange/outbox/fills/fill-environment-addendum.md`, v2.3, `1ea7a376…`. Equal to the tip's `campaign/standards/` copy; the base still holds v2 (`brief-check.txt`) |
| Base | `96d60278e4fde29b986ec1d0e59cd07f768fe28a` (records commit); TCSlib tree `a8174885` = `dac6b3b0`'s (#124) (`trees.txt`) |
| Head | `refs/review/g4-cont2` = `6fe3bf884ecbc0fd30a7f017665530e8a5dfdd7b`, fetched from the bundle |
| Tips | At dispatch: `397763c8` (TCSlib = `e9e97970`'s, #132), snapshot `oleans-l132b`. **Now: `64e2dd9e`** (#140 merged as `e2bc85eb` during this review; TCSlib `0fcc0e49` = #140's replayed head `7c963897`'s), snapshot `oleans-lbw2` (`tip-moved.txt`) |
| Worktrees | `wt-base`, `wt-head`, `wt-tipd` (`397763c8` + patch), `wt-tip64` (`64e2dd9e` + patch), each with the `.lake/packages` link |

Every path below is relative to `$S/review/g4-cont2-fill/out/` unless it says otherwise. Lean
ran only through `tools/leanelab.sh`, one elaboration at a time. Screens ran one at a time, each
only when no other screen ran, under `nice -n 10` (`scripts/run-screens.sh`). No build or cache
command was run. The shim `evidence/runtime/executable-path.c` (`985924ad…4fba7`, equal to the
addendum's) was neither compiled nor run. Every delivered Lean file was read before elaboration.

## (a) Integrity and scope

| # | Check | Result | Evidence |
|---|---|---|---|
| 1 | `SHA256SUMS` | PASS: 10/10 OK, covering every member except itself (the same for cp1) | `sha256sums-check.txt` |
| 2 | Bundle | PASS: `verify` okay; sole prerequisite `96d60278…`; head `fill/s13d-g4-cont2` = `6fe3bf88…` | `bundle-verify.txt` |
| 3 | Head commit | PASS: one commit, sole parent exactly the base, hash as in REPORT; touches only `Build/ZoneRebalance.lean` (+525/−21) | `head-commit.txt` |
| 4 | Patch | PASS: `0001-…patch` applied at the base to a temporary index gives the head tree `ca72bca6` | `patch-check.txt` |
| 5 | Delivered file | PASS: byte-equal to the head blob `77c9119d` (SHA-256 `6ef187fd…`) | `file-agreement.txt` |
| 6 | Worker's start | REPORT: campaign branch at `a2ed2694`, ancestor test passed, branch made at the base. `a2ed2694` exists, contains the base, and is an ancestor of the tip | `tip.txt` |
| 7 | Owned regions | PASS: every change inside (a) the home (the restated `zr_left_two_walks`, 560–578, and 508 lines inserted before `/-! ### The rows -/`, base 640), (b) the rebalance status paragraph (680–685) or (c) the extension status paragraph (721–727). 0 outside. Both `sorry` bodies untouched | `regions.txt`, `worker.diff` |
| 8 | Freeze (`declfreeze.py`) | PASS: public 18 → 18, none added or removed, no `STATEMENT CHANGED`; the two targets change in their status paragraphs only (authorized) | `declfreeze.txt` |
| 9 | Privates (`privstmt.py`) | PASS: 31 → 65; 34 added, none removed; `STATEMENT CHANGED` only `zr_left_two_walks` (the brief's "restate or remove"); the other 30 inherited are byte-identical | `privstmt.txt` |
| 10 | Code lines (`stmtcheck.py`) | PASS: of the base's 539 code lines, the only 2 missing are `zr_left_two_walks`'s two old statement lines | `stmtcheck.txt` |
| 11 | Hygiene (added lines) | PASS: no `sorry`, `admit`, `axiom`, `unfold`, `delta`, `change`, `set_option`, `open`, `section`, `variable`, attribute or `native_decide`. `decide` only on `Fin 2` numerals (`0 ≠ 1`, `1 ≠ 0`). `rfl` only as an `obtain` pattern, in `⟨false, rfl⟩` (a `Set.range` witness), in `Set.mem_singleton_iff.mpr rfl`, and closing syntactic goals after `split_ifs` (lines 811, 1107; sealed, see (c)) | `hygiene.txt` |
| 12 | Names | PASS: 34 new privates, all `zr_`; no public declaration added | `hygiene.txt`, `privates-head.txt` |
| 13 | Imports | PASS: unchanged (lines 6–9) | `worker.diff` |
| 14 | Widths | PASS: added lines at most 95 characters; whole file at most 99 (code points, not bytes) | `widths.txt` |
| 15 | Size | 861 → 1365 lines; 18 public / 31 → 65 private (lint INFO line) | `lint-build-head.out` |

**The 34 new privates** (head lines; `decl-lines.txt`, `decl-sizes.txt`):
- data and words: `zr_RightData` (639, an abbrev, `Σ n, Fin k → ZoneContents (n+1)`), `zr_rightFields`
  (642), `zr_rightWord` (646), `zr_rulerWord` (1081);
- the ruler prefix: `zr_rightSeekContract` (651), `zr_rightSeek_back_pre` (665),
  `zr_rightSeekBackContract` (686), `zr_rightSeekBack_post` (702), `zr_rulerCopyContract` (732),
  `zr_rulerCopy_skip_pre` (738), `zr_rulerSkipContract` (753), `zr_rightSeekBack_ruler_pre` (758),
  `zr_rightRulerContract` (779), `zr_rightRuler_pre` (790), `zr_constantCopy_cell` (798),
  `zr_rightRuler_post` (818);
- the adjusted walk: `zr_rulerStepContract` (863), `zr_rulerStep_walk_pre` (880),
  `zr_adjustedWalkContract` (900), `zr_adjustedWalk_post` (917), `zr_adjustedWalk_back_pre` (951),
  `zr_adjustedBackContract` (970), `zr_adjustedBack_post` (982);
- the half writes: `zr_halfCopyContract` (1014), `zr_innerCopyContract` (1020),
  `zr_innerCopy_adjusted_pre` (1028), `zr_adjustedBack_copy_pre` (1048), `zr_outerHalfContract`
  (1066), `zr_writeHalvesContract` (1072), `zr_rightRuler_write_pre` (1088);
- the pass: `zr_rightPassContract` (1111), `zr_rightPass_pre` (1116), `zr_rightPass_time` (1123),
  `zr_rightPass_time_le` (1138).

The table in REPORT ("Declaration inventory") matches this list name by name and role by role.

## (b) Elaboration and axioms

| # | Check | Result | Evidence |
|---|---|---|---|
| 16 | Head against `oleans-lseam2` | PASS: exit 0, 0 errors; warnings only `:1191:8` and `:1232:8` `declaration uses 'sorry'` (the two targets); 9 s | `elab-head-lseam2.out` |
| 17 | Base baseline | exit 0; `:686:8`, `:728:8` (the same two targets) | `elab-base-lseam2.out` |
| 18 | Axioms (in-module copy, `#print axioms` for all 65 privates and both targets) | PASS (partial): both targets `[propext, sorryAx, Classical.choice, Quot.sound]`; every private within `[propext, Classical.choice, Quot.sound]` (`zr_cellTM`: none). Name by name equal to the worker's `axioms.log` (67 lines) | `ax-head.out`, `ax-mine-norm.txt` = `ax-worker-norm.txt` |
| 19 | Admission walk | PASS: `exists_zoneRebalanceTM: [Turing.exists_zoneRebalanceTM]`, `exists_zoneExtendTM: [Turing.exists_zoneExtendTM]`. No `sorryAx` anywhere else | `ax-head.out` |
| 20 | External privates, equation lemmas | none reached from any of the 65 privates (`EXT` lines, 65/65 clean); 134 TCSlib constants reached in all | `ax-head.out`, `extlist-tcslib.txt` |
| 21 | The same probe at the tip | identical output against `oleans-l132b` | `ax-tipd.out` |
| 21a | Import probe (the brief's `G4C2ImportProbe.lean.txt`, 338 `#check`s, appended to the delivered module), plus Expansion A (39 TCSlib constants reached from the 35 new or changed privates and absent from the probe) and Expansion B (the worker's 62 extra names) | PASS: 0 errors, 439/439 outputs, only the two target sorry warnings | `importprobe-head.out`, `probes/G4C2ImportProbeOnHead.lean` |
| 21b | Cited beyond the probe | Expansion A (`extlist-new-not-in-probe.txt`). Lemmas: `Cfg.ext`, `Contract.exit_mem`, `FinTM.bufferTape_nat`, `length_joinFields_add_one` (the last via the inherited bridge). The rest are types, constructors, projections, instances, machines and primitives occurring in statements. All are public at the base; no external private is reached (row 20). The delivery ships no probe file: its expanded run is the `G4ExpandedProbeFinal` section of `final-sweep.log` (status 0), with the extra names listed there. One of them, `norm_num`, resolves to the tactic's `ParserDescr`, a harmless artifact of the worker's inventory | `worker-expanded-probe.txt`, `worker-probe-extra-names.txt` |

## (c) Correctness, route and rule 10

**What `zr_rightPassContract` is.** For positive-level data `D = ⟨n, z⟩` (levels `0..n`, so
`ℓ = n + 1`; `m = zoneCapacity n = 2^ℓ`; `N = zoneStart ℓ`), the printed machine is
(`levelone.out`, `#check`):

```
seam( seam( seam(seekEndTM 0, skipBackTM 0),            -- home → N → zone ℓ−1's first cell
            seam(copyMapTM 0→1 [merge ↦ inl false],      -- the ruler: m cells on scratch
                 skipTM 0) ),                             -- back to N
      seam( copyMapTM 1→0 [merge ↦ inr (· ↦ some none)], -- inner half [N, N+m)
            seam( seam( seam(zr_cellTM 1 (+1), walkTM 1 all (+1)),   -- the adjusted walk by m
                        skipBackTM 1 ),                  -- ruler head back to q
                  copyMapTM 1→0 [merge ↦ inr (· ↦ none)] ) ) )       -- outer half [N+m, N+2m)
```

This is the brief's binding route, step for step: `seekEnd` → `skipBack` → mapped copy of zone
`ℓ − 1` as the ruler → `skip` → constant copy (inner) → adjusted walk (the one-cell leaf, then
`walkTM` on the tail; the walk gate's convention) → `skipBack` on the ruler → constant copy
(outer). The only leaf is the inherited `zr_cellTM`. There is no counter tape, no extra tape, no
private host, no round and no trace: the added lines never mention `runFrom`, `Round`,
`iterate`, `inPhase` or a host (`rule7.txt`). Every composite is `Contract.seq` (the public seam,
one stationary dispatch step) re-wrapped by `Contract.ofSegment` only to normalize the exit set.

**What is proved about it.**
- *The links* (each phase's precondition at the previous endpoint), all through published
  equations:
  - `zr_rightSeek_back_pre`: after `seekEnd`, the last old zone is delimited behind the head, by
    `zr_right_offset` and `zonedTape_right_word`;
  - `zr_rightSeekBack_ruler_pre`, `zr_rulerCopy_skip_pre`: the source zone stays delimited;
  - `zr_rightRuler_write_pre`: the scratch ruler is delimited, from the blank scratch of
    `zoneRowPre` and the ruler's cell formula;
  - `zr_rulerStep_walk_pre`, `zr_adjustedWalk_back_pre`, `zr_innerCopy_adjusted_pre`,
    `zr_adjustedBack_copy_pre`: the ruler survives the writes and the walk.
- *Closed-form endpoints of the sub-composites*:
  - `zr_rightSeekBack_post`: the zoned head at `zoneStart n`;
  - `zr_rightRuler_post`: tape 0 unchanged, scratch `[q, q+m)` = `inl false`, the zoned head at
    `N`;
  - `zr_adjustedWalk_post`: the zoned head `+m`, scratch `+m+1`;
  - `zr_adjustedBack_post`: only the zoned head `+m`;
  - `zr_constantCopy_cell`: one formula for every constant mapped copy.
- *Precondition* `zr_rightPass_pre`: exactly `zoneRowPre ⟨n+1, z⟩`.
- *Time* `zr_rightPass_time = zoneStart ℓ + 10·m + 23`. I re-derived it from the rows' time
  equations (`Contract/Catalog.lean`):
  - seek `N + 1`;
  - skip back `m + 3`, twice;
  - copies `2m + 2`, three times;
  - skip `m + 1`;
  - leaf `1`;
  - walk `(m − 1) + 1`;
  - eight seams `+1` each.

  That makes `10m` and `15 + 8 = 23`.
- *Bound* `zr_rightPass_time_le ≤ 32·(2^ℓ + 1)`, through `zr_extent_cost`.

**What is not proved (F1).** No lemma gives `(zr_rightPassContract x).post`,
`(zr_writeHalvesContract x).post` or `(zr_outerHalfContract x).post`, and none bounds any composite's
`lo`/`hi` (`endpoint-coverage.txt`). The contract is sound by construction. What it writes is
known only by unfolding the composite. The two statements continuation 3 needs elaborate
(`probes/G4C2Targets.lean`, `cont3-targets.out`; `sorry` there only):
- **Endpoint.** The state is `some (inr (inr (inr done)))`.
  - Tape 0: `[N, N + 2m)` holds `inr (· ↦ if q < N + 2^ℓ then some none else none)`, and every
    other cell is unchanged.
  - Scratch: `[q, q+m)` holds `inl false`.
  - Heads: tape 0 at `N + m`, every other head and field unchanged.
- **Envelope.** Tape 0 stays within `±zoneStart (ℓ + 1)`:
  - the hull's minimum is `≥ 0`;
  - its maximum is `N + 2m = zoneStart (ℓ+1) − 1`.

Both follow by hand from the field equations: `sweepPost`, `seekPost`, `walkTM_contract_post`,
and the copies returning their heads. Also note: the pass's exit set is the nested image
`Option.map Sum.inr '' (…{some SweepPhase.done})`, not a singleton. Composing it by
`Contract.seq` needs one more `Contract.ofSegment` re-wrap, as the worker did for every
intermediate composite.

**Later checkpoints: what is claimed and what holds.**

| Claim (REPORT) | Holds? | Evidence |
|---|---|---|
| Left displacement: unadjusted full-ruler walk (`2^ℓ + 1`) then adjusted walk (`2^ℓ`), from `2 − zoneStart ℓ` to `1 − zoneStart ℓ − zoneCapacity ℓ` | **Yes, as arithmetic only**: `zr_left_two_walks` states exactly `−fieldOffset(left layout) ℓ − (2^ℓ+1) − 2^ℓ = −(zoneStart ℓ + zoneCapacity ℓ − 1)`. This is the brief's first option. No walk is composed, as the report says | head 565–575 |
| "The checked level-one example gives −8, not −7" | **True, but not shipped.** I checked it in-module: the seek stops at `−3`; the amended route reaches `−8`; two adjusted walks would stop at `−7` | `levelone.out`, `probes/G4C2LevelOne.lean` |
| Return home, ℓ = 0 branch, cleanup, assembly, phase 2 | open, as reported; nothing is claimed | — |

**Rule 10 (no unfolding of other files' definitions).**
- **Seal test** (`scripts/mkseal2.py`, `probes/G4C2SealHead.lean`):
  - **Method.** The whole home (head 127–1145, all 65 privates) runs inside a section with
    `attribute [local irreducible]` on 56 other-file definitions (`seal-list.txt`). The list is
    the worker's 51 plus 5 more that my dependency walk found: `Cfg.inputSymbol`,
    `instDecidableEqSeekPhase`, `instDecidableEqSweepPhase`, `zoneShiftInW`, `zoneShiftOutW`. The
    walk lists every semireducible, non-projection TCSlib definition reached
    (`sealcand-all.txt`).
  - **Controls.** Two `rfl` controls sit inside the section:
    `(skipTM_contract 0 x).time w d = w.length + 1` and `zoneStart 0 = 2`. They must fail there,
    and they do. The same two after the section must pass, and they do.
  - **Result.** Exactly the two control errors, and the two target sorry warnings; nothing in the
    home fails (`seal-head.out`). The same holds at the tip against `oleans-l132b`
    (`seal-head-tip.out`).
  - This covers the `rfl`/`split_ifs` closings of row 11: none closes by unfolding a sealed
    definition.
- **Argument inspection.** The added `rw`/`simp`/`simpa`/`norm_num` lists hold 97 distinct
  identifiers (`rwargs.txt`); each was resolved in-module (`kinds.out`):
  - every TCSlib one is a **theorem**: the contract field equations of `Contract/Catalog`,
    `Contract/Basic` and `Contract/Seam`, `Cfg.mapState_*`, `FinTM.bufferTape_nat`/`_eq`,
    `zoneCapacity_eq`, `zoneCells_length`;
  - the definitions passed are all this file's own: `zoneRowPre` and the `zr_` contracts and
    words;
  - the rest are locals (`he`, `hj`, `hn`, `hpos`, `hz.*`) or core/Mathlib lemmas.

  There is no `unfold`, `delta`, `change` or `show` on another file's definition. REPORT's
  inspection table (90 entries) agrees.
- **Rule 11.** No R3 row (`hygiene.txt`); no external private is reached (`ax-head.out`). All new
  names are `zr_`.

## (d) Escalations and promotion candidates

**Escalations: none new, and I agree.** The left-pass escalation of continuation 1 is resolved by
the brief's amendment (verified above). No API is missing for the next checkpoints. The worker's
return-home note reads correctly against the rows' equations:
- `skipTM` over the outer half lands at `N + 2m + 1 = zoneStart (ℓ+1)`, where `skipBackTM` over
  zone `ℓ` starts;
- each `skipBackTM`'s endpoint (the word's first cell) is the next one's start;
- home is the only field whose second cell is blank.

**Promotion candidates** (REPORT's list; my assessment):
- `zr_adjustedWalkContract`/`zr_adjustedBackContract`, "walk exactly `|w|`, optionally rewinding
  the ruler": **the strongest candidate.** It is the walk gate's convention as a row. The left pass
  needs its leftward form, so parametrize it by direction now, not as a mirrored copy (the brief's
  90% mirror hazard).
- `zr_constantCopy_cell`: a constant-merge corollary of `copyMapTM_contract_post_workTapes`. It
  is generic over `Γ` in all but its signature and would sit in `Contract/Catalog`.
- `zr_rulerCopyContract`/`zr_rulerSkipContract`: the ruler builder (a constant mapped copy).
- `zr_writeHalvesContract` (two constant blocks) and `zr_rightPassContract`: zone-specific. They
  stay private until the row is filled (ruling 5).
- Inherited: `zr_cellContract`, the layout bridges, `zr_mirror_tape`. Unchanged.

## (e) Duplication and lint

| # | Check | Result | Evidence |
|---|---|---|---|
| 22 | Screen v3 script | SHA-256 `f4feac91…d878f181`, the same at base, head and tip and in the main repo | `screen-script-sha.txt` |
| 23 | Before (base, the brief's 10-file population) | `declarations screened: 808; copy pairs …: 439; reproduced text: 127,994 chars` (exit 0, 290 s). Byte-equal to the worker's `screen-before.txt`, and to `campaign/fills/s13d/logs/s13d-fill-g4-cont2-screen-base.txt` minus its comments | `screen-before.txt`, `.status` |
| 24 | After (head) | `838; 478; 137,237 chars` (exit 0, 302 s). Byte-equal to the worker's `screen-after.txt` | `screen-after.txt`, `.status` |
| 25 | New pairs (`pairdiff.py`, by name, against before and the repo base) | **39, all in-file (`ZoneRebalance` ↔ `ZoneRebalance`); no cross-file pair; 0 pairs removed. Maximum 81%, none at 90% or above: new copies, none.** The 39 are line for line REPORT's justified table. The accepted `zr_pair_pass`/`zr_inPass_out` pair is unchanged | `screen-compare.txt` |

On the pairs:
- **The top two.** `zr_rightRulerContract` reproduces `zr_rightSeekBackContract` at 81%, and
  `zr_halfCopyContract` reproduces `zr_rulerCopyContract` at 80%. They share the composite
  adapter
  `let R := (…).seq (…) link (…); Contract.ofSegment R.pre R.time R.post R.lo R.hi (by simpa only [Set.image_singleton, Option.map_some] using R.segment …) (… R.exit_mem …)`
  (four instances), and one `copyMapTM_contract` instance line respectively.
- **The rest (50–74%)** pair link lemmas and endpoint lemmas that share public getter
  applications (`Cfg.mapState_*`, `seekPost_*`, `Function.update_*`) but read different rows.
  The worker's one-line justifications are accurate.
- **The known hazards:**
  - no pair with `rt_copyMachine`/`exists_fieldsCopyTM` (`RecordTable`);
  - none with `Build/Zone`'s cascade family;
  - no mirrored direction yet;
  - no contiguous copy of a layout's cells: each copy is a single public mapped-copy row writing
    one constant block, so there is nothing to reconcile with F3's clock writer.
- **Note for continuation 3.** No public helper normalizes `Contract.seq`'s exit set
  `Option.map Sum.inr '' {some e}` to `{some (Sum.inr e)}`. A search of `Build/Contract/*` and
  the TCSlib tree found none. The four-line adapter will recur with every new composite, so
  factor it once: a private `zr_` helper, or, if the maintainer prefers, a published `seq`
  corollary in an API PR. This stops it from drifting toward the 90% line.

| # | Check | Result | Evidence |
|---|---|---|---|
| 26 | Lint, `TuringMachine/Build` (the brief's scope) | `0 FAIL, 31 WARN over 38 files` (base `0 FAIL, 30 WARN`). The new WARN is `ZoneRebalance.lean 1365 lines > 1000`. Ground rule 8 and the standing decision say that size alone is no driver. The head output is line-equal to the worker's `final-lint.log` | `lint-build-base.out`, `lint-build-head.out` |
| 27 | Widths | no line over 100 characters (added max 95, file max 99) | `widths.txt` |
| 28 | Docstrings | All 34 new privates have docstrings. Seven carry a "Proof sketch". Of the proofs over ~20 lines, only `zr_adjustedBack_post` (21 lines) lacks the label (F3) | `decl-sizes.txt` |
| 29 | Public-facing text | 79 added comment or docstring lines; none carries a campaign label (G4, §13d, checkpoint, phase number, brief, gate, finding, round, escalation), path or date. The only narrative word is "corrected" (F2) | `public-text.txt` |

**The two status paragraphs** are headed `**Implementation status.**` and are mathematical, as the
brief asks. Suggested landing rewording of the extension's (F2, and F1's precision):

> **Implementation status.** A positive-level right-pass contract composes the seek, skip,
> ruler copy, half-zone writes, adjusted walk and scratch rewind, with its exact precondition and
> time (the right-layout extent plus ten half-capacities and twenty-three control steps); its
> endpoint equation and envelope bound are not yet stated. The left displacement, an unadjusted
> walk followed by an adjusted walk across the separating blank, is proved as arithmetic. The
> return-home rounds, the left pass, the zero-level branch, ruler cleanup and the assembly of the
> complete extension remain open. Only this target's body is admitted.

The rebalance paragraph can stay as delivered.

## (f) Environment (v2.3)

**Addendum v2.3's cache step succeeded on its first use.** The narrowed fetch was enough for the
whole 81-module sweep. Evidence: the `ENVIRONMENT EVIDENCE` sections appended to
`logs/bootstrap.log` (`environment-v23.txt`).

| Item | Record |
|---|---|
| Host | `nproc` 9; cgroup v2 `memory.max` 8,589,934,592; `/workspace/scratch/…`, `/tmp` and `/root` on `overlay` (disk-backed) |
| Initial preflight (00:40:05Z) | headroom `8,589,934,592 − (anon 135,479,296 + kernel 18,190,336 + shmem 0)` = 7.857 GiB (floor 4); disk 31,966,261,248 B = 29.77 GiB (floor 12); OOM 0/0. **PASS** |
| Re-check before the cache (00:42:05Z, after the toolchain) | headroom 7.594 GiB; disk 26.03 GiB (floor 8, v2.2's rule); `memory.current` 4.53 GB is page cache (`file` 4.09 GB), correctly not counted. **PASS**. The raw `memory.stat` and the arithmetic come from two close samples, as REPORT notes |
| Lean start | pinned 4.25.0 failed with `failed to locate application`; the Part 2 shim (hash as authorized) gave `Lean (version 4.25.0, … commit cdd38ac5…)`. `LD_PRELOAD`, `LEAN_SYSROOT` and `LAKE_HOME` were scoped to Lean/Lake |
| Packages | 11 materialized packages match `lake-manifest.json` (URL and revision); the 4 inactive doc packages were not materialized (`package-pins-check.txt`) |
| Roots | 35 `Mathlib.*` roots; **identical to my own extraction** from the order list by the addendum's command (`mathlib-roots-mine.txt` = `mathlib-roots-worker.txt`) |
| Cache command (REPORT) | `TAR_OPTIONS=--no-same-owner lake exe cache get $(cat evidence/logs/mathlib-roots.txt)` |
| Fetched | `Attempting to download 967 file(s)` → `Downloaded: 967 file(s) [attempted 967/967 = 100%]`, `Decompressing 967 file(s)`, `Unpacked in 1809 ms`, `Completed successfully!`. Zero `fail`/`error`/`403`/`retry`/ENOSPC lines. **No retry, no cleaned retry, no E-RES** |
| Checks after the cache | empty-olean scan: empty; cache probe `G4CacheProbe`: status 0 (its source is not shipped, so which root it imported is unverified) |
| Lake activity in the cache step | 17 `✔ [n/20]` jobs compile the cache executable itself (`Cache.*`, 3 `Batteries` modules, `cache:exe`); then `Fetching ProofWidgets cloud release… done!` (v2.1's allowed internal validation). This is `lake exe`'s own compilation, not a `lake build` |
| Unfiltered fetch / `lake build` | none recorded. The 967-file count (the full cache is ~7,506) shows the fetch was the narrowed one. The only occurrences of either command in the delivery are REPORT's two statements (`environment-v23.txt`, last block) |
| Did it suffice? | **Yes.** Bootstrap 81/81 and final sweep 81/81 at status 0, with no error (`sweep-check.txt`) |

**Minor record gaps** (not findings against the fill):
- the addendum's `evidence/logs/{preflight,cache-get}.log` and `mathlib-roots.txt` ship as
  sections of `logs/bootstrap.log`, not as files;
- `/usr/bin/time` was missing, so a `wait4` wrapper recorded `maximum_rss` (peak 2,232,480 KiB
  for `Universal`).

**For a v2.4:** state that `lake exe cache` first compiles its own executable (about 17 Lake jobs,
including a few Batteries modules). That is expected and is not a `lake build`.

**The sweep** (`sweep-check.txt`, `scripts/sweepcheck.py`):
- **Final sweep:** 81 runs, exactly the order list
  `campaign/fills/s13d/orders/s13d-fill-g4-cont2.txt` in order, all status 0, 0 error lines.
- **Sorry warnings:** 35 in 15 modules. Mapped to declarations through the base tree (the head's
  for ZoneRebalance), they are **name for name the base set**
  `campaign/fills/s13d/logs/s13d-fill-g4-cont2-base-sorries.txt`. ZoneRebalance's are at 1191 and
  1232.
- **Bootstrap:** 81 distinct runs, all status 0, as two sublists, each in the list's order: the
  owned file's 22-module upstream closure first (ending with `Build/ZoneRebalance`), then the
  other 59. REPORT records this scheduling, and addendum item 5 allows it.

## (g) Landability

- **The owned file is unchanged from the base to both tips.** Its blob `e88edbda` is the same at
  the base, at `397763c8` and at `64e2dd9e` (`trees.txt`). The patch applies cleanly at both tips
  and yields the head blob `77c9119d` (`patch-at-tip.txt`).
- **Upstream changes since the base.** TCSlib changed in `Build/Primitives`, `Simulation`,
  `UniversalK`, `CodeSimulator` and `NTimeHierarchy` (`397763c8`). Then #140 changed the facade
  and added `BufferWords` (`64e2dd9e`) (`tip-changes.txt`, `tip-moved.txt`). Of the owned file's
  21 upstream modules, only `Simulation` changed (`closure-updown-tip.txt`).
- **Elaboration at the tips:**
  - `wt-tipd` against `oleans-l132b`, and `wt-tip64` against `oleans-lbw2`: exit 0, 0 errors,
    only the `:1191`/`:1232` sorry warnings (`elab-tipd-l132b.out`, `elab-tip64-lbw2.out`);
  - the seal and the axiom probe at `397763c8`: identical to the base run.
- **Replay closure** (`g5x-closure.py` over the tip's import graph): `Build/ZoneRebalance`, then
  the facade `TCSlib/Complexity/TuringMachine`, 2 modules, the same at the base and at both tips
  (`closure-tip.txt`, `closure-tip64.txt`). All 73 facade imports are in `oleans-lbw2`
  (`facade-imports.txt`). The facade could not be elaborated here: there is no olean of the
  delivered module.
- **Overlap with the open PRs** (`closure-overlap.txt`; #140 is now merged):
  - none touches `Build/ZoneRebalance`;
  - #133 (`InputDevice`), #137 (`InputWindow` + facade), #138 (`Rewind` + facade) and #139
    (`StepClock`) share only the facade, the last module of every replay;
  - #134 and #136 share nothing.
- **Sorry count after landing:** unchanged. 35 over the 81-module order; the campaign total is
  unchanged.

## (h) Recommendation and continuation 3

**Not yet clear to merge**: the landing PR `lean/g4-cont2-partial` is still to be opened,
replayed and gated. It is clear only after its replay passes and its gate is recorded.

**Land as a partial: yes.** It is the first composed machine of the zone rows. It is private,
sealed and admission-free, and it is the base that continuation 3 builds on. Holding it would gain
nothing: F1's missing endpoint is a lemma about this exact contract, and it needs no redesign.

PR body points:
- **Base and commit.** Base: the campaign branch (`complexity/arora-barak-ch3-4`, now `64e2dd9e`),
  not a stacked branch. Cherry-pick `6fe3bf884ecbc0fd30a7f017665530e8a5dfdd7b` from the verified
  bundle (`refs/review/g4-cont2`, prerequisite `96d60278`). It touches only
  `Build/ZoneRebalance.lean`, unchanged from the base to the tip.
- **A maintainer commit on top** (recommended):
  1. the extension status paragraph: the rewording in (e) (F2; it also states F1's open
     endpoint);
  2. optional cosmetics (F3): collapse the two double blank lines and label
     `zr_adjustedBack_post`'s docstring "Proof sketch.".

  The module header's "**Status: statements.** … everything else here is proved" is still
  accurate and can wait for integration.

  After the commit: re-elaborate (expect 0 errors and two sorry warnings), re-lint, and re-run
  the v3 screen on the population (docstring-only edits; expect the same pair set, or note the
  difference).
- **What it adds:** 34 private `zr_` declarations (the ruler prefix, the adjusted walk, the half
  writes, the right-pass contract with its precondition, exact time and bound) and the restated
  `zr_left_two_walks`. No public declaration and no admission. 861 → 1365 lines, 18 public /
  65 private.
- **Review table:**
  - integrity 10/10, bundle and patch;
  - owned regions only;
  - tip elaboration;
  - axiom and admission walks;
  - the seal (56 sealed, controls fail and pass);
  - import probe 439/439;
  - lint 0 FAIL / 31 WARN (Build);
  - the v3 screen (see (e));
  - environment v2.3 PASS.
- **Replay:** `Build/ZoneRebalance`, then the `TuringMachine` facade, into a copy of
  `oleans-lbw2` (the post-#140 snapshot, TCSlib = the tip's). The replay worktree needs the
  `.lake/packages` link. Whichever of #133/#137/#138/#139 merges later re-replays the facade.

**Continuation 3 should carry forward:**
1. **Checkpoint 1.1b first (F1):** prove the right pass's endpoint and its tape-0 envelope.
   - The statements are in `probes/G4C2Targets.lean`. Add the scratch envelope
     (`q − 1 … q + m + 1`).
   - Then prove the bridge to the specification: after the pass, tape 0 agrees with
     `zonedTape (extend)` at every cell `≥ 0`, and with `zonedTape z` at every cell `≤ 0`
     (`zr_extend_cell`, `zonedTape_extend`).
   - Re-wrap the pass by `Contract.ofSegment` to a singleton exit before sequencing it.
2. **1.2, the return home**, by the worker's inspected design:
   - `skipTM` over the outer half to `zoneStart (ℓ+1)`;
   - then `Round.iterate` over `skipBackTM` rounds built by `round_iff`, each with a one-cell
     test for home (the unique one-cell field: its second cell is blank), and an anchor distinct
     from `skipBackTM`'s run state.
3. **1.3, the left pass** (amended):
   - the displacement is `zr_left_two_walks` (unadjusted full-ruler walk, then adjusted walk);
   - the second seek's precondition is local agreement on `[−zoneStart ℓ, 0]` carried through the
     right pass's frame (now available from item 1), not `zoneRowPre`;
   - **parametrize `zr_rulerStepContract`/`zr_adjustedWalkContract`/`zr_adjustedBackContract` by
     direction** (and read the ruler from its right end) rather than writing a leftward copy.
4. **1.4–1.6:**
   - the `ℓ = 0` branch by the leaf;
   - `clearTM_contract` on the ruler `[q, q+m)`, with the head restored;
   - assembly by `Contract.ofSegment` in the `HeadBox` of `zoneRowLo`/`zoneRowHi`, with
     `zoneExtendPost_frames`.
5. **Phase 2 unchanged:** the two-exit scan by `round_iff`/`Round.iterate` with the unary count;
   one level's guarded column move; the passes with the home move; `dir = false` via
   `zr_mirror_tape`.
6. **Promotion candidates:** as in (d), with the direction-parametrized adjusted walk first.
7. **Inputs at the landing commit:**
   - the probe (add the 39 constants of Expansion A, `extlist-new-not-in-probe.txt`);
   - the population (unchanged);
   - the order list (81, unchanged unless the facade's imports change);
   - the base sorry set (35);
   - the screen base: the landing's re-screen.
8. **Environment:** addendum v2.3 as is (it passed on first use), optionally with the v2.4 note
   in (f).
9. **Budget:** this round reached one checkpoint. Ask continuation 3 for 1.1b, 1.2 and 1.3 as
   checkpoints, each landing alone.

**Decisions for the user:**
- (1) Land this partial now as `lean/g4-cont2-partial` (recommended), or hold it for a fuller
  delivery.
- (2) Record checkpoint 1.1 as "composed; endpoint and envelope open (1.1b)" (recommended),
  rather than "complete" as the report has it.
- (3) Whether to add the one-line v2.4 note on `lake exe cache`'s self-compilation to the
  addendum.
