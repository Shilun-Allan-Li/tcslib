# §13d G2–G4 landing: notes

The gate closed on 2026-10-14 (PASS 0/0/5; `audits/s13d-g24-statements-findings.md`, resolutions
`…-resolutions.md`). It was built at `f2d48ad5`, before MIG-1 stage S. Its first obligation is that
the landing rebuild the landed files at the actual tip and re-run the gate's checks there. This
folder records that rebuild, at the campaign tip `6672531c` (after #105, the merge to main).

## 0. Base, snapshot, tools

- **Base:** a `git archive` export of `6672531c`. Its 742 `TCSlib` blobs were checked equal to the
  commit's tree with `git hash-object` against `git ls-tree`. The tip had not moved when the PR was
  opened.
- **Snapshot:** `oleans-lmain`, the root replay of #104 at `ff2d6f6b`, Lean-equal to the tip.
- **Lean:** only through the throttled `tools/leanelab.sh` (no `-o`, no olean written).
- **Python:** only as `python3 -I`.
- **The screen:** `audits/evidence/retrofit/copy-text-screen-v3.py`, SHA-256
  `f4feac91d3a1ec036f3bbcaafde83e6855a1bf1a62d31dac31a40a40d878f181`, equal to the tip's copy.

## 1. What changed since the gate's base, and what that does to the landing

| File | Since `f2d48ad5` | Effect on the landing |
|---|---|---|
| `Build/Zone.lean` | unchanged | none |
| `Build/Contract/Catalog.lean` | unchanged | none |
| `Build/Catalog.lean` | MIG-1 S: two endpoint theorems added (`Cfg.ofWords_copy_endpoint`, `…_transfer_endpoint`); the rewind head bounds moved to `Simulation` | every asserted edit still applies; the endpoint theorems unfold no table (obligation 4) and keep their axioms |
| `TuringMachine.lean` (facade) | #94, #98, #102 entries | `mkfacade.py`'s two anchors still match |

All the gate's writers (`mklanded.py`, `mklanded_zone.py`, `mklanded_catalog.py`, `mkfacade.py`)
ran unchanged at the tip. Every one of their edits is asserted, and a second run regenerates the
landed files byte for byte.

## 2. The gate's minors

| # | Disposition at landing |
|---|---|
| 1 | Carried to G5's statement phase. The design note's §5(e) is annotated (`../G24-design.md`). |
| 2 | Carried to G5's statement phase. The fit probe is evidence and does not land. |
| 3 | Fixed, in prose only. `copyMapTM`/`transferMapTM` are qualified by `src ≠ dst`, and `sweepPost` says "all work heads" (`parts/M1.body.landing.diff`, `parts/C1.body.landing.diff`). |
| 4 | Fixed: the two labels now read `**Proof sketch.**`, with the fill-plan text kept after them (`parts/R.body.landing.diff`). |

The three edited part files are identical to the gate's once comments are removed.

## 3. Checks (`logs/verify.log`: 7 checks and 8 checker controls, 0 failures)

`scripts/logs.sh` is the gate's `runall.sh`, re-pointed by `scripts/derive_logs.py` with asserted
replacements. `scripts/verify.py` asserts each result against the gate's expectations:

1. **Cut checks and landed forms.**
   - The 7 unit cuts, the landed `Zone`, the zone chain, the landed `Catalog` and the Catalog chain
     elaborate with 0 errors.
   - Sorries sit exactly at the fill targets: `zoneCascadeRight_home`, `copyMapTM_run_ofCfg`,
     `transferMapTM_run_ofCfg`, `exists_zoneRebalanceTM` and `exists_zoneExtendTM`.
   - The landed `Catalog`'s warnings are the base's plus those 2 sorries.
2. **Freeze.**
   - `Build/Catalog`: 480 old declarations, 0 statements changed, the 5 listed bodies changed,
     6 added.
   - `Build/Contract/Catalog`: the 3 listed bodies changed, 10 added.
   - No downstream proof names `copyTM`, `transferTM` or `clearTM_contract` inside `simp`,
     `unfold`, `rw` or `delta` (obligation 4).
3. **Axioms.**
   - No printed axiom lies outside `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`.
   - Every public `Catalog` declaration has the same axioms before and after, MIG-1 S's included,
     and none gains `sorryAx`.
   - The new prints, and the unit's, the fit probe's and the zone chain's prints, all equal the
     gate's.
   - The promoted `zoneCascadeRight_frame` is proved.
4. **Names.**
   - The only full-name clash is the promotion.
   - 8 statement units were screened, including the pending B5a canonizer continuation 4 overlay.
   - The positive control caught 2 of 2.
5. **Retirements:** the 16 retired names have no Lean consumer at the tip.
6. **Unit, probes, controls, lint, widths, citations.**
   - The unit (6 sorried, as gated), the sanity probe and the fit probe elaborate.
   - The gate's 4 Lean negative controls each fail.
   - Lint is the gate's: one pre-existing facade-rule FAIL, and the size findings.
   - No line of new material exceeds 100 characters.
   - The unresolved cited tokens are the gate's (prose tokens, and one note in the unit that does
     not land).
   - The promoted statement is identical to the private lemma's.
7. **Copy-text screen (v3), on the gate's population.**
   - Before: 312 pairs; after: 329.
   - The new 24 and removed 7 are exactly the gate's accepted pairs, by declaration, and none is
     cross-file.
   - v3 labels the two `Catalog.lean` files by full path; the comparison uses basenames, as the
     gate's v2 screen did.
   - The base's 10 extra pairs against the gate's 302 come from the base itself: 12 pairs involve
     MIG-1 S's endpoint theorems, and 2 rewind pairs left with the move to `Simulation`. They
     are present before and after.

Checker controls: each of the 8 feeds one check a broken input and requires it to fail:
- an extra sorried declaration;
- a changed statement;
- a downstream unfold;
- a foreign axiom;
- a second name clash;
- a consumer of a retired name;
- a missing sorry;
- an extra screen pair.

## 4. The PR and the replay

- **The PR:** #106 (`lean/g24-landing`, head `dc7d8a23`), six files: `Build/Catalog`,
  `Build/Contract/Catalog`, `Build/Zone`, the new `Build/ZoneTape` and `Build/ZoneRebalance`, and
  the facade.
- **The replay:** 87 modules, the downstream closure of the six (`replay-order.txt`,
  `logs/graph.log`), from `oleans-lmain` into `oleans-lg24`, root excluded.

## 5. Not checked here

- The downstream modules' elaboration against the landed `Catalog` and `Zone`. The replay does that.
- The facade's own elaboration. It imports the two new modules, which have no oleans before the
  replay.
- [AB09] §1.7 was not re-read; the gate checked fidelity.
