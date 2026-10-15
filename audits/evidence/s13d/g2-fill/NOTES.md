# §13d G2 fill (maintainer): notes

The G2 fill proves the three declarations that the G2–G4 landing (PR #106) left sorried:
- `Turing.copyMapTM_run_ofCfg` and `Turing.transferMapTM_run_ofCfg` (`Build/Catalog.lean`);
- the pure `Turing.zoneCascadeRight_home` (`Build/Zone.lean`).

The user chose on 2026-10-15 that the maintainer finishes the fill and opens a PR ("Maintainer
finishes, then PR"). The PR is #108, branch `lean/g2-fill`, head `8e3cee48`. Next comes the G2
fill gate.

## 0. Base, snapshot, tools

- **Base:** the campaign tip `02553301`. `Build/Catalog.lean` and `Build/Zone.lean` are unchanged
  from there to the PR's parent `83a463ee` (after #107).
- **Snapshot:** `oleans-lcanon4`, the replay output of #107, which is Lean-equal to `83a463ee`.
- **Lean:** only through the throttled `scripts/leanelab.sh` (no `-o`, no olean written).
- **Python:** only as `python3 -I`.
- **The generators:** both files are written by asserted generators from the base files:
  - `scripts/mkoverlay.py`, with `scripts/mapped-block.lean.txt`, for Catalog;
  - `scripts/mkzone.py` for Zone.
  Every edit matches its anchor exactly once. Re-running both on the files at `83a463ee`
  reproduces the PR head byte for byte.
- **The screen:** `audits/evidence/retrofit/copy-text-screen-v3.py`, SHA-256
  `f4feac91d3a1ec036f3bbcaafde83e6855a1bf1a62d31dac31a40a40d878f181`, the tip's copy.

## 1. The design

**Catalog: one trace family** (gate ruling 7).
- The plain sweep families and their three traces are replaced by:
  - value-parametric families: `catalogSweepF`, generic in the written value `v`; `catalogSweepR`;
    and `catalogSweepResidueR`, which adds the residue `u`;
  - one trace lemma, `catalog_transferMap_trace`.
  - The plain families (`catalogCopyF`, `catalogCopyR`, `catalogTransferR`) and traces
    (`catalog_copy_forward`, `catalog_copy_trace`, `catalog_transfer_trace`) are the six
    privates retired.
- `catalog_trace_clauses` derives the trajectory clauses of every framed row from a trace. It is
  generic in the set of touched tapes.
- The copy is the transfer with the identity residue `some`: its return pass writes back what it
  reads (`copyMapTM_step_eq`, `copyMapTM_runFrom_eq`).
- `transferTM_run_ofCfg` and `copyTM_run_ofCfg` are the mapped framed rows at the identity map.
  `transferTM_spaceUsedByTape` and `copyTM_spaceUsedByTape` go through the mapped trace at the
  identity map.
- The mapped framed block moves to just before `transferTM_run_ofCfg` so that the plain rows can
  cite it. It moves verbatim.

**Zone: one induction.**
- `zoneStepPair_pre` is the classical pre-state descending one level through the outer step pair.
  It is the block that `zoneSide_cascadeRight`'s successor case proved inline at the base.
- `zoneCascadeRight_classical` is one induction on the index giving both the two word equalities
  and the new home.
- `zoneSide_cascadeRight` and `zoneCascadeRight_home` are its two projections.

**Docstrings.**
- Zone's module status now reads "proved".
- The G2 section header and five proof sketches (three in Catalog, two in Zone) name what the
  formal proofs instantiate or share.

## 2. Checks

| Check | Result | Log |
|---|---|---|
| Elaboration, Catalog | 0 errors, 0 sorry warnings. 78 warnings against the base's 92: 0 new, 14 removed, keyed by message and source line. | `logs/elab-catalog-*.out`, `logs/warnings-catalog.log` |
| Elaboration, Zone | 0 errors, 0 warnings. The base's one warning was the sorry. | `logs/elab-zone-*.out`, `logs/warnings-zone.log` |
| Freeze, Catalog | Publics 95/95: none added, removed or restated. The body changes are the six authorized: the two mapped framed rows, the two plain framed rows and the two plain space lemmas. Privates: −6, +7. No other private changed. | `logs/freeze-catalog.log` |
| Freeze, Zone | Publics 65/65: none added, removed or restated. The body changes are the two authorized: `zoneCascadeRight_home` and `zoneSide_cascadeRight`. Privates +2. | `logs/freeze-zone.log` |
| Axioms | Every public of both files uses standard axioms only, and none uses `sorryAx`. Catalog: 51 use `[propext, Classical.choice, Quot.sound]`, 6 `[propext, Quot.sound]`, 8 `[propext]`, 30 none. Zone: 27 / 19 / 17 / 2. The probe is the final file with `#print axioms` appended (`scripts/mkaxprobe.py`), so the logs are also the elaboration logs. | `logs/elab-*-final-with-axioms.out` |
| Copy-text screen v3 | Population: the G2–G4 gate's five files and `Simulation` (`logs/screen-population.txt`). Base: 548 declarations, 384 pairs, 124,738 characters. Final: 552 declarations, 370 pairs, 116,705 characters. 4 pairs are new by name, all in-file; 18 are gone. | `logs/screen-*.txt`, `logs/screen-delta.log`, `logs/pairs.log` |
| Lint | `scripts/campaign_style_lint.py` and `scripts/style_lint.py` on `Build/`, base and head: 0 FAIL on both. The WARN sets are equal apart from the two files' line counts in the existing size warnings. | `logs/lint-*.txt` |
| Hygiene | 462 added lines, 0 hits for `#eval`, `run_cmd`, `IO`, `unsafe`, `implemented_by`, `extern`, `native_decide`, `syntax`/`macro`/`elab`, `sorry`, `admit`, `axiom`. | `logs/hygiene.log` |
| Widths | No new line over 100 characters. | |
| Pre-ship probes | `probes/G2ImportProbe.lean.txt`: 52 `#check`s, 0 errors. `probes/zone-seams.lean.txt`: the three seams proved. | `probes/*.out` |

## 3. Duplication: four pairs for the user's approval

Each pair is below the 90% factoring line. Three are successors of base pairs. `logs/pairs.log`
lists the reproduced segments.

| New pair | Overlap | What it is |
|---|---|---|
| `catalog_transferMap_trace` ← `catalog_clear_trace` | 67%, 1,086 chars | The successor of the base's `catalog_transfer_trace` ← `catalog_clear_trace` (54%, 866 chars). The shared sweep-trace tactic idiom (`split_ifs <;> simp_all <;> omega`, `apply Cfg.ext <;> simp [...]`, the `change ((M).tr _ _ _).apply _ = _` steps). It grew because one trace now carries both rows. |
| `catalog_transferMap_trace` ← `catalog_write_take` | 50%, 62 chars | New: two 31-character idiom fragments. |
| `zoneCascadeRight_classical` ← `zoneCascadeRight_zero` | 60%, 87 chars | The successor of the base's `zoneSide_cascadeRight` ← `zoneCascadeRight_zero` (80%, 117 chars): the zero case's unfolding `simp only` list. |
| `zoneCascadeRight_lengths` ← `zoneStepPair_pre` | 60%, 608 chars | The successor of the base's `zoneCascadeRight_lengths` ← `zoneSide_cascadeRight` (53%, 761 chars): the frame half of the pre-state block, which moved into the new lemma. `zoneCascadeRight_lengths` cannot cite it, because its hypotheses and conclusion are exact lengths. |

The 18 gone pairs include:
- the base's 91% `catalog_transfer_trace` ← `catalog_copy_trace`;
- the 61–78% pairs among the clear, copy and transfer framed rows and their space lemmas;
- the three pairs above that have successors.

In-file reproduced text falls from 105,808 to 98,390 characters in Catalog, and from 3,840 to
3,225 in Zone.

## 4. Process record

- **The first screen of the proved files** (Zone with two separate inductions) showed 6 new pairs.
  - `zoneCascadeRight_home` and `zoneSide_cascadeRight` reproduced each other at 52–54% (297
    characters: the induction skeleton).
  - Both became projections of `zoneCascadeRight_classical`. This removed both pairs, and the zero
    case's pair now has the shared lemma as its source.
- **The earlier screen of the overlay with the traces stubbed** showed 0 new pairs, but it could not
  see the proved bodies. The screen above is of the final files.
- **The first elaboration of the final Catalog** gave 7 "simp argument is unused" warnings in new
  code:
  - `Ne.symm hne`, `hne` and `List.getElem?_eq_getElem hr` in the trace lemma;
  - `catalogCfg` in the space lemmas.
  They were removed in the generators, and the re-elaboration has 0 new warnings.

## 5. Replay

87 modules: `Build/Catalog`, `Build/Zone` and their downstream closure. This is the same set as
#106's replay (`replay-order.txt`, from `graph2.py`, root excluded). It replays from
`oleans-lcanon4` into `oleans-lg2`.

Expected result:
- `Build/Catalog`: 2 sorry warnings to 0;
- `Build/Zone`: 1 to 0;
- the other 85 modules: as in the replays of #106 and #107.
