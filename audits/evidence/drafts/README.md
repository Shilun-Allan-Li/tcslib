# Brief drafts (maintainer, 2026-10-16/17; not issued)

Six fill briefs, measured at #118's round-3 head `531b98a2`, whose Lean is the tip's once #118
merges. Each issues after #118 merges with only its base hash (⟨BASE-LEAN⟩) left to fill. The
issue tool is `issue-tools/issue.py.txt` (`plan`, `apply`, `dispatch`).

| Draft | Target | Order | Base sorries | Probe | Screen base |
|---|---|---|---|---|---|
| `u2s-fill-startup` | `exists_selfStartupTMK` (`UniversalK`) | 92 | 35 in 15 modules | 100 names | 655 declarations, 514 pairs |
| `b6-fill-rulerdevice` | F5's three rows (`Build/InputDevice`) | 80 | 35 in 15 modules | 58 names | 272 declarations, 138 pairs |
| `b6-fill-configclock-cont1` | `exists_configWindowRunnerTM` (`WindowClock`) | 176 | 28 in 11 modules | 60 names | 1,043 declarations, 510 pairs |
| `b5a-fill-canon-cont6` | `exists_canonGrammarStage` (`CodeSimulator`) | 102 | 41 in 16 modules | 156 names | 2,411 declarations, 2,631 pairs |
| `s13d-fill-g4-cont1` | G4's two rows (`Build/ZoneRebalance`) | 80 | 35 in 15 modules | 338 names | 795 declarations, 437 pairs |
| `mig12-fill-cfgrecord` | MIG-12, the swap of `Build/CfgRecord` onto the contract layer | 279 | 83 in 21 modules | 227 names | 870 declarations, 437 pairs |

- **Pre-ship, all against `oleans-lbapi4`** (#118's round-3 replay; re-run 2026-10-17, 19
  elaborations):
  - U2-S's and F5's import overlays, F3's overlay, and G4's bridge overlay each elaborate with
    exactly their expected sorry warnings; MIG-12's overlay has 0 errors and 0 warnings;
  - F3's consumer probe, and cont6's inherited probes and note-50 walk, elaborate with 0 errors;
  - the six import probes elaborate with 0 errors.

  Every output's messages equal the run against `oleans-lbapi3` (#118's round 2) line for line.
- **History.** The first measurements were against `oleans-lbapi2` (#118's round 1). Before
  round 3, F5's probe had 52 names and MIG-12's 219; round 3 added 6 and 8. The screen bases
  above are at the round-3 head: F5's is unchanged, and each of the other five gained one
  declaration with the same pairs.
- **The inventory** for the first five is #118's (`audits/evidence/brief-api/`). G4's was re-run
  over its 338 probe names at the head: every definition in their statements has a published
  lemma, is a model primitive, or is the worker's own. MIG-12's is its own
  (`mig12-fill/`): 68 external definitions crossed with the 173-row unfolding ledger
  (`mig12-fill/unfold-sites.tsv`, the corrected copy of
  `brief-api/r3/unfold-sites-r3.tsv`), every row with a published lemma to re-point to.
- **G4's helpers to re-point** (rule 10): `audits/evidence/drafts/s13d-g4-cont1/repoint.md`.
- The staged inputs (overlays, probes, populations, order lists, sorry sets) are in
  `audits/evidence/drafts/issue-inputs/` and `mig12-fill/`; each brief's inputs commit copies them
  to their brief paths at issue.

## C1 wave 1 (drafted 2026-10-17; not issued)

Five fill briefs, measured at #120's head `6d18902f`, the tip once #119 and #120 merge. They issue
after both merge, by `issue-tools/issue2.py.txt`, once the pre-ship elaborations
(`issue-tools/preship-wave1.sh`) have run against `oleans-lndnf`.

| Draft | Target | Imports added | Order | Base sorries | Probe | Screen base |
|---|---|---|---|---|---|---|
| `c1-fill-writer` | W, `ndWriterTM_run_block` (`Build/NDHost`) | none | 80 | 35 in 15 modules | 20 names | 780 declarations, 1,018 pairs |
| `c1-fill-window` | WC, `exists_inputWindowCopyTM` (`Build/InputWindow`) | none | 80 | 35 in 15 modules | 49 names | 125 declarations, 43 pairs |
| `c1-fill-exhaustive` | E, `FinNDTM.exists_exhaustiveDecider` (`ClassNP/ExhaustiveReplay`) | 3 | 77 | 19 in 9 modules | 61 names | 278 declarations, 106 pairs |
| `c1-fill-core` | R, `exists_ndInterpreterCore` (`NDCodeSimulator`) | 2 | 80 | 35 in 15 modules | 77 names | 171 declarations, 19 pairs |
| `c1-fill-universal` | UN with BF, H′ and S (`Diagonalization/NTimeHierarchy`) | 5 | 72 | 29 in 13 modules | 53 names | 67 declarations, 14 pairs |

The route inventories behind them are in `audits/evidence/nd-api/` (#119's three commits).

**Pre-ship, against `oleans-lndnf`** (`issue-tools/preship-wave1.log`; 2026-10-17): the three overlays
and W's and WC's own files elaborate with exactly their expected sorry warnings; the five import
probes have 0 errors. E's, R's and UN's probes list only names from other files: the owned file's
own declarations are not in the overlay's import context. `issue2.py plan` passes.
