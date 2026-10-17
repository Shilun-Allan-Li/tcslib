# Brief drafts (maintainer, 2026-10-16; not issued)

Five fill briefs, measured at #118's head `4ae686be`, whose Lean is the tip's once #118 merges.
Each issues after #118 merges, with only its base hash (⟨BASE-LEAN⟩) and, for two of them, the
screen base (⟨BASE-COUNTS⟩) left to fill.

| Draft | Target | Order | Base sorries | Probe | Screen base |
|---|---|---|---|---|---|
| `u2s-fill-startup` | `exists_selfStartupTMK` (`UniversalK`) | 92 | 35 in 15 modules | 100 names | 654 declarations, 514 pairs |
| `b6-fill-rulerdevice` | F5's three rows (`Build/InputDevice`) | 80 | 35 in 15 modules | 52 names | 272 declarations, 138 pairs |
| `b6-fill-configclock-cont1` | `exists_configWindowRunnerTM` (`WindowClock`) | 176 | 28 in 11 modules | 60 names | 1,042 declarations, 510 pairs |
| `b5a-fill-canon-cont6` | `exists_canonGrammarStage` (`CodeSimulator`) | 102 | 41 in 16 modules | 156 names | 2,410 declarations, 2,631 pairs |
| `s13d-fill-g4-cont1` | G4's two rows (`Build/ZoneRebalance`) | 80 | 35 in 15 modules | 338 names | 794 declarations, 437 pairs |

- **Pre-ship, all against `oleans-lbapi2`:**
  - U2-S's and F5's import overlays, F3's overlay, and G4's bridge overlay each elaborate with
    exactly their expected sorry warnings;
  - F3's consumer probe, and cont6's inherited probes and note-50 walk, elaborate with 0 errors;
  - the five import probes elaborate with 0 errors.
- **The inventory** for all five is #118's (`audits/evidence/brief-api/`). G4's was re-run over
  its 338 probe names at the head: every definition in their statements has a published lemma,
  is a model primitive, or is the worker's own.
- **G4's helpers to re-point** (rule 10): `audits/evidence/drafts/s13d-g4-cont1/repoint.md`.
- The staged inputs (overlays, probes, populations, order lists, sorry sets) are in
  `audits/evidence/drafts/issue-inputs/`; each brief's inputs commit copies them to their brief
  paths at issue.
