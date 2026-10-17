# MIG-24's library-wide copy-text screen (maintainer, night of 2026-10-17; measurement only)

The user's ruling (2026-10-17): run the library-wide screen overnight as MIG-24's input (the
mirror-pair factoring). No Lean is edited.
- **Tree:** #118's round-2 head `4624fc05`.
- **Screen:** v3 (`audits/evidence/retrofit/copy-text-screen-v3.py`), run one at a time under
  `nice -n 10` (`overnight.sh`).

| Population | Files | Declarations screened | Pairs (≥ 50%) | Pairs at ≥ 90% (directed / unordered) |
|---|---|---|---|---|
| `TuringMachine/` (`pop-tm.txt`) | 79 | 2,931 | 3,116 | 648 / 394 |
| `SpaceComplexity/` (`pop-sc.txt`) | 107 | 1,346 | 588 | 166 / 123 |

**The unordered pairs at 90% or more, by owner** (`summary.txt`):

| Population | MIG-1 (`f2_` copies) | MIG-2 (timed universal layer) | Small (< 200 shared characters) | MIG-24 candidates |
|---|---|---|---|---|
| `TuringMachine/` | 185 | 38 | 113 | 58 |
| `SpaceComplexity/` | 0 | 0 | 89 | 34 |

- `mig24-*-candidates.tsv` lists the candidates, ranked by shared characters, in-file and
  cross-file.
- The largest are in-file families:
  - in `TuringMachine/`: `Catalog`, `Primitives`, `Loop` (`emCall_bank_initial`/`_final`) and
    `Composition`;
  - in `SpaceComplexity/`: `ARMSim`, `ExpBFS/Run` and `SavitchARM/Recursion`.
- The pairs are text overlap, not proof of duplication. Each candidate needs reading before
  MIG-24 schedules a factoring, and files owned by others (Hydroxyi's) go to the user's 12.2c
  window, not into MIG-24.
- **Not counted:** cross-directory pairs between `TuringMachine/` and `SpaceComplexity/`, because
  each population was screened separately.
