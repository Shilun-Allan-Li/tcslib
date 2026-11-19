# Gate 170, round 2 · RAM simulation, tier 2 job D: the phase interfaces (PR #386)

**Round 2 of the Codex audit.** Round 1 (`findings.md`) was **HOLD**: 0 blockers, 2 majors,
2 minors. It found the proofs sound (G170-05, -06) and the evidence consistent (G170-07), and held
on two duplications. Seyoon ruled (2026-11-18) that Codex repair both rather than record them as
debt. This round answers all four findings. PR #386 is a draft into `complexity/ram-simulation`.
Seyoon dispatches and merges.

- **Lean head:** `113975d68167062693583a9bbbf63a982b80b817` (branch `ram/fill-phases`). Since
  round 1's head `09546b89`:
  1. `59c7b4be`, a merge of the RAM branch: #385 (`WordArith`), #382 (`exists_tmProc`), #388
     (`InputBit`, `Startup`) and #389 (`KeyTable`). It keeps the branch's copy of the identical
     reader `Turing.Cfg.select_eq` (from #388), so this PR no longer adds it;
  2. `113975d6`, the Codex repair round `fill-ram-phases-r3`, landed unchanged (zip SHA-256
     `d98185b3…`). The patch reproduces all 27 delivered files byte for byte. `Sim/Phases.lean`
     is byte-identical to round 1.
- **#391 merged after this run** (`b9b521fd`). It changes only `Build/Convention`,
  `StateRenaming` and `CodeSimulator`; this PR touches none of them and still merges cleanly. The
  replay below is of this PR merged into the branch before #391.
- **Rulings that bind:** as in round 1 (D1, D2, the reader rule), and Seyoon's repair ruling.

## Resolutions

| # | Severity | Resolution |
|---|---|---|
| G170-01 | major | **Cited.** `phase_reaches_zero` (`Sim/PhaseControl`) takes its segment from `Turing.Segment.zero`, reads it with `Turing.segment_iff` and returns through `Turing.reachesWithin_iff`. `phase_reaches_trans` (`Sim/PhaseHost`) reads both witnesses with `reachesWithin_iff`, widens both head predicates to the summed radius about the first start, builds the two segments with `segment_iff`, cites `Turing.Segment.trans`, and reads the result back. No `runFrom_add` or prefix split remains. Both wrappers stay because their callers use the `ReachesWithin` form; their only own work is the radius and time-bound transport. |
| G170-02 | major | **Unified.** One structure, `PhaseCertificate E P Q selected` (`Sim/PhaseBlock`): a finite machine, an injective exit map `E ↪ State` with `[Fintype E] [DecidableEq E]`, a common constant, and a restored-head run to the selected exit. `PhaseBlock` and `PhaseBranch` are now its `Unit` and `Bool` cases (abbreviations with equality readers `PhaseBlock_eq`, `PhaseBranch_eq`). There is **one** composition proof, `PhaseCertificate.seq` (a one-exit prefix followed by any certificate), and **one** fresh-entry packaging proof, `phase_machine_ofCertificate` (`Sim/PhaseControl`). `phase_machine_ofBlock` and `phase_machine_ofBranch` keep their statements and are now citations of it. Both former duplicate pairs (661/747 and 806/1035) are gone from the screen. New public names, all in `WordRAM.Sim` under D1: `PhaseCertificate`, `PhaseBlock_eq`, `PhaseBranch_eq`, `PhaseCertificate.weaken`, `PhaseCertificate.seq`, `phase_machine_ofCertificate`. |
| G170-03 | minor | **Described and checked.** The kit's metadata check is an **axiom allowance**. The check of named dependencies is the kit's new **admission walk** (`checks/admission-walk.py`), run on the final replay's snapshot. It walks every constant reachable from each root through types and values, theorem proofs included, and fails unless each root's admission sites lie in the allowlist. This round the allowlist is **empty**, and both `exists_phase` and `exists_verdictPhase` reach **no** admission (`ADMISSION-WALK.json`): the twelve row statements round 2 cited are all proved on the branch. The fill's own walk is in the evidence too: `fill/FinalAxioms.lean.txt`, `fill/final-axioms.log`, `fill/final-admissions.json` (all 361 roots, empty) and `fill/final-target-admissions.json`. Its complete per-target graphs, 8 MB together, are in the fill's archive `inbox/fill-ram-phases/fill-ram-phases-r3.zip` on the exchange. |
| G170-04 | minor | **Homes bundled, screen extended.** All citation homes are in the bundle. They also join the copy screen's population (`population_extra`), with the four files the repair brief named (`Build/Contract/Basic`, `Build/Contract/Seam`, `Build/Seam`, `Build/NDHost`). |
| G170-05 – -07 | note | No change needed. |

## The copy screen

The population is the 29 changed files plus 19 cited homes. 106 new pairs, 0 gone (260 → 366),
all classified (`PAIR-DISPOSITIONS.json`, `pair-notes.json`). 81 carry round 1's dispositions. The
25 new ones are pairs with the cited homes, and the fill's merged certificate against `PhaseRow`.
They are shape matches through the same field and step readers, with one **parallel to note**:

- `PhaseFrame` (public, 8 tapes, `Sim/PhaseCore`) and `InputBitData` (private, 5 tapes,
  `Build/InputBit`, merged with #388) are the same notion. Each is a configuration without its
  control state: the input head, work tapes, heads and output.
- They are two four-field records, not copied proofs.
- A tape-count-generic frame in the Turing-machine library could serve both. It is listed as a
  follow-up candidate; its home needs Seyoon's ruling.

The fill's own screen (over the phase files and the four named files) is in `REPORT-phases-r3.md`:
151 → 140 pairs, with its cumulative per-file ledger.

## Brief for the auditor

1. **G170-01:** the two wrappers' proofs are the citations, with only radius and time transport.
2. **G170-02:** `PhaseCertificate` with its `Unit` and `Bool` cases is faithful to the two old
   interfaces (exit cuts, selected exits, constants). `phase_machine_ofCertificate`'s
   `Option E` routing gives the old one-exit and two-exit machines. No composition or packaging
   proof is duplicated.
3. **G170-03:** `ADMISSION-WALK.json` and the fill's walk agree: both targets reach no admission.
4. **G170-04:** the homes are present at the audited head, and the 25 new dispositions hold.
5. **Statements:** `exists_phase`, `exists_verdictPhase` and every statement outside the owned
   files are unchanged (`SOURCE.json`; `Sim/Phases.lean` byte-identical).

## Evidence (`evidence/`)

- **`REPLAY.json`:** the merged-tree replay on `oleans-cl175-cl169`, the RAM branch's build after
  #382, #388 and #389. 172 modules: 172 passed, 0 failed.
- **Seals:** 155 proofs and 67 heads, all passing.
- **Controls:** 71 definitions and 142 identities in two parts, native-PASS and sealed-FAIL.
- **Sweeps:** the proof-syntax sweep finds 0 read candidates in 155 roots. Citation homes are in
  `CITATION-HOMES.json`.
- **Admission walk:** `ADMISSION-WALK.json`, with its Lean file and log in the data carrier.
- **The fill's report** (`REPORT-phases-r3.md`) and walk files (`fill/`). Round 1's pack is
  `pack.md`.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate170-ram-phases-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
