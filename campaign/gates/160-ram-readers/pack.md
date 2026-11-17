# Gate 160 · RAM readers for the class corollaries (PR #370)

**Not yet clear to merge.** PR #370 is a draft, into `complexity/ram-simulation`. Seyoon dispatches
and merges.

- **Lean head:** `e75d290706e1b05e1e43cd07cfcea94484207b25` (branch `ram/readers`). It is one
  commit on the RAM branch at `e1236e6f`, whose Lean is `main` `5cb25d52`.
- **Records:** the branch tip named in the dispatch prompt. Its later commits change records
  only.
- This is the first audit on the RAM work branch.

## Scope

The tier 3 fill proves the nine class corollaries of `RAMSimulation/Classes`. Under rule 10 it
needs readers for definitions in other files. Seyoon approved eight new public readers
(2026-11-17), each `Iff.rfl` or `rfl`, each in its definition's home file:

| File | Reader | Statement |
|---|---|---|
| `ClassP/DTIME` | `Complexity.mem_DTIME_iff` | `L ∈ DTIME T ↔ ∃ c M, M.DecidesInTime L (c * T ·)` |
| `SpaceComplexity/NSPACE` | `Turing.FinNDTM.decidesInSpace_iff` | the three clauses of `DecidesInSpace` |
| `SpaceComplexity/NSPACE` | `Complexity.mem_NSPACE_iff` | `L ∈ NSPACE s ↔ ∃ c N, N.DecidesInSpace L (c * s ·)` |
| `SpaceComplexity/SpaceClasses` | `Complexity.NL_eq` | `NL = NSPACE logSpace` |
| `RAMSimulation/Simulation` | `WordRAM.simTime_eq`, `WordRAM.simSpace_eq` | the two bounds' formulas |
| `RAMSimulation/Simulation` | `WordRAM.outputOf_false`, `WordRAM.outputOf_true` | `[v]` in verdict mode, `o` in function mode |

- No existing declaration changes, and no attribute is added.
- Each file's module docstring lists its new readers.
- `SOURCE.json`: 4 owners, 8 added declarations, none removed, no header or definition change.
  Net +45 lines.

## Brief for the auditor

1. **Each reader's statement against its definition.** Each must be exactly the definition,
   with no weakening or reshaping: the `∃` binders, the `c * …` constant absorption, the `+ 1`
   terms and the `if` in `outputOf`.
2. **Fitness for tier 3.** The tier 3 brief (`campaign/items/ram-tm/briefs/fill-ram-classes.md`,
   bundled) cites these readers. Check that, with the readers already published, they suffice to
   prove the nine corollaries without unfolding any other file's definition.
3. **Rule 10 and standards:** the seal, control and sweep evidence below; the docstrings; and
   no campaign labels in the new text.

## Evidence (`evidence/`)

- **`REPLAY.json`:** the merged-tree replay of the 4 owners' downstream closure on
  `oleans-cc91f4`.
  - 265 modules replayed: 265 passed, 0 failed.
  - 24 inherited admissions, all pre-existing: the 14 RAM admissions (WordSize 3, Simulation
    2, Classes 9) and 10 in `main`'s BooleanAnalysis (UniqueGames 8, MaxCutAlgorithm 2).
  - 898 objects in and 898 out.
  - Pool 3 of 4 cores; peak memory 3.8 GB of 16.9 GB; no back-off.
- **Seals:** all 8 proofs pass with every other-file definition they reach made irreducible
  (DTIME 1, NSPACE 2, SpaceClasses 1, Simulation 4).
- **Controls:** one part, 20 sealed definitions and 40 paired identities, each native-PASS and
  sealed-FAIL.
- **Sweeps:**
  - proof-syntax sweep: 8 roots, 0 read candidates;
  - Lean-backed sweep (`DEFSWEEP-SUMMARY.json`): no flag;
  - citation homes (`CITATION-HOMES.json`): `SpaceComplexity/Basic`, `TuringMachine/Finite`,
    `TuringMachine/Nondeterministic`.
- **Copy screen** (population: the 4 files): 0 → 0 pairs.
- **`DATA-CARRIER.json`** and its recovery map: every log and input of the run, and the gate kit
  (`devtools/seyoon/gatekit/`) that produced them.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate160-ram-readers-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
