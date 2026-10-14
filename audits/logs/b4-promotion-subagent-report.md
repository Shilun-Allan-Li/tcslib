# P4 report: B4 pre-issue promotion

Branch `maint/b4-promotion`, commit `40b38caf7544e4df0826d9ff7e69fbd290e8e36f` (parent `49fccb6b38fcca2d53621ed558754cab6e63a9a1`). Not pushed.

## Old → new names

| old (private) | new (public) |
|---|---|
| `Complexity.sat_takeTrues_repr` | `Std.Sat.CNF.takeTrues_repr` |
| `Complexity.sat_parseLit_repr` | `Std.Sat.CNF.parseLit_repr` |
| `Complexity.sat_parseClause_repr` | `Std.Sat.CNF.parseClause_repr` |
| `Complexity.sat_parseClauses_repr` | `Std.Sat.CNF.parseClauses_repr` |
| `Complexity.sat_parse_repr` | `Std.Sat.CNF.parse_repr` |
| `satSyntaxStep` / `satSyntaxSuffix` | `CNF.syntaxStep` / `CNF.SyntaxSuffix` (Prop def) |
| `satSyntaxSuffix_cons/_nil/_run` | `CNF.syntaxSuffix_cons/_nil/_run` |
| `satSyntax` / `satSyntax_spec` | `CNF.syntaxOK` / `CNF.syntaxOK_spec` |
| `taut_{takeTrues,parseLit,parseClause,parseClauses,parse}_shape` (Tautology) | deleted; uses cite `CNF.parseLit_repr`, `CNF.parseClause_repr`, `CNF.parse_repr` |
| `Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc` | same name, moved Zone → **Catalog** |

## Files (lines before → after)

- `Formulas/CNFEncoding.lean` 475 → 744
- `ClassNP/SAT.lean` 4635 → 4407
- `ClassNP/Tautology.lean` 1728 → 1629
- `Build/Catalog.lean` 12732 → 12756
- `Build/Zone.lean` 1191 → 1173

## Verification

Command: `leanelab.sh <wt-p4> oleans-m1 <file>`.

| file | exit | errors | warnings vs. original |
|---|---|---|---|
| `CNFEncoding.lean` (direct) | 0 | 0 | 0 → 1: `unnecessarySimpa`, moved in with `syntaxSuffix_cons` |
| `Catalog.lean` (direct) | 0 | 0 | same message text as HEAD copy (90) |
| `ScratchSAT.lean` | 0 | 0 | 84 = 84, same multiset (reordered; 4 messages quote renamed identifiers) |
| `ScratchTaut.lean` (includes the CNF additions; Tautology uses them) | 0 | 0 | +1, the moved `unnecessarySimpa` (line 180, inside the added block 18–278); body 0 = 0 |
| `ScratchZone.lean` | 0 | 0 | same text (2 `sorry`) |

- Moved code is identical to the originals apart from renames, `CNF.` prefixes and docstrings (diffed).
- Every rename was counted: SAT 2/4/6/8/10 (`parseLit_repr`/`parse_repr`/`syntaxStep`/`syntaxOK_spec`/`syntaxOK`); Tautology 1/1/2.
- grep: no file in `TCSlib/` still uses a deleted private name. `satSyntax_poly` untouched.
- Only `Zone` uses `spaceUsedByTape_le_card_Icc`, and it imports `Build.Catalog` directly.
- Scratch files deleted.

## Judgement calls

1. **Import added**: `Mathlib.Tactic.FinCases` in CNFEncoding (needed for `fin_cases`). No TCSlib import.
2. **Tautology**: `taut_parse_shape` states exactly what `parse_repr` states. Its four helpers also duplicate the promoted lemmas exactly (`takeTrues` up to `.symm`), and one would have been left unused, so all five were deleted.
3. **Move 3 destination**: Catalog, per the coordinator's revision. The lemma is at line 392, just before `catalog_space_bound`. Its explicit `{k}` hides Catalog's `variable {k}`, so the statement is unchanged.
4. Zone's module-docstring bullet now points to the new home, and its empty `### The cardinality export` header was removed. One renamed SAT line over 100 characters was re-wrapped.
5. **Commit subject**: it says "moved to Catalog" instead of the briefed "Deterministic" to match the actual move.

## Duplicates for the maintainer to retire (left unchanged)

- `Catalog.lean:407` private `catalog_space_bound` is a special case of the moved lemma (interval `[-1, L]`).
- The same interval-cardinality argument is written out inline in Catalog's `f2_poly_space`, `f2_counter_space`, `a2_map_space`, `f2_space_radius` and `capture_visitedByTapeHead`, and in Embed (around line 480). Seam has none.

## Stale non-Lean references (not edited)

- `blueprint/src/chapter/Complexity/ClassNP/SAT.tex` and `Tautology.tex` still have `\lean{}`/`\uses{}` entries for the old private names. `dep_graph.json` does too; regenerate.
- `machine-library-design.md:1172` still says the lemma lives in `Build/Zone.lean`.

## Downstream replay (reverse import closure)

Counts: CNFEncoding 37, SAT 29, Tautology 2, Catalog 23, Zone 2. Union with the 5 edited modules: 55 (each group includes its facade):

- `TCSlib`, `ComputationalModels`
- `CircuitComplexity`: `CircuitEvalNP`, `CircuitSatNPHard`, `CircuitSatReduction`, `CircuitSatReductionMachine`, `CircuitSatReductionMachineTapes`, `CircuitSatReductionSpec`, `CircuitSatReductionValid`, `DAGCircuitSatLang`, `KarpLipton`, `KarpLiptonPrefix`, `KarpLiptonSearchFamily`, `LogspaceTableau`, `Meyer`, `MeyerComplete`, `MeyerSigma`, `MeyerSound`, `MeyerSoundInput`, `MeyerVerifier`, `MeyerVerifierGlue`, `UniformTableau`
- `ClassNP`: `SAT`, `Tautology`
- `ClassOracle`: `Classes`, `SATOracle`
- `ClassPSPACE`: `TQBF`
- `CookLevin`: `Hardness`
- `Diagonalization`: `EXPCOM`, `Relativization`
- `Formulas`: `CNFEncoding`, `DNF`, `QBFEncoding`
- `SpaceComplexity`: `Inclusions`
- `TuringMachine`: `Build.{Catalog, CertShell, CfgRecord, CounterLoop, InputCall, InputLength, OracleSim, RecordTable, Scan, Zone}`, `CodeSimulator`, `Codes2Tape`
