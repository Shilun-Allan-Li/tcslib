# Check 5: the duplication population and the screen

## The population (16 files, `preship-77f1eb4f/screen-population.txt`)

- **The owned file:** `NDCodeSimulator`.
- **Every file the route cites:** the homes of every declaration the brief cites are `NDCodes`,
  `MathlibBridge`, `Composition`, `Finite`, `CodeSimulator`, `ChoiceReplay`, `Build/StepBlock`,
  `CodeFormat`, `CodeParser`, `Encoding`, `Nondeterministic`: all in. One home is not:
  `Deterministic.lean`, of `MultiTapeTM.ComputesInTimeAndSpace`, which the brief only seals (no
  route step reads it, so no copy hazard).
- **Known hazards:** `Codes2Tape`, `CircuitComplexity/UHaltMachine`,
  `Diagonalization/NotTimeConstructible`, `ClassNP/PolyTime`.

## The copy-hazard search (the tree at `6e8db28f` and both open PR heads)

What the route would prove: a record-list skip, lockstep record rounds, a header split by length,
the replay table's layout, `workReadsK`'s snoc form, a record widening, `Primrec` compositions of
`option_casesOn` / `nat_iterate` / `codePrimPrefix`, a running-maximum monotonization, and the
compile-and-compose step. `git grep` over `TCSlib/` for `Primrec`, `codePrim`, `codeSkipActionK`,
`codeSkipRepeat`, `tableBitsK`, `workReadsK`, `actionBitsK`, `serializeK`, `replayTM`,
`nat_iterate`, `codePrim_machine`, `computesFunInTime_comp`, `ComputesInTime.mono`,
`Finset.le_sup`, `Fin.snoc`, `Fin.cons_snoc_eq_snoc_cons`:

| File | What it has | In the population? | Hazard |
|---|---|---|---|
| `CodeSimulator` | `skipRepeat_consumes`, `canonSkipRepeat_add`/`_mul`, `canonSkipTable_eq` (repetition algebra and length bounds), the table grammar | yes | the nearest relatives of the skip and rounds lemmas: covered |
| `MathlibBridge` | the `codePrim*` blocks, `codeSkipRepeat_iter`, `bridge_binary` (a length-indexed `Finset.univ.sup` time bound) | yes | covered |
| `NDCodes`, `Codes2Tape`, `CodeFormat`, `CodeParser` | format readers and skippers, their erasure and append laws | yes | covered |
| `UHaltMachine`, `NotTimeConstructible` | private `Primrec` proofs and `codePrim_machine` pipelines | yes | covered |
| `CircuitComplexity/UHalt` | one `Primrec.list_map … list_range` composition (`List.replicate`), a `Computable` argument | no | none (different combinators, a few lines) |
| `Uncomputability/Computable` | `Computes.exists_computesFunInTime`: a length-indexed `Finset.univ.sup` bound with `ComputesInTime.mono` | no | low: a different statement from the running maximum over `range (n + 1)`, 6 lines; optional to add |
| `UniversalK` | `ss_lengthBound` (the same length-indexed `sup`), one `serializeK_eq` use on tapes | no | low (as above) |
| `Build/SeamLayout`, `Build/StepBlockForward`, `Build/StepBlockLoop`, `SelfUniversal` | `tableBitsK`/`serializeK` read on tapes (`sl_read_table`, `sl_read_unary`) | no | none (tape-level, not list identities) |
| `ClassNP/ExhaustiveReplay`, `Diagonalization/NTimeHierarchy` | `replayTM` runs, not tables | no | none |
| Composition users (`ClassNP/*`, `Build/Catalog`, `Build/Primitives`, …) | `computesFunInTime_comp` applications | `PolyTime` only | the 10-line compose idiom; `PolyTime` stands for it |

No file has a private copy of the record skip over a list of records, the lockstep rounds, the
record widening, the replay-table identity, the `workReadsK` snoc lemma or the running-maximum
monotonization (the draft's claim holds).

**Open PR heads (fetched):**
- `origin/lean/phasehost-last` (#156, `0e5f210b`, merge-base `906a9d7b`): six files —
  `Build/Seam` (the new last-phase lemmas) and phase-host prefix re-points in `Build/StepBlock`,
  `CodeSimulator`, `Build/WindowRun`, `Build/OracleSim`, `SpaceComplexity/Inclusions`. None
  touches the route's material; two of them (`StepBlock`, `CodeSimulator`) are in the population,
  so the screen base moves if #156 merges before issue (F9).
- `origin/complexity/arora-barak-ch7` (#135, `a7433f3f`, onto `main`): `Computable.nat_rec`
  compositions in `Randomized/BiasedCoinHalting`; not on the campaign branch; no hazard.

The rule-of-thumb items: the drafting brief's input-rewind lesson does not apply (no rewind);
the population needs no `Simulation`/`Build/InputRewind`.

## The screen (re-run once at the review worktree, niced, under the lock)

`scripts/run-screen.sh`: `nice -n 10 python3 -I scripts/copy-text-screen-v3.py <worktree>
<the 16 files>`, start 05:10:59Z, end 05:18:00Z (7 minutes on this host; 12.6 on the drafting
host), exit 0, empty stderr, the lock released.

- **Byte-identical to `preship-77f1eb4f/screen-base.txt`** (`cmp`): 541 declarations, 173 pairs,
  86,076 characters.
- No pair has an `NDCodeSimulator.lean::` declaration on either side (the brief's claim).

RESULT: PASS. Population complete for the route; `Uncomputability/Computable.lean` an optional
addition (one 6-line idiom, F7).
