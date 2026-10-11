# External audit pack — §12.8 statement gate, round 2 (full re-audit after repairs)

Campaign: Arora-Barak chapters 3-4. This is the **second round** of the §12.8
statement gate on PR #28 (`integrate/s12-8-statements`), the rich-alphabet
record layer R8.0–R8.8. Round 1 **failed**: 0 blockers, 1 major, 7 minors and
39 notes. The relevant records are attached:

- the round-1 pack, `audits/s12-8-statements-pack.md`;
- the findings, verbatim, in `audits/s12-8-statements-findings.md`;
- every disposition, in `audits/s12-8-statements-resolutions.md`.

A round with a major is followed by repairs and a **full re-audit**
(`workflow.md` §3). So this round audits the whole layer again, not only the
repairs. The gate closes on zero blockers and zero majors. The duplication
rule (`audits/TEMPLATE.md`, failure mode 5) is in force.

## What changed since round 1 (verify)

The round-2 delta patch is `audits/evidence/s12-8/s12-8-statements-r2-delta.patch`.
It covers four files, against the branch after it merged the campaign tip.

**The merge.** Between the rounds the branch merged the campaign tip, which
now contains epoch B1 (PR #26). B1 changed `Finite`, `Oracle`, `OracleFinite`,
`OracleNondeterministic`, the new `Build/OracleCall`, `Classes`, `SATOracle`,
`Relativization` and the facade. Its own gate is closed. None of those changes
is under audit here, but the replay below covers the merged tree. B1 filled
SATOracle's three sorries, so the base sorry set is now 7.

| Item | Change |
|---|---|
| **Major 1** (finding 1) | A new clause on `exists_recordStepTM`, `exists_recordEqTM`, `exists_recordTestTM` (`Build/CfgRecord.lean`) and `exists_inputSeekTM` (`Build/InputCall.lean`). Through the verdict or exit, every work head `j` satisfies `\|pos_u j − pos_0 j\| ≤ C·(size + 1)`. The size is the record layout length `L` for step and test, `fs`'s layout length for equality, and `\|w\|` for the seek. The auditor asked for this on the step and the seek; equality and test get it too, so that all record rows are uniform. Docstrings and sketches are updated |
| Note 28 | The step row's sketch names the saved-input-position obligation (binary, width `posWidth \|x\|`, restored after the read; no move at `\|x\| = 0`) and the clamping obligation (`0` and `\|x\| + 1`, as `moveInputPos` clamps) |
| Minor 2 | The input seek's sketch: `timed_rewind` stops at position `1` within `pos + 2`, then one left move |
| Minor 3 | The input call's sketch: split on entry = exit, with `seamReleaseTM_firstReturn` in that branch |
| Minors 4, 5, 6 | Docstrings: `recordValid_iff` (folds plus width templates); `Cfg.InWindow` (the record determines the configuration *core*, with the tag); `fieldOffset` (the end formula needs `fs ≠ []`) |
| Minors 7, 8 | Records only: the declfreeze erratum (3 citations, not 4) in the resolutions; Catalog's ledger denominator, 318/459 = 69.3%, in the ledger's new §12.8 section |
| **Q6, facade** (user decision) | `TCSlib/Complexity/TuringMachine.lean` imports `SymbolLift`, `Build/CounterLoop`, `Build/Scan`, `Build/InputCall` and `Build/CfgRecord`, with Contents entries. None of the five has the facade in its upstream closure. Nine older files of the topic are still absent; they are recorded as `backlog.md` FAC-1 |
| Q1–Q5, Q7 (user decisions) | Recorded in `machine-library-design.md` §12.8a §9, and Q7 also in §13d's G2 row. All seven of the auditor's recommendations were adopted. Only Q6 changes Lean |

## Brief for the auditor

1. **The major's repair.** For each of the four strengthened statements:
   - **Truth.** Is the head bound true for the construction its sketch
     describes, including the step row's saved input position, the lifted
     input seek on scratch digit tapes, the clamped position update and the
     not-windowed branch?
   - **Adequacy.** Does it give the named consumers what they need, without
     depending on native-head travel? Savitch needs `O(S)` per frame; logspace
     consumers need `O(log n)`.
   - **Composition.** Does the form, a radius `C·(size + 1)` about the entry
     heads with the same existential `C` as the time bound, compose under
     repeated calls and R1 embedding?

   `audits/evidence/s12-8/S128R2SpaceProbe.lean.txt` derives
   `spaceUsed ≤ k·(2R + 1)` from any clause of this form (a proved lemma). It
   instantiates that for the input seek and the record step. Is anything still
   missing? For example, should the input call (R8.5e) carry a space clause
   too? Its space is its witness machine's, so it was left without one.
2. **Full re-audit.** Re-confirm the round-1 results for the unchanged
   statements and definitions, and the minors' sketch and docstring
   corrections. In particular, check that no corrected docstring is now
   false.
3. **The facade wiring.** Check the import edges for cycles, for the five
   added imports and their Contents entries, and for clashes. `ConfigGraph`'s
   private `InWindow` is a separate declaration from `Turing.Cfg.InWindow`;
   the replay shows the facade and its 18-module closure elaborate. The root
   `TCSlib.lean`, the facade and `SpaceComplexity/ConfigGraph.lean` are now
   attached (finding 39).
4. **The decisions' records.** Do §12.8a §9 and §13d's G2 row record Q1–Q7
   accurately? Is FAC-1's list of absent files complete?
5. **Duplication.** The screen is unchanged: 408 pairs, the same set. Is any
   repaired statement or sketch a copy?
6. Anything else, in the standard table.

## Repository-side attestations (verify or challenge)

* **Replay** (`audits/logs/s12-8-statements-r2-replay.log`; order list
  `…-r2-order.txt`).
  - 18 modules: the downstream closure of the nine modules that differ from
    the campaign tip `6b7ff5ec`, in dependency order, with
    `ComputationalModels` and the root excluded.
  - It ran on the repaired branch `f36765d2`, into a snapshot of the B1 olean
    tree; the user ran it from the maintainer's command.
  - **0 errors**; every module exits 0.
  - **32 sorry warnings**: the base 7 (TQBF 4, Zone 2, Codes2Tape 1) plus the
    same 25 new statements (Seam 1, Catalog 12, CfgRecord 5, Scan 4,
    CounterLoop 1, InputCall 2). SATOracle has 0 now, and `SymbolLift` and
    the facade have none.
* **Probes** (`…-r2-probes.log`). Both were elaborated by the maintainer
  against the replay's olean tree, with no olean output:
  - the round-1 pre-ship probe, 35 executed examples, still 0 errors and 0
    warnings;
  - the round-2 adequacy probe, 0 errors and 0 warnings.
* **Freeze** (`…-r2-declfreeze.log`, against round 1's `510d85ea`).
  - Exactly four statements changed: the major's.
  - `fieldOffset`, `Cfg.InWindow`, `recordValid_iff` and
    `exists_inputCallTM` changed in their docstrings only.
  - Catalog's code is identical with comments stripped.
  - The facade gains the five imports. A sixth, `OracleCall`, comes from
    B1's merge.
* **Lint** (`…-r2-stylelint.log`). 0 FAIL. The same 14 file-size WARNs as in
  round 1.
* **Screen** (`…-r2-copytext.txt`). The round-1 after population on the
  repaired tree: 535 declarations, 408 pairs, 120,748 characters. These match
  round 1 exactly, with no new pair.
* **Inputs.**
  - The full patch against the campaign tip (`s12-8-statements-r2.patch`) and
    the delta patch.
  - All new and changed sources in their final state.
  - The cited layers: `Configuration`, `Deterministic`, `Finite`,
    `Simulation`, `Build/Convention`, `Build/Embed`, `Build/Loop` and
    `Robustness/AlphabetReduction`.
  - The facade, the root `TCSlib.lean` and `SpaceComplexity/ConfigGraph.lean`.
* **Evidence boundary.** No delivery zip exists; this is maintainer work.
  Replay, lint and probe results are attestations from the attached logs.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/s12-8-statements-r2-findings.md`.
