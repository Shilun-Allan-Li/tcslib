Proof fills for fifteen of the GSW phase-6b targets stated in #377 (Gate 46), and the two public glue lemmas that ruling Q-6BF-3 (A) allows. No statement, header, definition or reader changes: proofs, refreshed proof sketches, the module admission sentences, and the ruled insertions only.

## Contents
- **U14+U16**, `Homomorphic/GSW/Bootstrap.lean` and `Leveled.lean`: G9 `encrypts_bootNAND`, G10 `decrypt_fheEval`, G18 `decrypt_fheEvalCircuit`, G12 `decrypt_keygen_fheEvalCircuit`, G13 `bootNoise_le`; L2 `encrypts_leveledEval`, L3 `decrypt_keygen_leveledEvalCircuit`. Two commits. The allowed public helper `encrypts_bootGate` (the brief's statement, byte for byte) and one private helper.
- **U15+U17**, `Circular.lean` and `LeveledSecurity.lean`: G15 `distAdv_fheView_noEvk_le`; L4 `distAdv_levelHybrid_le`, L5 `distAdv_leveledView_le`. Three commits; seven private helpers, no public one. L4's route is accepted as delivered (Q-U1517-1 A).
- **U18+U19**, `PolyRatio.lean` and `Asymptotic.lean`: G16 `bootRatio_le_poly`, G17 `decrypt_fheEval_of_ratio` and `decrypt_leveledEval_of_ratio`; A1 `indCPA_of_dlweAssumption`, A3 `leveledINDCPA_of_dlweAssumption`, both proved from their frozen `heff` hypotheses, which stay (Q-6BF-1 A). Two commits. The allowed public helper `Parameters.ofFamily_columns_le`, kept in its `Nat` form (Q-U1819-1 A), and one private helper.
- The seven worker commits are applied with `git am -3`, keeping the workers' authorship, on the records tip `53e430b6` (its `TCSlib` tree `745bf4b4` is #392's merge). The six files are blob-identical to the delivered `src/`; the last worker commit's `TCSlib` tree, `37ae0f32`, is the full 6b stack the reviews replayed.
- Two maintainer landing edits, docs only (6b fill rulings, Seyoon: "fix both"):
  - **LE-u1517-doc** (U1517-F02): "Glue." notes, Lean-order formulas and step comments on the seven private helpers of `LeveledSecurity.lean`, as prepared in the review evidence.
  - **LE-u1819-doc** (U1819-F02): A1's and A3's proof sketches name `Parameters.ofFamily_columns_le` where the proofs use it, instead of `Parameters.ofFamily_width` and `dimension_le`.
  - With comments and docstrings stripped, the code is identical before and after each edit.
- 6 files, +883 / −90; 9 commits.

## Maintainer reviews (records: `briefs/lattice-gsw/phase6/issued-6b-fills-r1/U14-U16/final-r1/`, `.../U15-U17/final-r1/`, `.../U18-U19/final-r1/`)
- **Verdicts:** all three accept; 0 blockers, 0 majors.
- **Integrity:**
  - patches reproduce the workers' heads on B6;
  - headers and statement prose of the 15 targets byte-identical to B6;
  - no `sorry`, `admit`, `native_decide`, `axiom` or `opaque`;
  - no new attribute, `set_option` or import.
- **decls2** against the records tip: ADDED exactly `encrypts_bootGate` and `Parameters.ofFamily_columns_le`; 0 changed, 0 removed.
- **Duplication:** the inline copies of three small facts are accepted and recorded as ledger **DL-71** (publish `le_bootNoise`, `LWE.sample_eq` and `distAdv_nonneg` after the fills land, and re-point the copies).
- **Minors:** U1416-F01 (records side: the pre-dispatch sweep missed `m·B ≤ bootNoise P (m·B)`; DL-71) and U1517-F02 (fixed by LE-u1517-doc).

## Landing re-check (copy of olean snapshot #11, at this branch's head)
- 12/12 modules rc 0, including the root `TCSlib`; 0 errors, 0 `sorry` warnings; state check 1,456 OK.
- Admissions fall from 33 in 14 modules (records tip) to 18 in 8: all 15 targets are gone, and the six files hold none.
- **Axioms:** the 15 targets and both helpers are standard-only; 0 `sorryAx` over the 168 constants of the six modules.
- **Seals:** canonical coe-A, 0 errors on the six files (444 / 479 / 464 / 1,561 / 1,394 / 1,654 requests); paired controls for both helpers ALL_OK.
- **Lint:** no FAIL or WARN change.

Draft until the Codex fills gate (Gate 55) passes.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA
