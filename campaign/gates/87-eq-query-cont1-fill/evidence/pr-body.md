The stage query's main machine: `Turing.NTimeDiag.exists_queryTM` (`Diagonalization/NTimeDiagonalizer.lean`) is proved. The machine is the phase host of a setup, a locator and two writers over a kit of published calls. The setup computes `bits n` and the first rung. Each locator round runs `f`'s witness under the step clock, tests the rung against `|bits n|`, and builds the next rung `2^{X⁴}` in unary. The loop stops at the stage `stage f n` within a linear bound. The writers emit the query's word. The guard and the reduction to the main machine landed in #173. The file keeps one sorry, `exists_diagonalizer`, which is out of scope.

**Commits**
- Eight commits by the fill worker, their subjects reworded and their authorship kept.
- One maintainer commit of landing edits:
  - the new docstrings drop internal labels;
  - the module header records the target as proved;
  - two private `Nat.bits` lemmas cite Mathlib (`Nat.size_le_size`, `Nat.lt_size_self`, through `Nat.size_eq_bits_len`);
  - seven double blank lines become single;
  - nine private proofs gain proof sketches.

**Checks** (against the snapshot of the tree after #174, the tip's Lean)
- **Elaboration:** one warning, `exists_diagonalizer`'s sorry.
- **Axioms:** `exists_queryTM` and every new private use only the standard three.
- **Statements:** no public declaration is added or changed (22 → 22); 211 new privates.
- **Rule 10:**
  - The review's maximal seal covers every other-file definition the new code can reach, 275 in all. The body elaborates sealed, with 289 controls that close unsealed and fail sealed.
  - No other-file definition is passed to `simp`, `rw` or `unfold`.
- **Lint:** both linters pass, but for the file's size note.

**Merge conditions:** the fill gate, and the replay of the downstream closure (`NTimeDiagonalizer`, `NTimeHierarchy`, the `Diagonalization` facade).

🤖 Generated with [Claude Code](https://claude.com/claude-code)
