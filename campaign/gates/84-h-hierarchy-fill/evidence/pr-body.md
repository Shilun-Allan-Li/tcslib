Proves the nondeterministic time hierarchy theorem, `Complexity.ntime_hierarchy` ([AB09, Theorem 3.2]), from its two contracts: the diagonalizer `Turing.NTimeDiag.exists_diagonalizer` and the linear coded normal form `Turing.FinNDTM.exists_codeNDTM_accepts_linear`. Both are still `sorry`, so the theorem and its two corollaries now reach `sorryAx` only through them. The proof is the one the review of H's fill brief assembled (`campaign/fills/h/reviews/brief/`). The user ruled (2026-10-27) to land it by a maintainer PR instead of a fill, with the truncation step through the published `Turing.run_take_of_halted` (a second import).

**What changes (one file, `Diagonalization/NTimeHierarchy`)**
- **Two imports:** `Diagonalization/NTimeDiagonalizer` (the contracts) and `TuringMachine/ChoiceWords` (`run_take_of_halted`). `ChoiceWords` imports only Mathlib, so there is no cycle.
- **The target's body:** lazy diagonalization over one late stage of the alleged decider's code. The middle steps chain, then the flip at the top, then the transfer at the bottom.
- **Ten private lemmas:**
  - the chain's induction;
  - the absorption, a constant fold and the inclusion;
  - the top, bottom and middle thresholds;
  - a late stage of a code;
  - the truncation of an acceptance at an all-branch budget, and its reading for a decider.
- **`ntime_hierarchy_of_pos`:** the same statement; its factor-2 fold now cites the shared private `nh_fold`.
- **Docstrings:**
  - the target's sketch is rewritten to the proof as built;
  - the module status is updated;
  - the corollaries' stale "fill pending" is removed.

**Checks** (against the snapshot after #170)
- **Elaboration:** 0 diagnostics. The ten privates use only the standard axioms. An axiom walk finds `sorryAx` directly only in the two contracts, for all three results.
- **Rule 10:** sealed over the review's 12 definitions, with the four `@[simp]` TCSlib definitions erased, the module has 0 diagnostics.
- **Freeze:** 5 → 5 public declarations, with no statement changed, and 10 → 20 private. The body changes are the target and `ntime_hierarchy_of_pos`; `NTIME_linear_ssubset_square` changes only in its docstring.
- **Screen** (14 files): 224 → 226 pairs, none gone. The two new pairs:
  - the truncation leaf at 61% against `Nondeterminism`'s private copy of the same fact; disclosed and ledgered;
  - a 50% idiom pair.
- **Lint:** 0 FAIL, the base's warnings.

**Merge conditions:** a fill gate, and the replay of `NTimeHierarchy`'s downstream closure after #171 and E-Q's checkpoint 1 land.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
