An API PR in `SpaceComplexity`: `Complexity.spaceConstructible_poly` (the polynomial bounds `n ^ c + 1`, for `c ≥ 1`, are space-constructible) moves from `Savitch.lean` to `Constructible.lean`, beside the logarithmic and linear rows. The space hierarchy's corollary `SPACE_linear_ne_NP` needs it at degree two, and `Hierarchy.lean` does not import `Savitch`. The user ruled (2026-10-27) that the lemma moves to `Constructible`, with its statement unchanged.

**The move**
- `Constructible.lean` gains the block: the eight private helpers (`scp_tailδ`, `scp_tailO`, `scp_transduce_copy`, `scp_transduce_tail`, `scp_tail_pow_le`, `scp_value`, `scp_time_arith`, `scp_space_arith`) and the theorem. It imports `ClassNP/Transducer` (the tail transducer). Its closure gains four modules (`ClassNP/Transducer`, `ClassNP/PolyTimePairing`, `ClassNP/PolyTime`, `TuringMachine/Build/Primitives`); there is no cycle.
- `Savitch.lean` loses the block and its import of `ClassNP/Transducer`, which only the block used; `Savitch` imports `Constructible`, so its closure is unchanged. Its module docstring says where the lemma now is.
- **The statement and the name are unchanged.** The block's text is unchanged except for three hunks:
  - the docstring's citation tag `[AB09, p. 79]`, as `spaceConstructible_logSpace` carries;
  - the proof's dominance step `logSpace n ≤ n + 1`, which cited `Machines/ARMWidth`'s `logSpace_le_succ` (outside `Constructible`'s closure), is now proved through `logSpace_eq` and `Nat.log_le_self`;
  - the proof sketch's citation of that step.

**Checks** (against the snapshot of the tree after #172, whose closure for these two files is the tip's)
- **Elaboration:** `Constructible` 0 diagnostics; `Savitch` its one expected sorry warning (`savitch`). `spaceConstructible_poly` and the file's other three theorems use only the standard axioms.
- **Rule 10:** the moved block, sealed over the 12 other-file definitions it reaches with the three `@[simp]` ones erased, has 0 diagnostics; the 15 controls close unsealed and fail sealed. No other-file definition is passed to `simp`, `rw` or `unfold`.
- **Freeze:** one public and eight private declarations leave `Savitch` and arrive in `Constructible`; nothing else is added, removed or changed.
- **Lint:** `SpaceComplexity` 0 FAIL, the base's 82 warnings.

**Merge conditions:** an API gate (gate 86), and the replay of `Constructible`'s and `Savitch`'s downstream closure.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
