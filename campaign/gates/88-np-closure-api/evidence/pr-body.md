An API PR in `ClassNP/Reductions`: `Complexity.mem_NP_of_polyTimeReducible`, that is, if `L ≤ₚ L'` and `L' ∈ NP` then `L ∈ NP`, beside `mem_P_of_polyTimeReducible`. The space hierarchy's corollary `SPACE_linear_ne_NP` (`SpaceComplexity/Hierarchy`) needs it: it pulls a padded language back along the padding reduction. The user ruled (2026-10-27) that the maintainer publishes it by an API PR before H's fill issues.

**The proof**
- `L'` is read in the bounded-certificate form `mem_NP_iff_exists_length_le`: a verifier `V ∈ P` and a bound `C (|y| + 1) ^ c`.
- The verifier for `L` accepts `⟨x, u⟩` exactly when `|u| ≤ C (|f x| + 1) ^ c` and `⟨f x, u⟩ ∈ V`. That is the intersection of a length test against a unary word and a preimage of `V` under a polynomial-time pair map, both in `P` by `ClassNP/PClosure`'s rows (`inter_mem_P`, `lenLe_preimage_mem_P`, `preimage_mem_P`).
- Its certificate bound is `C (A + 1) ^ c (|x| + 1) ^ (d c)`, from the reduction's output bound `|f x| ≤ A (|x| + 1) ^ d`.
- `Reductions` now imports `PClosure`: 13 modules join its closure, with no cycle.
- `prefixTM_copy`, an existing private, gains its proof sketch, so the policy linter is clean on the file.

**Checks** (against the snapshot of the tree after #174, the tip's Lean)
- **Elaboration:** 0 diagnostics; the new theorem uses only the standard axioms.
- **Rule 10:** the theorem, sealed over the six other-file definitions it reaches with the three `@[simp]` ones erased, has 0 diagnostics; the six controls close unsealed and fail sealed. It reads `NP` only through `mem_NP_iff_exists_length_le`, and its `simp` arguments are theorems.
- **Freeze:** 10 → 11 public, nothing else added, removed or changed.
- **Lint:** `ClassNP` 0 FAIL, the base's warnings; the policy linter 0 findings on the file.
- **API copies:** no ref has a declaration of this name or of an `NP` closure under `≤ₚ`.

**Merge conditions:** an API gate, and the replay of `Reductions`' downstream closure.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
