Four general facts about space bounds and space classes move out of `SpaceComplexity/Machines/ARMWidth` to the files that define their subjects. `ARMWidth` keeps its register-machine wrappers.

| Declaration | From | To |
|---|---|---|
| `Complexity.logSpace_le_succ` (`logSpace n ≤ n + 1`) | `Machines/ARMWidth` | `SpaceComplexity/Basic`, beside `logSpace_eq` |
| `Complexity.logSpace_le_of_le_mul_two_pow` | `Machines/ARMWidth` | `SpaceComplexity/Basic` |
| `Complexity.LOGSPACE_subset_PSPACE` | `Machines/ARMWidth` | `SpaceComplexity/SpaceClasses`, beside `space_poly_subset_PSPACE` |
| `Complexity.SPACE_succ_pow_subset_PSPACE` | `Machines/ARMWidth` | `SpaceComplexity/SpaceClasses` |

**Why.** The space hierarchy's fill needs `logSpace n ≤ n + 1` and `L ⊆ PSPACE`, but `ARMWidth` is outside `SpaceComplexity/Hierarchy`'s imports. `Constructible` already proved `logSpace n ≤ n + 1` inline twice; both steps now cite the lemma. The moves were ruled by the user (2026-11-04), including the other two facts, which also fall under this file's subject.

**What changes.**
- The names and statements are unchanged. `ARMWidth`'s edit is mechanical: the declarations, their docstrings and its module docstring's entries.
- Every user of the four results already imports the new homes. The users are `ARMWidth` itself, `ARMWidthExample`, `NARMProof`, `SavitchARM/Reach`, `SavitchARM/Correct`, `TQBFARM/Correct` and `Logspace/ISCountGenCorrect`.
- `SpaceClasses` now imports `ClassP/P`, for `succ_pow_le`. That adds one module, no Mathlib root and no simp lemma, and every module downstream of `SpaceClasses` already imports `ClassP/P`. So no other module's environment changes.
- `LOGSPACE_subset_PSPACE` now reads `LOGSPACE` through `LOGSPACE_eq`.

**Checks so far.** The four files and all seven users elaborate with 0 diagnostics, in a local chain over the campaign's snapshot. The merged-tree replay (`replay-lsm1`, the four files' 137 downstream modules) and the audit gate are pending.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
