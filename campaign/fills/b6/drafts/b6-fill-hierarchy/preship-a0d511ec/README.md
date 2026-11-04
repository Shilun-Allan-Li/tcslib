# B6's H, the space hierarchy: the pre-ship at #177's tree (maintainer, 2026-11-04)

**Tree:** worktree `wt-hps` at `a0d511ec61b2e40b2216e44c07278531fc33a2e6` (#177, `lean/np-closure`:
`preimage_mem_NP` in `ClassNP/PClosure`, the campaign after #175 merged in). `NTimeDiagonalizer`
(#176) is outside H's order list, so this holds for the issue tree whichever of #176 and #177
merges first. **Snapshot:** `oleans-lnpc3` (`replay-lnpc3`, passed). Lean through
`tools/leanelab.sh`, one elaboration at a time; each `.out` is the raw output, paths stripped.

| Check | Result | File |
|---|---|---|
| The overlay (four imports: `SelfUniversal`, `Build/WindowRun`, `WindowClock`, `ClassNP/PClosure`) | exactly the four sorry warnings (154, 271, 288, 318 = base 150, 267, 284, 314 + 4), no other diagnostic | `HierarchyOverlay.*` |
| Import probe | 68 checks, 0 errors: the first round's 65 and `spaceConstructible_poly` (in `Constructible` since #175), `preimage_mem_NP`, `preimage_mem_P` | `HImportProbe.*` |
| Where each name lives | 23 modules (`HWhere.*`, by `Environment.getModuleIdxFor?`) | `HWhere.*` |
| Route probe, **now sealed** (5 definitions: `SpaceConstructible`, `SPACE`, `logSpace`, `LOGSPACE`, `PSPACE`; the four `@[simp]` TCSlib definitions erased) | `hr_inclusion`, `hr_logSpace_dom`, `hr_logspace_ssubset`: exit 0, each on `[propext, Classical.choice, Quot.sound]` | `HRouteProbe.*` |
| Seal controls (5 `rfl`, 4 `simp`) | unsealed 9 of 9 pass; sealed 9 of 9 fail | `HSealControl_*` |
| Duplication probe (6 `exact?`) | none closes, from the four-import overlay; in particular `logSpace n ≤ n + 1` and `LOGSPACE ⊆ PSPACE` are not in reach (below) | `HDupProbe.*` |
| Order list | **218 modules**, **63 roots**, **26 sorried declarations in 10 modules** (`Hierarchy`'s four, `Savitch`'s `savitch`, and the inherited twenty-one) | `order.txt`, `roots.txt`, `base-sorries.txt` |
| Lint | `SpaceComplexity` 0 FAIL, 83 WARN over 110 files; `Hierarchy` 321 lines, 4 public, 0 private; the policy linter: `Hierarchy`'s module docstring lacks `## Main definitions` (the base's) | `lint-base-SpaceComplexity.txt`, `style-lint-base.txt` |
| Screen base | 27 files (`screen-population.txt`), at the overlay commit `45a46c93`, clean | 1,338 declarations, 740 pairs, 207,465 characters; `Hierarchy` in no pair; 766 s, 1.71 GB. **To re-take at H's issue:** the API PR moving the `ARMWidth` space facts changes `Basic`, `SpaceClasses` and `Constructible`, three population files |

**An open choice (for the user).** `hr_logspace_ssubset` proves `logSpace n ≤ n + 1` inline
(`logSpace_eq`, `Nat.log_le_self`): the statement of `Machines/ARMWidth`'s public
`logSpace_le_succ`, which is the ledger's LS-1 family (accepted debt, retired in 12.2c). `ARMWidth`
is outside `Hierarchy`'s upstream closure (106 modules with the overlay) but inside H's order list,
and its closure (42 modules) adds no module to that list and makes no cycle; only the
`SpaceComplexity` facade imports `Hierarchy`. **Tested:** a fifth overlay import of `ARMWidth`
elaborates with exactly the four sorries (`HierarchyOverlay5.*`), and the import probe with it
resolves `logSpace_le_succ` and `LOGSPACE_subset_PSPACE` (70 checks, 0 errors, `HImportProbe5.*`).
With it the fill cites `LOGSPACE_subset_PSPACE` and adds no LS-1 member.

**Ruled (user, 2026-11-04), superseding the open choice:** no fifth import. An API PR first moves
`logSpace_le_succ` and `logSpace_le_of_le_mul_two_pow` to `SpaceComplexity/Basic`, and
`LOGSPACE_subset_PSPACE` and `SPACE_succ_pow_subset_PSPACE` to `SpaceClasses` (all four out of
`Machines/ARMWidth`), and re-points `Constructible`'s two inline steps; H then cites them from its
four-import overlay. H issues after that PR merges, with the pre-ship re-taken.
