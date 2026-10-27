# B6's H, the space hierarchy: the first pre-ship checks (maintainer, 2026-10-27)

**Tree:** the frozen worktree at `940671e0`, whose Lean is the campaign's (the tree after #172; #174 is
open but `NDHost` is outside H's closure). **Snapshot:** `oleans-lhh`. Lean ran through
`tools/leanelab.sh`, one elaboration at a time; each `.out` is the raw output, paths stripped.

| Check | Result | File |
|---|---|---|
| The overlay | `Hierarchy.lean` with three imports added (`TuringMachine/SelfUniversal`, `Build/WindowRun`, `SpaceComplexity/WindowClock`): exactly its four sorry warnings (153, 270, 287, 317), no other diagnostic | `HierarchyOverlay.*` |
| Order list | **198 modules** (the base's 183 and the overlay's 15), **54 roots**, **26 base sorries in 10 modules**; no `NDHost`, `NDNormalForm` or `NTimeDiagonalizer` | `order.txt`, `roots.txt`, `base-sorries.txt` |
| Import probe | 65 checks of 65 names, 0 errors: the readings, the hosts, the runner, the record rows, the window facts, the normal forms, the composition's space lemmas, `counterValue_bits` for the radius word | `HImportProbe.*` |
| Route probe | `hr_inclusion` (the inclusion half), `hr_logSpace_dom` (`A · logSpace n ≤ n + 1` eventually), `hr_logspace_ssubset` (`LOGSPACE ⊂ PSPACE` from the hierarchy's statement): 0 diagnostics, each on `[propext, Classical.choice, Quot.sound]`, through published readings only | `HRouteProbe.*` |

**Outside the closure** (found by the import probe):
- `Complexity.spaceConstructible_poly` (`Savitch.lean:158`), which `SPACE_linear_ne_NP` needs at
  degree two. Its home is a decision (the route note).
- `Complexity.LOGSPACE_subset_PSPACE` (`Machines/ARMWidth`): not needed; `hr_logspace_ssubset`
  derives the inclusion from `SPACE.mono` and `space_poly_subset_PSPACE`.

Still to take before issue: the seal controls, the duplication probe, the screen base, the lint
base, and the order list at the issue commit.
