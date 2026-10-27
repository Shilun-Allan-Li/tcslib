# #172 on #173's tree: a pre-check before the replay (maintainer, 2026-10-27)

- **The merge:** a local trial merge of #173's head `599497bc` into #172's head `33d68537`, in a
  detached worktree, was clean (`2973a416`, not pushed). Against `599497bc`, its Lean differs in
  `NTimeHierarchy` alone.
- **The elaboration:** `NTimeHierarchyAxTrial.out`. Against `oleans-leqcp1` (#173's replay
  snapshot), the gate's probe `../NTimeHierarchyAx.lean.txt` (unchanged) was elaborated: the head
  module with the three axiom prints and the review's sorry walk. Exit 0, no diagnostics, 17.6 s,
  1.9 GB. The output is identical to the gate's run against `oleans-lb5am`
  (`../NTimeHierarchyAx.out`, paths stripped). All three results are on
  `[propext, sorryAx, Classical.choice, Quot.sound]`, with direct `sorryAx` only in
  `exists_codeNDTM_accepts_linear` and `exists_diagonalizer`.

This is not the replay. `mk-next.sh` writes the replay once #173 merges (closure
`NTimeHierarchy` and the `Diagonalization` facade, chained from `oleans-leqcp1`).
