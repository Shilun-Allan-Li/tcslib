# F3 continuation 2: the pre-ship at the campaign tip `906a9d7b` (maintainer, 2026-10-23)

Tree: `906a9d7b` (after #155; its Lean tree equals #155's head `6efc5be0`). Snapshot:
`oleans-lslsk` (#155's replay, the same tree). Every elaboration through `leanelab.sh`. This
re-runs the pre-ship of `0416ffea` (`../preship-0416ffea/`) after #149, as the draft required.

| Check | Result | File |
|---|---|---|
| Owned file | `SpaceComplexity/WindowClock` (458 lines; target 426, sorry 456, status paragraph 404–424): exactly the target's sorry warning | `elab-WindowClock.out` |
| Order list | 182 modules: the 176 of `0416ffea` and six `Build/Contract` modules, which #150's `CfgRecord` brings into the closure; 54 Mathlib roots, unchanged | `order.txt`, `roots.txt` |
| Base sorries | 28, the same set | `base-sorries.txt` |
| Import probe | 102 checks: the 100 of `0416ffea` and the space API's `spaceUsed_eq_sum` and `spaceUsed_le_of_abs_le`. 0 errors, 0 warnings | `F3C2ImportProbe.*` |
| Consumer probe | continuation 1's, unchanged: 0 errors | `F3ConsumerProbe.out` |
| Join probe | gate 56's published version: exactly its two bare controls fail, as in gate 56's record | `F3C2JoinProbe-published.out` |
| Route probe | the 12-definition seal as before, plus `f3c2_space_api`: the target's space clause from its envelope clause by `spaceUsed_le_of_abs_le`, with `spaceUsed`, `spaceUsedByTape` and `visitedByTapeHead` sealed. It passes; the only error is the old sum route's sealed control, line 168 | `F3C2RouteProbe.*` |
| Seal controls | 12 `rfl` goals fail sealed, at the same positions as at `0416ffea` | `F3C2RouteSealControl.out` |
| Screen base | the 21 files: 1,058 declarations, 513 pairs. Against `0416ffea`'s base, all changes are #150's in `CfgRecord`: 6 new in-file pairs and 3 gone, among them `recordRun_trans` ↔ `Segment.trans` (100%) | `screen-base.*`, `screen-vs-0416ffea.txt` |
| Lint | `SpaceComplexity`: 0 FAIL, 81 WARN over 107 files; `WindowClock` none | `lint-spacecomplexity.txt` |

**The lists' tool.** `fillinputs.py` (here) reads the tree with `git show`. At `0416ffea` it
reproduces the earlier roots and base sorries exactly, and the order list's set; its topological
order differs from the earlier list's, and any topological order bootstraps.

**The route is now fully published.** At `0416ffea` the space clause had no published route
(the user's ruling of 2026-10-22: the space API first). With #149 merged it follows from the
radius lemma at `r = C · (L + 1)`, sealed.
