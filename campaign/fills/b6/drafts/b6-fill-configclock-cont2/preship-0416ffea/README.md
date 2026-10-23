# F3 continuation 2: the pre-ship at the campaign tip `0416ffea` (maintainer, 2026-10-22)

Tree: `0416ffea` (after #144; its Lean tree equals `0beb75a3`'s). Snapshot: `oleans-lsk2`
(#144's merged-tree replay, the same tree). Every elaboration through `leanelab.sh`.

| Check | Result | File |
|---|---|---|
| Owned file | `SpaceComplexity/WindowClock` (458 lines; target 426, sorry 456, status paragraph 404–424): exactly the target's sorry warning | `elab-WindowClock.out` |
| Order list | 176 modules (the same set as continuation 1's), 54 Mathlib roots | `order.txt`, `roots.txt` |
| Base sorries | 28 (continuation 1's set) | `base-sorries.txt` |
| Import probe | 100 checks: continuation 1's 60, then the six helpers' citations, the join, the record's per-field lemmas, the seam's lockstep lemmas and `Cfg.mapState` fields, silence, space. 0 errors, 0 warnings | `F3C2ImportProbe.*` |
| Consumer probe | continuation 1's `F3ConsumerProbe.lean.txt`, unchanged: 0 errors | `F3ConsumerProbe.out` |
| Join probe | gate 56's published version: exactly its two bare controls fail, the output identical to gate 56's record | `F3C2JoinProbe-published.out` |
| Route probe | sealed (12 other-file definitions), every prescribed step's premise from public lemmas: silence from an endpoint (`MultiTapeTM.output_prefix` at both ends, `List.IsPrefix.eq_of_length`); each field as a delimited word at its offset (`recordAt_iff`, `fieldsTape_field`, `fieldOffset_add_length_le`); the source rewind field by field (`fieldOffset_succ`; the end at `length_joinFields_add_one`); a word patched on a blank tape as a delimited word (F2's clock precondition); the clock rewind; the join of a pass's writes (`wordPatch_append`); the seam's head positions at every time (`seamCompTM_runFrom_left`, `_right`). Exactly one failure: the space control (below) | `F3C2RouteProbe.*` |
| Seal controls | the route probe's 12 sealed definitions: 12 `rfl` goals close unsealed and fail sealed | `F3C2RouteSealControl.*` |
| Screen base | 21 files (continuation 1's population): 1,049 declarations, 510 pairs; against continuation 1's after-screen, no pair new or gone (the one new declaration is `wordPatch_append`) | `screen-base.*` |
| Lint | `SpaceComplexity`: 0 FAIL, 81 WARN over 107 files; `WindowClock` none | `lint-spacecomplexity.txt` |

**Two route facts for the brief.**
- **The clock rewind.** After the last round, `cw_leftTM` leaves the clock head on the word's right
  delimiter, but `skipBackTM_run_ofCfg` needs the head one cell past it. The published route: a
  `skipTM` over the empty word (one step right; its premise is the blank delimiter), then
  `skipBackTM` over the word.
- **Silence** needs only each phase's endpoint: the output at any intermediate time lies between the
  output at `0` and at the endpoint (`MultiTapeTM.output_prefix`), and the framed rows' endpoints
  keep the output.

**The space clause: no published route.** `MultiTapeTM.spaceUsed` is defined as the sum of the
per-tape counts, with no equation; the per-tape bound `MultiTapeTM.spaceUsedByTape_le_card_Icc` is
public. The route probe's space control closes unsealed and fails with `spaceUsed` sealed. **Ruled
(user, 2026-10-22): an API PR first, with the equation and a radius lemma** (#149:
`MultiTapeTM.spaceUsed_eq_sum` in `Deterministic`, `MultiTapeTM.spaceUsed_le_of_abs_le` in
`Finite`). The brief issues after #149 merges. At issue: add the radius lemma to the import probe,
re-run everything against #149's replay snapshot, and fill the draft's placeholders.
