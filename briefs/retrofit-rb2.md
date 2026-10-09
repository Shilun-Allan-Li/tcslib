# Chapter-1/2 retrofit — Epoch R1, Batch RB2: the dead emitter batch, Encoding swaps, and the splitSolve subsumption (`Build/Primitives.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`** — this exact branch,
  NOT `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/retrofit-rb2`),
  record the base commit hash you branched from in `REPORT.md` (the brief
  was issued at `ff012d28ca3131452161669e1d7efe389b75ba2e`), and never
  rebase onto anything else.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `retrofit-rb2.zip` with `REPORT.md`, the full modified source file, a
  `git format-patch` series against your recorded base, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.
- Integration note (no action for you): the maintainer integrates retrofit
  deliveries on a side branch and opens a PR; this changes nothing about
  the delivery format above.

## What this is — read carefully, it differs from a fill batch

This is a **retrofit batch** on a fully proved file: **zero `sorry` and
zero `error:` before and after every commit**. No admissions exist and
none may be introduced — a partial delivery means fewer tasks completed,
never a `sorry`. The task list is extracted from the commissioned
inventory `audits/retrofit-inventory/primitives.md` (read it for full
context) and embedded here verbatim as the binding contract.

## Owned file (modify this and nothing else)

`TCSlib/Complexity/TuringMachine/Build/Primitives.lean` (7,636 lines,
18 public declarations, 318 privates, 0 sorries).

**Task 1 — delete the 62 dead private declarations** (commit 1). The
superseded earlier emitter batch (59) plus three split-search orphans.
Complete list (binding; delete each with its docstring):

- *F24a eval (6):* `emitterIdleTM`, `emitterEvalTM`, `emitterEvalCfg`,
  `emitter_eval_run`, `emitter_eval_initial`, `emitter_eval_first`.
- *F24b clear (13):* `emitterInterval`, `emitterCleared`,
  `emitter_cleared_step`, `emitterClearTM`, `emitterClearCfg`,
  `emitter_clear_left`, `emitter_cleared_zero`, `emitter_cleared_all`,
  `emitter_clear_scan`, `emitter_origin_erase`, `emitter_clear_origin`,
  `emitter_clear_run`, `emitter_clear_first`.
- *F24c track (18):* `emitterSpan`, `emitter_span_extend`, `emitterSlots`,
  `emitterTrackTM`, `emitterTrackCfg`, `emitterTrackMid`,
  `emitter_track_action`, `emitter_track_stamp`, `emitterLo`, `emitterHi`,
  `emitter_track_extent`, `emitter_track_support`, `emitter_span_zero`,
  `emitter_track_initial`, `emitter_track_run`, `emitter_track_computes`,
  `emitter_span_interval`, `emitter_track_clearable`.
- *F24d bank (11):* `emitterBankSymbols`, `emitterBankPart`,
  `emitterBankTM`, `emitterBankCfg`, `emitterBank_part`,
  `emitterBank_step`, `emitterBank_run`, `emitterClear_fixed`,
  `emitterBank_clear`, `emitterBank_fixed`, `emitterBank_first`.
- *F24e right (9):* `emitterRightTM`, `emitterRightCfg`,
  `emitter_right_step`, `emitter_right_run`, `emitterRightScan`,
  `emitter_right_scan`, `emitter_right_finish`, `emitter_right_endpoint`,
  `emitter_right_computes`.
- *F24f eval closers (2):* `emitter_prepared_eval_first`,
  `emitter_width_eval_first`.
- *Split orphans (3):* `splitFind_none`, `splitCount_firstHalt`,
  `splitPrepare_first`.

Inventory evidence (binding): none of the 62 is referenced from outside
the set; the only external mentions are docstrings (`Embed.lean` and
`CookLevin/Hardness.lean` — those files are NOT yours to touch and their
docstring mentions are harmless history). **Deletion protocol**: the
compile is the deadness proof. If removing any one breaks the check,
restore it, record the escalation (the found referencer) in `REPORT.md`,
and continue with the rest.

**Task 2 — the two Encoding swaps** (commit 2). Two privates are exact
duplicates of public lemmas already inside this file's import closure:

| Delete | Re-point its uses to |
|---|---|
| `catalogPair_inverse` | `Turing.eq_pairEncode_of_pairDecode` (`Encoding.lean:231`) |
| `catalogPair_length` | `Turing.length_pairEncode` (`Encoding.lean:192`) |

**Task 3 — comment-only cleanups** (same commit as Task 2): the module
docstring block at **L67–110** carries a stale "admitted" status (the file
is zero-sorry); the section blocks at **L4419–4439** and **L5956–5959**
describe the now-deleted families. Rewrite each minimally to the current
truth; touch no other comment.

**Task 4 (OPTIONAL STRETCH — attempt only after Tasks 1–3 are delivered-
ready; a delivery without it is complete)** — the splitSolve subsumption
(commit 3). `computesFunInTime_splitSolve` (line 4393) follows from
`computesFunInTime_splitSolveWith` (line 7399) plus
`computesFunInTime_polyBits`, because `solveSplitWith (fun i => C*(i+1)^e)`
unfolds to `solveSplit C e` **by definition** (`Convention.lean:125-133`).
The only mathematical work is the bound
`c*(n+1)*(b*(n+2)^(e+1)+n+2) ≤ K*(n+1)^(e+2)`. Rewrite the **proof body
only** of `computesFunInTime_splitSolve` (its statement, docstring, and
signature stay byte-identical — this is the single sanctioned public-body
change of this batch), then delete every private this frees and that the
compile confirms dead: the expected set is families F16–F18, F20, F22 and
parts of F13 of the inventory (≈35 further declarations beyond the three
orphans of Task 1, ≈870 lines) — enumerate the actual deleted set in
`REPORT.md`.

**Explicitly OUT OF SCOPE (do not touch, recorded decision):** the
`emitterCompare*` family (F25a) and the `emitterP2Erase*` family (F27a) —
their catalog replacement is deferred to the 12.2c window because it
requires a `Build/Catalog` import this file must not gain now. **Do not
add any import**, in particular not `Build.Catalog`.

## Binding ground rules

1. **Public-surface freeze.** All 18 public `computesFunInTime_*` rows stay
   byte-identical in signature, statement, and docstring; proof bodies stay
   byte-identical except `computesFunInTime_splitSolve` under Task 4.
2. **No new private declarations** except what Task 4 strictly needs (list
   each), and **zero new copies of existing proved material** —
   `policy.md` **Duplication** is binding; `REPORT.md` carries a
   duplication-ledger line (expected: "new copies: none").
3. **No renames, no re-signatures, no import changes.**
4. Escalation on anything unexpectedly live or unprovable: stop that item,
   record it, deliver what stands.
5. Docstrings stay except the named Task 3 blocks and deleted
   declarations' own docstrings.

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned.
  Setup once: `lake exe cache get`. **Never run `lake build`.**
- Bootstrap once:
  `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  (65 modules).
- Iterate on your file per edit:
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Build/Primitives`.
- Final, in order: your file, then
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine` (the
  facade) — zero `error:` lines, zero `sorry` warnings, fresh `.olean`s.
- **Axiom prints**: `#print axioms` for all 18 public rows on the final
  fresh tree; each footprint **at most**
  `[propext, Classical.choice, Quot.sound]` and unchanged; no `sorryAx`.
- Style lint: `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`
  — 0 FAIL.

## REPORT.md checklist

- [ ] Base commit hash; working branch name.
- [ ] Task 1: deletions confirmed 62/62 (or the escalated subset with
      referencer evidence).
- [ ] Task 2: both swaps with the re-pointed use sites listed.
- [ ] Task 3: the three comment blocks as rewritten.
- [ ] Task 4: done/not attempted/frontier; if done — the new proof route,
      the bound's constant `K`, the enumerated freed-and-deleted set, and
      confirmation the statement is byte-identical.
- [ ] Duplication ledger: "new copies: none".
- [ ] Line count before/after (expected ≈ 6,350 after Tasks 1–3; ≈ 5,480
      with Task 4).
- [ ] Final sweep log tail + 18 axiom prints.
- [ ] Diff touches only `Build/Primitives.lean`.

## Known pitfalls at this pin (hard-won)

- Deleting a declaration with a preceding `/-- … -/` docstring: remove the
  docstring too, or it attaches to the next declaration and silently
  changes frozen text.
- The Task 4 unfolding is definitional at `Convention.lean:125-133` —
  `show`/`change` to the `solveSplitWith` form rather than `simp`-unfolding
  `solveSplit` (bare `simp` with folded forms thrashes at this pin).
- `omega` needs beta-reduced, non-`Fin`-projection goals; for the Task 4
  bound prefer `calc` with `Nat.pow_le_pow_left/right` and explicit
  monotonicity over `nlinarith`.
- `Function.update_of_ne` (not `update_noteq`).
- The six private `instance`s in this file are live through `FinTM`'s
  `[Fintype]`/`[DecidableEq]` fields despite having no textual references
  — they are NOT dead; none is on the deletion list, leave them.
