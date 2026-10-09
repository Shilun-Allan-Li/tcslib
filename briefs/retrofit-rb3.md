# Chapter-1/2 retrofit — Epoch R1, Batch RB3: dead clusters, three strict swaps, and the `clFresh` seam citation (`CookLevin/Hardness.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`** — this exact branch,
  NOT `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/retrofit-rb3`),
  record the base commit hash you branched from in `REPORT.md` (the brief
  was issued at `ff012d28ca3131452161669e1d7efe389b75ba2e`), and never
  rebase onto anything else.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `retrofit-rb3.zip` with `REPORT.md`, the full modified source file, a
  `git format-patch` series against your recorded base, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.
- Integration note (no action for you): the maintainer integrates retrofit
  deliveries on a side branch and opens a PR; this changes nothing about
  the delivery format above.

## What this is — read carefully, it differs from a fill batch

This is a **retrofit batch** on the campaign's largest fully proved file:
**zero `sorry` and zero `error:` before and after every commit**. No
admissions exist and none may be introduced — a partial delivery means
fewer tasks completed, never a `sorry`. The task list is extracted from
the commissioned inventory `audits/retrofit-inventory/hardness.md` (read
it for full context) and embedded here verbatim as the binding contract.

## Owned file (modify this and nothing else)

`TCSlib/Complexity/CookLevin/Hardness.lean` (8,904 lines; public surface =
`NPHard.polyTimeReducible`, `SAT_NPHard`, `SAT_NPComplete`, `SAT3_NPHard`,
`SAT3_NPComplete`; 553 privates, 0 sorries).

**Task 1 — delete the 6 dead private declarations** (commit 1):

| Declaration | Line | Inventory evidence |
|---|---|---|
| `clRefClockTM` | 899 | referenced only inside `clRefClockCfg` |
| `clRefClockCfg` | 914 | no referencers |
| `clCount_first` | 1151 | only inside `clRefCount_first` |
| `clRefCountTM` | 1188 | only inside `clRefCount_first` |
| `clRefCount_first` | 1205 | no code referencers; one docstring mention at 1242 |
| `clReadFields` | 3133 | only its own recursion |

Three closed clusters; nothing any public theorem reaches cites any of
them. **Also fix the `clCount_width` docstring at lines 1241–1243**, which
mentions `clRefCount_first` — rewrite that sentence to drop the deleted
name; change nothing else. **Deletion protocol**: the compile is the
deadness proof; if a removal breaks the check, restore it, record the
escalation (the found referencer) in `REPORT.md`, and continue.

**Task 2 — three strict swaps** (commit 2). Each private duplicates a
public fact already in this file's import closure; delete the private and
re-point its uses:

| Delete | Replacement | Use sites |
|---|---|---|
| `clCompute_comp` (4887–4901) | `FinTM.bufferedCompTM_computesInTime` (`Composition.lean:355`) + `output_length_le` + monotonicity | 5160, 5314 |
| `clBuffer_append_bit` (1711) | `(FinTM.bufferTape_append w b).symm` | 1757 |
| `clA5_pt_unaryLength` (6896) | `clNative_fill true` (this file's own private wrapper, line 693 region) | 10 sites — enumerate them in `REPORT.md` |

**Task 3 — the `clFresh` seam citation** (commit 3). The family `clFreshTM`
(3513), `clFresh_run`, `clFresh_idle`, `clFresh_first` (through 3584)
hand-builds exactly the §12 seam composite. Inventory finding (binding as
the proof plan):

> `clFreshTM` already has `seamCompTM`'s shape, up to unfolding: state
> `Fin 3 ⊕ clReadTM.State`, dispatch
> `FinTM.controlAction 0 (some (.inr entry))`, left branch
> `Action.mapState Sum.inl`. Hardness's `.mapState Sum.inl` /
> `.mapState Sum.inr` seams match the R2′ `seamCompTM_run_ofCfg` statement
> exactly. The stream head is displaced, which the general-configuration
> variant handles. No glue is needed. `clFresh_idle` / `clFresh_first`
> stay, because `clRead_run` has no first-return cut.

Redefine `clFreshTM` as the `seamCompTM` instance and re-prove
`clFresh_run` by citing `seamCompTM_run_ofCfg`
(`Build/Seam.lean` — the general-configuration trio). This **requires one
new import**: add
`import TCSlib.Complexity.TuringMachine.Build.Seam` to the header — this
is the single sanctioned import change of this batch, flag it prominently
in `REPORT.md` (Hardness becomes the first §12-layer consumer outside
`Build/`). If the citation does not land cleanly (e.g. a state-type
mismatch the inventory missed), escalate and deliver Tasks 1–2 — they are
independent.

## Binding ground rules

1. **Public-surface freeze.** The five public theorems stay byte-identical
   — signatures, statements, docstrings, and proof bodies.
2. **No new private declarations** except what Task 3 strictly needs (list
   each), and **zero new copies of existing proved material** —
   `policy.md` **Duplication** is binding; `REPORT.md` carries a
   duplication-ledger line (expected: "new copies: none").
3. **No renames, no re-signatures**; the one sanctioned import change is
   Task 3's `Build.Seam`.
4. Escalation on anything unexpectedly live or unprovable: stop that item,
   record it, deliver what stands.
5. Docstrings stay except the named 1241–1243 edit and deleted
   declarations' own docstrings.

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned.
  Setup once: `lake exe cache get`. **Never run `lake build`.**
- Bootstrap once:
  `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  (65 modules — Hardness is module 51; everything before it must be fresh).
  Then `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Build/Seam`
  (Task 3's import; it may not be in the order list — check it before
  first use).
- Iterate on your file per edit:
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/CookLevin/Hardness`.
- Final, in order: your file, then
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/CookLevin` (the
  facade) — zero `error:` lines, zero `sorry` warnings, fresh `.olean`s.
- **Axiom prints**: `#print axioms` for the five public theorems on the
  final fresh tree; each footprint **at most**
  `[propext, Classical.choice, Quot.sound]` and unchanged; no `sorryAx`.
- Style lint: `python3 scripts/campaign_style_lint.py TCSlib/Complexity/CookLevin`
  — 0 FAIL (the file-size WARN remains and is justified by the recorded
  retrofit/12.2c program).

## REPORT.md checklist

- [ ] Base commit hash; working branch name.
- [ ] Task 1: 6/6 deletions (or the escalated subset with referencer
      evidence); the 1241–1243 docstring as rewritten.
- [ ] Task 2: the three swaps with every re-pointed use site enumerated
      (the `clA5_pt_unaryLength` ten).
- [ ] Task 3: done/escalated; the new `clFreshTM` definition, the
      `seamCompTM_run_ofCfg` citation, the flagged `Build.Seam` import —
      or the recorded obstruction.
- [ ] Duplication ledger: "new copies: none".
- [ ] Line count before/after (expected ≈ 8,710 after all three tasks).
- [ ] Final sweep log tail (Hardness + CookLevin facade) + 5 axiom prints.
- [ ] Diff touches only `CookLevin/Hardness.lean`.

## Known pitfalls at this pin (hard-won)

- `seamCompTM`'s dispatch branch matches on `Sum.inl s` with
  `if s = exit`: after `cases`, `dsimp only` then `split` — the
  `DecidableEq` instance is a binder, don't `decide`.
- The general `_ofCfg` seam trio starts phase two from phase one's
  returned configuration with only the control state replaced
  (`Cfg.mapState`); `(Cfg.ofWords q w).mapState f = Cfg.ofWords (f q) w`
  is definitional-or-near.
- Deleting a declaration with a preceding `/-- … -/` docstring: remove the
  docstring too, or it attaches to the next declaration and silently
  changes frozen text.
- `Function.update_of_ne` (not `update_noteq`); after
  `cases hs : cfg.state`, `dsimp only` before rewriting; avoid bare `simp`
  with folded forms; `omega` needs beta-reduced goals.
- This file's five publics live in namespace `Complexity` — print axioms
  with the names exactly as the file declares them.
