# Chapter-1/2 retrofit — Epoch R1, Batch RB1: dead code and the `emit_run` citation (`Build/Loop.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`** — this exact branch,
  NOT `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/retrofit-rb1`),
  record the base commit hash you branched from in `REPORT.md` (the brief
  was issued at `ff012d28ca3131452161669e1d7efe389b75ba2e`), and never
  rebase onto anything else.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `retrofit-rb1.zip` with `REPORT.md`, the full modified source file, a
  `git format-patch` series against your recorded base, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.
- Integration note (no action for you): the maintainer integrates retrofit
  deliveries on a side branch and opens a PR; this changes nothing about
  the delivery format above.

## What this is — read carefully, it differs from a fill batch

This is a **retrofit batch**: you are editing a fully proved, zero-sorry
file. The file must have **zero `sorry` and zero `error:` before and after
every commit you make**. There are no admissions to fill and none may be
introduced — a partial delivery means fewer tasks completed, never a
`sorry`. The authoritative task list below is extracted from the
commissioned inventory `audits/retrofit-inventory/loop.md` (in the repo;
read it for full context) and is **embedded here verbatim as the binding
contract**.

## Owned file (modify this and nothing else)

`TCSlib/Complexity/TuringMachine/Build/Loop.lean` (5,713 lines, 8 public
declarations, 214 privates, 0 sorries).

**Task 1 — delete the 8 dead private declarations** (commit 1):

| Declaration | Defined at (line, at the recorded base) |
|---|---|
| `loop_silent_prefix` | 193 |
| `loopDebitTM` | 443 |
| `loopDebitCfg` | 459 |
| `loopBorrow_step` | 466 |
| `loopBorrow_run` | 492 |
| `loopBorrow_rewind` | 517 |
| `loopBorrow_correct` | 551 |
| `loopBody_capture` | 697 |

Inventory evidence (binding): the six `loopDebit*`/`loopBorrow*` members
(the standalone one-tape debit machine, lines 439–563 — its own docstring
says it "privately re-derives the counter template") refer only to each
other; `loop_silent_prefix` and `loopBody_capture` have no referrers at
all; the host performs its borrow itself (`loopHost_borrow*`). Delete each
declaration together with its docstring. **Also fix the historical
docstring sentence at line 2205** that mentions `loopBorrow_correct` —
rewrite that one sentence so it no longer references a deleted name;
change nothing else in that docstring.

**Deletion protocol**: the compile is the deadness proof. If removing any
of the eight breaks the check, **restore that declaration, record the
escalation in `REPORT.md` (which referencer the inventory missed), and
continue with the rest** — never "fix" a breakage by editing other code.

**Task 2 — replace the H4 family with the now-proved public lemma**
(commit 2). The three privates

| Declaration | Line |
|---|---|
| `emLoopForwardCfg` | 5185 |
| `emLoop_forward_apply` | 5192 |
| `emLoop_forward_run` | 5210 |

(lines 5183–5240, ≈56 lines) re-derive a forwarding lockstep; the
docstring at 5206 says it was "proved locally so this batch does not
depend on the concurrent `Turing.emit_run` admission". That admission is
gone: **`Turing.emit_run` (`Build/Wrappers.lean:273`) is proved** (the
file is zero-sorry). Replace the family with a derivation from the public
`Turing.emit_run` plus `leftCfg_run` (`Simulation.lean`). The inventory's
verified glue sketch (binding as the proof plan; adapt as the kernel
requires):

> a padded source `P.tr = leftAction 1 id (loopBodySource.tr …)`;
> `emitAction ∘ leftAction 1 id = leftAction 1 id ∘ emitAction` (closes by
> `simp` with `Option.map_id`); one `Cfg.ext` showing
> `emitCfg ∘ leftCfg = leftCfg ∘ emitCfg`; the liveness guard comes from
> `leftCfg_run`. About 15–25 lines replacing 56.

Update the sole consumer `emLoopHost_body_forward` (line 5275) to cite the
replacement (ideally it becomes a direct `emit_run` citation). If the
replacement does not land within budget, deliver Task 1 alone and record
the frontier — Task 1 is independent.

## Binding ground rules

1. **Public-surface freeze.** The 8 public declarations (`Turing.stateWord`,
   `Turing.loop_run`, `Turing.FinTM.exists_loopCfgTM`, `exists_loopTM`,
   `exists_loopFindTM`, `exists_emitLoopTM`, `exists_installCallTM`,
   `exists_emitCallTM`) stay **byte-identical** — signatures, statements,
   docstrings, and proof bodies. Only the privates named above change.
2. **No new private declarations** except what Task 2's replacement
   strictly needs (list every one in `REPORT.md`), and **zero new copies
   of existing proved material** — `policy.md` **Duplication** is binding:
   your `REPORT.md` must contain a duplication-ledger line (expected:
   "new copies: none").
3. **No renames, no re-signatures, no import changes** (`emit_run` and
   `leftCfg_run` are already in the import closure via Wrappers and
   Composition/Simulation).
4. Escalation on anything unprovable or unexpectedly live: stop that task,
   record the obstruction, deliver what stands.
5. Docstrings stay except the two named edits (line 2205; H4's removal).

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned.
  Setup once: `lake exe cache get`. **Never run `lake build`.**
- Bootstrap once:
  `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  (65 modules), then
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Build/Catalog`.
- Iterate on your file per edit:
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Build/Loop`.
- Final, in order: your file, then
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Build/Catalog`
  (the big direct importer), then
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine`
  (the facade) — each with **zero `error:` lines and zero `sorry`
  warnings**, fresh `.olean`s.
- **Axiom prints**: `#print axioms` for all 8 public declarations on the
  final fresh tree; each footprint **at most**
  `[propext, Classical.choice, Quot.sound]` and unchanged from the base;
  no `sorryAx`.
- Style lint: `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`
  — 0 FAIL (the pre-existing size WARNs remain).

## REPORT.md checklist

- [ ] Base commit hash; working branch name.
- [ ] Deletions: all 8 (or the escalated subset, each with its found
      referencer); the line-2205 docstring sentence as rewritten.
- [ ] Task 2: the replacement derivation (new private helpers listed, with
      roles), `emLoopHost_body_forward`'s new form, net line delta — or
      the recorded frontier if not attempted/landed.
- [ ] Duplication ledger: "new copies: none" (or the disclosure, which
      requires maintainer approval before integration).
- [ ] Line count before/after; expected ≈ 5,513–5,523 after both tasks.
- [ ] Final sweep log tail (Loop + Catalog + facade, 0 errors / 0 sorries)
      + 8 axiom prints.
- [ ] Diff touches only `Build/Loop.lean`.

## Known pitfalls at this pin (hard-won)

- `Function.update_of_ne` (not `update_noteq`); after
  `cases hs : cfg.state`, `dsimp only` before rewriting; avoid bare `simp`
  with folded forms; `omega` needs beta-reduced goals.
- `Cfg` equality: `cases`-and-`rfl` or field congruence; beware eta.
- `emit_run`'s hypothesis is an *agreement* form (`hagree`-style): any
  host whose embedded actions are the emit-wrapped actions follows the
  trajectory — instantiate it at the padded source, do not specialize it
  away.
- Deleting a declaration with a preceding `/-- … -/` docstring: remove the
  docstring too, or the orphaned docstring attaches to the next
  declaration and changes its (frozen) text.
