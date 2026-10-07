# Ch2 fill campaign — Epoch 1, Batch B: nondeterministic run calculus

## Context

You are filling Lean 4 proofs in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity* (2009), Chapter 2 (statement layer complete, four
audit gates closed — `audits/ch2-phase*`). This batch delivers the NDTM run
calculus: monotonicity of all-branch halting and of acceptance in the choice
word, the lockstep embedding of deterministic machines, `NTIME`
monotonicity, `DTIME ⊆ NTIME`, and the degenerate-budget emptiness lemma.
The six **proved** unfolding lemmas in `Nondeterministic.lean`
(`Turing.NDTM.runWith_nil`, `runWith_cons`, `runWith_append`,
`runWith_of_halt`, and the `stepWith` pair) are your toolkit — every sketch
below reduces to them plus list bookkeeping. No new machine is built.

## Repository, branch, deliverable

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`. Base: branch
  `complexity/arora-barak-ch1`, **not** `main`.
- Branch `fill/ch2-e1-B`. **Delivery by zip, not PR** (`workflow.md` §4):
  `fill-ch2-e1-B.zip` with `REPORT.md`, full modified sources, a
  `git format-patch` series against the base, a git bundle, the final sweep
  log, the axiom-print log, and `SHA256SUMS`.
- Read first: `policy.md`; `workflow.md` §4; `AroraBarakChapter2Plan.md` §4
  (you are batch 1B); `audits/ch2-phase2-findings.md` (the NDTM surface's
  audit — especially the prefix-shaped bounded reading of all-branch halting
  and the output-exactly-`[true]` acceptance convention).

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/TuringMachine/Nondeterministic.lean` (2 targets)
- `TCSlib/Complexity/ClassNP/NTIME.lean` (4 targets)

## Environment and verification

- Toolchain pinned (`lean-toolchain`, Lean 4 v4.25.0); setup:
  `lake exe cache get`. **Never run `lake build`.**
- Bootstrap once:
  `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`.
- Iterate per edit:
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Nondeterministic`
  (resp. `…/ClassNP/NTIME`), then every later module in the order list —
  `Nondeterministic` sits early, so budget time for the downstream re-checks.
- Final: full 53-module sweep, zero `error:` lines; axiom prints for each
  filled target, expected exactly `[propext, Classical.choice, Quot.sound]`
  (this batch has **no** out-of-batch sorried dependencies — any `sorryAx`
  is a defect).

## Ground rules (binding)

1. **File ownership.** Only the two owned files. Helpers `private`; shared
   wishes go under "Requested shared lemmas" in `REPORT.md` with a `private`
   copy locally. New declarations all listed (the audit blind-restates them).
2. **Statement freeze.** No renames, re-signatures, restatements, or
   attribution edits; docstring-sketch appendices allowed, flagged.
3. **Escalation** on any target that looks unprovable as stated: stop that
   item, record the obstruction, continue.
4. No touching sorries outside the target list. 5. Docstrings stay.
6. Precise imports; keep `set_option` headers.

## Targets (fill in this order)

1. **`MultiTapeTM.toNDTM_runWith`** (Nondeterministic.lean:228). Induction
   on `w` generalizing `cfg`. One step: `stepWith` on `toNDTM` and
   `MultiTapeTM.step` are the same match — halted branches identity, live
   state applies `tm.tr` since `toNDTM.tr b = tm.tr` definitionally for
   either `b`. Cons: `runWith_cons` against
   `MultiTapeTM.runFrom_succ_eq_step` (right side counts `|w| + 1` via
   `List.length_cons`). Mind which end the step peels from — align with the
   proved `runWith_cons` orientation before starting the induction.
2. **`HaltsWithin.mono`** (Nondeterministic.lean:183). Split
   `w = w.take t ++ w.drop t` (`List.take_append_drop`;
   `List.length_take_of_le`), run through `runWith_append`, absorb the tail
   with `runWith_of_halt`.
3. **`AcceptsWithin.mono`** (NTIME.lean:103). The dual padding direction:
   extend the accepting word by `List.replicate (t' - t) false`;
   `runWith_append` + `runWith_of_halt` preserve the halted state *and* the
   output `[true]` (acceptance is output-exactly-`[true]` — phase-2
   convention; do not weaken to "contains true").
4. **`NTIME.mono`** (NTIME.lean:139). Same machine, larger budget.
   All-branch halting by target 2. Acceptance forward by target 3; backward
   by truncation: `w.take (c * T₁ n)` has halted (all-branch halting at the
   smaller budget), so `runWith_append` on `take ++ drop` with
   `runWith_of_halt` shows the full run equals the truncated one.
5. **`DTIME_subset_NTIME`** (NTIME.lean:154). Via target 1 on
   `Turing.FinTM.toFinNDTM M`: every branch is `M`'s deterministic run, so
   all-branch halting is `M`'s halting (unfold `Turing.FinTM.DecidesInTime`
   through `computesInTime_iff`), and branch acceptance ↔ `M` outputs
   `[true]` ↔ `x ∈ L` by the indicator contract
   (`Turing.MultiTapeTM.indicator`); for `x ∉ L` every branch outputs
   `[false] ≠ [true]`.
6. **`NTIME_eq_empty_of_exists_zero`** (NTIME.lean:166). Instantiate the
   claimed decider at `List.replicate n false`; `HaltsWithin` at the empty
   choice word (`runWith_nil`) asserts the initial configuration is halted,
   contradicting `Turing.Cfg.init`'s state `some q₀`.

## Out-of-scope sorries you will see (leave untouched)

Everything in the other E1 batches (PolyTime/Reductions — 1A; CoNP/NP/EXP —
1C; `Formulas/` — 1D) and the whole E2–E4 surface, in particular all of
`Nondeterminism.lean` (the compilations are epoch 2/3, despite living next
door to your NTIME targets — note the file is `ClassNP/Nondeterminism.lean`,
distinct from your owned `TuringMachine/Nondeterministic.lean`).

## REPORT.md checklist

- [ ] Targets filled (6), one line each vs the sketch — note especially any
      orientation flip needed in target 1's induction.
- [ ] New declarations listed (public and private).
- [ ] Requested shared lemmas — or "none". Escalations — or "none".
- [ ] Final sweep log tail (zero `error:` lines) + axiom-print log (standard
      triple only).
- [ ] Diff touches only the two owned files.

## Known pitfalls at this pin

- After `cases hs : cfg.state`, insert `dsimp only` to iota-reduce
  `match some q with …` before rewriting, or use nested `split`.
- Avoid bare `simp` with folded forms (`initCfg` is `@[simp]`); prefer
  `simp only`.
- `List.length_take` returns `min`; use the `_of_le` form or `omega` after.
- `Function.update_of_ne` (not `update_noteq`); core `Nat.pow_pos`.
- `omega` cannot see `(⟨e, h⟩ : Fin _).val` — normalize first.
- Vendored API spellings: `MultiTapeTM.runFrom_succ_eq_step'` vs
  `runFrom_succ_eq_step` — check which end each peels; `Cfg.inputSymbol` is a
  double `dite`.
- Destructure `ComputesInTime` after
  `simp only [FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace]`.
