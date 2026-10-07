# Ch2 fill campaign — Epoch 3, Batch C: snapshot locality

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e3-C`). The
  required base is `b55180a8bb38b94427e75e63630aa6eab5fd6e95`; record it in
  `REPORT.md` and never rebase onto anything else.
- **Delivery is by zip, not PR or push**: `fill-ch2-e3-C.zip`, **flat**
  (`SHA256SUMS` at the root), with `REPORT.md`, the full modified source,
  the `git format-patch` series, a git bundle, the final sweep log, the
  axiom-print log, and `SHA256SUMS`.

## Context

Epochs 1 and 2 are complete and audited (38/59 proved;
`audits/ch2-epoch2-resolutions.md`). Your batch is the **snapshot locality
layer** [AB09, eq. (2.3) with footnote 6] — the five lemmas everything in
the Cook-Levin summit (E4) consumes. Unlike most of the campaign, this is
**run-calculus mathematics, not machine construction**: no new machines,
no budgets — exact statements about `runFrom`, the oblivious schedule, and
cell histories. The oblivious machinery (`Turing.FinTM.Oblivious`,
`Robustness/Oblivious*.lean`) is proved Chapter-1 material; the snapshot
vocabulary (`Snapshot`, `snapshotAt`, `inputPosAt`/`workPosAt`,
`prevVisit`, `stepState`/`writtenOrKept`/`emitted`, `inputBitAt`) is
defined, audited, and frozen in your own file.

## Owned file and targets (in order)

- `TCSlib/Complexity/CookLevin/Snapshot.lean` — targets:
  1. `oblivious_schedule_eq` (4 pts): instantiate `M.Oblivious` at `x` and
     `List.replicate x.length false` (`List.length_replicate` equalizes);
     the two conjuncts are the two claims; function equality on work
     positions specializes at `τ`.
  2. `snapshotAt_zero` (2 pts): `runFrom_zero` + `Cfg.init`; position `1`
     reads `x[0]` or the boundary blank, which is `inputBitAt x 1` in both
     cases.
  3. `snapshotAt_state_succ` (3 pts): `runFrom_succ_eq_step'` + the halted
     and live branches of `step` against `stepState`.
  4. `snapshotAt_inputSymbol` (4 pts): `Cfg.inputSymbol`'s boundary/interior
     case split equals `inputBitAt` at every position `p ≤ |x| + 1`
     (positions live in `Fin (|x| + 2)`); rewrite by target 1.
  5. `snapshotAt_workSymbol` (9 pts): the last-visit reconstruction — the
     cell recurrence, the maximal-earlier-visit argument over
     `prevVisit`'s filtered `List.max?`, the never-visited blank case,
     with halting needing no separate case.

## Environment and verification

- Pinned toolchain (Lean 4.25.0, `cdd38ac5115b`; mathlib `029db123ddaa`).
  Setup once: `lake exe cache get`. **Never run `lake build`.**
- Bootstrap the **57-module** order
  (`scripts/ab_ch1_module_order.txt` via `scripts/lean_check_tree.sh`);
  iterate the owned module plus later modules; final full fresh sweep,
  zero `error:` lines.
- **Axiom prints**: all five targets at most
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx` — **zero
  sanctioned admitted dependencies**. Kernel-traversal template:
  `audits/programs/ch2-e2-ClosureAxioms.lean`.

## Ground rules (binding)

1. **File ownership.** Only `Snapshot.lean`; only the five targets plus
   `private` helpers; list every new declaration.
2. **Statement freeze** absolute (the definitions above are audited and
   frozen too); escalation over alteration, always.
3. Docstrings stay (append-only, flagged). Precise imports; keep
   `set_option` headers.
4. **Budget** (22 points): if exhausted, deliver a partial flat zip;
   `REPORT.md` states proved/admitted/frontier exactly (admissions allowed
   **only** in a partial delivery, each listed). Targets 1–4 are expected
   to land well within budget; the mass is target 5.

## Inherited audit contract (verbatim; binding on the fill)

From `audits/ch2-phase4-findings.md`, finding 4 (via the phase-4
resolutions):

> The schedule and last-visit reconstruction are valid with optional
> writes, first visits, and absorption. Derivation A establishes the cell
> recurrence, maximum-visit facts, and both branches. An outer `none`
> preserves the cell; `some none` erases it. No common halting time,
> positive tape count, or positive input length is needed. No statement
> repair. **Preserve the strict `s < t` bound and the distinction between
> no write and writing blank in the fill.**

And from Derivation A itself (`audits/ch2-phase4-findings.md`, the
locality derivation — **read it in full before starting target 5**; it is
the audited proof plan, including the cell recurrence (1) and the
exhaustive written-value table):

> | Source state/action | Value left at the old head |
> |---|---|
> | Halted | `w_t(p_t)` |
> | Live, outer write option `none` | `w_t(p_t)` |
> | Live, write `some none` | Blank, even if the old cell was nonblank |
> | Live, write `some (some b)` | `some b` |
>
> Thus (1) also applies to the halting transition itself, including a
> simultaneous write and move. **It must not be replaced by a rule that
> ignores the action whose successor state is `none`.**

Your `REPORT.md` must map the recurrence, both `prevVisit` branches, and
the halting-transition clause to your discharging lemmas.

## Out-of-scope sorries you will see (leave untouched)

The padding cluster and `EXP_subset_NEXP` (3A, concurrent); `SAT.lean`
(3B); `Tautology.lean` (3D and 4B); everything in `CookLevin/Hardness.lean`
(E4 — it consumes your targets; do not touch it). On completion
`Snapshot.lean` is admission-free.

## REPORT.md checklist

- [ ] All five targets filled (or the frontier exact); the Derivation-A
      mapping (recurrence, both branches, halting clause, strict `s < t`,
      `some none` vs `none`).
- [ ] Base hash; new privates listed; final file size.
- [ ] Axiom prints (standard triple at most, roots empty); final sweep log
      tail; diff touches only `Snapshot.lean`; archive flat.
- [ ] Requested shared lemmas / escalations — or "none".

## Known pitfalls at this pin (hard-won)

- `Action.apply` updates tape `τ` at the old head position only
  (`Function.update`), **before** the position changes; `Function.update_of_ne`
  (not `update_noteq`) for untouched cells.
- `Cfg.inputSymbol` is a double `dite`; `moveInputPos` clamps at both
  boundaries; positions are `Fin (n + 2)` — avoid `omega` on raw `Fin`
  projections (beta-reduce and `Fin.val` first).
- `runFrom_succ_eq_step'`/`…_step` peel opposite ends; halted
  configurations are fixed points of `step` — the frozen-run argument for
  later times in target 5's docstring uses exactly this.
- `prevVisit`'s `List.max?` over a filtered range: membership and
  maximality come from `List.max?_mem`-style reasoning plus the filter
  predicate; keep the bound **strictly** `s < t` as the contract requires.
- `D6`'s `Turing.MultiTapeTM.timed_input_bound` (public, run calculus) is
  available if a head-displacement bound helps; the Chapter-1
  `Robustness/Oblivious*` files hold the schedule infrastructure — consume
  public statements only.
