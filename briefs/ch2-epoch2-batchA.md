# Ch2 fill campaign — Epoch 2, Batch A: the `NP ⊆ EXP` enumerator

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e2-A`), record
  the base commit hash you branched from in `REPORT.md`, and never rebase
  onto anything else.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-ch2-e2-A.zip` with `REPORT.md`, the full modified source file, a
  `git format-patch` series against your recorded base, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context

You are filling one proof in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity* (2009), Chapter 2. Statement layer audited across
four closed gates; epoch 1 filled 27 of 59 admissions and closed its gate in
one round (`audits/ch2-epoch1-resolutions.md`). This batch is one target —
the **brute-force certificate enumerator**, [AB09, Claim 2.4] — and it is one
of the chapter's two biggest technique risks: a looping machine that lays out
candidate certificates, simulates a verifier call per round with captured
output, resets, and increments, under a timed loop invariant. The in-file
proof sketch (the audited route) names every machine obligation; the audit
record below completes the contract list. In-repo precedents, all proved:
`Turing.universalCaptureTM` (`UniversalStartup.lean` — capture/suppress/
redirect), the `Simulation.lean` lockstep gadgets, `Composition.lean`'s
buffered timed composition, and epoch 1's budget-arithmetic patterns.

## Owned file (modify this and nothing else)

- `TCSlib/Complexity/ClassNP/EXP.lean` — target: `NP_subset_EXP` (line 123).
  `P_subset_EXP` and `EXP_subset_NEXP` in the same file are **not yours**
  (the former is filled; the latter is epoch 3).

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned.
  Setup once: `lake exe cache get` (narrowing to the order list's Mathlib
  roots is fine — the epoch-1 reports' pattern). **Never run `lake build`.**
- Bootstrap once:
  `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  (53 modules).
- Iterate: `bash scripts/lean_check_tree.sh TCSlib/Complexity/ClassNP/EXP`
  per edit, then every later module in the order list. Final: the full
  53-module sweep, **zero `error:` lines**.
- **Axiom prints**: `#print axioms Complexity.NP_subset_EXP` on the final
  fresh tree; the footprint must be **at most**
  `[propext, Classical.choice, Quot.sound]` — proper subsets are fine
  (epoch-1 disposition D1) — and `sorryAx` must not appear: this batch has
  **no sanctioned admitted dependency**.

## Ground rules (binding)

1. **File ownership.** Only `EXP.lean`, and only the one target's proof plus
   `private` helpers. Shared wishes go under "Requested shared lemmas" in
   `REPORT.md` with a `private` local copy. List every new declaration — the
   epoch audit blind-restates them.
2. **Statement freeze.** No renames, re-signatures, restatements, or
   attribution edits anywhere. Docstring sketch appendices allowed, flagged.
3. **Escalation** on anything unprovable as stated: stop, record the
   obstruction, deliver what exists.
4. No touching sorries outside the target. 5. Docstrings stay.
6. Precise imports; keep `set_option` headers.
7. **Continuation budget**: this is a 12-point target. If your budget
   exhausts, deliver a partial zip whose `REPORT.md` states exactly which
   obligations are proved, which are stated `private` with `sorry` (allowed
   **only** in a partial delivery, each listed), and where the frontier is —
   the maintainer issues a continuation brief (the chapter-1 `universal` B2
   precedent).

## The audited route

The docstring sketch at `EXP.lean:123` is binding: evaluate the explicit
width `Q n = C(n+1)^c`; all-`false` initial candidate; per round assemble
`x ++ u`, run the verifier **captured**, test the bit, reset, increment as a
fixed-width counter; reject on overflow after the `2^(Q n)`-th round;
enumeration over **exactly** the definition's length. The private
`counterInc` layer of `ClassP/TimeConstructible.lean` is a **template, not a
citable API** — re-derive privately what you need (phase-1 finding 5).
The budget shape to land: `a · 2^(Q n) · (n + Q n + 1)^d ≤ 2^(n^e)` for a
fixed `e`, small lengths absorbed into `DTIME`'s constant.

## Inherited audit contract (verbatim; binding on the fill)

From `audits/ch2-phase1-round3-findings.md` (via
`audits/ch2-phase1-resolutions.md`):

> **Enumerator: completeness of the repaired obligation list.** I found no
> further unnamed substantive construction obligation at this sketch's
> level. A fill agent will need auxiliary lemmas, but they fall under the
> named contracts:
>
> | Named obligation | Contract needed in the fill |
> |---|---|
> | Width evaluation and initialization | Compute `Q(n)`, retain `x`, and construct the initial all-false candidate of exactly that width. Initialization has polynomial cost. |
> | Fixed-width increment and overflow | Visit every width-`Q(n)` word once until acceptance or exhaustion; preserve width, and terminate after the final rejection. For width zero, process the unique empty word before reporting exhaustion. |
> | Buffering, retention, and verifier-call simulation | Present exactly `x++u` as the simulated read-only input with correct initial head/boundary behavior, while protecting the retained instance and candidate. |
> | Capture and return | Suppress every physical verifier emission; capture its bit, including an emission on the halting transition; return control instead of halting the enumerator. Test the updated captured bit. Emit exactly one final answer. |
> | Restart | Restore verifier control, simulated heads, work tapes, and captured bit. Clear the bounded visited region and restore buffer/head bookkeeping within a polynomial budget. |
> | Timed loop invariant | Combine candidate coverage, correct calls, empty real output before finalization, and polynomial call/reset cost into termination, the singleton-output decision contract, and the stated exponential budget. |
>
> The precedent is real: `UniversalStartup.lean:405`, `universalCaptureTM`,
> sets physical emission to `none` while storing the source emission, and
> turns a source halt into a live administrative state before transfer. In
> particular, the halting action's output is captured before transfer. That
> wrapper stores output on a tape and transfers to its particular
> interpreter; the enumerator must implement the named finite-control-bit
> variant and restart behavior. The repaired sketch correctly calls it a
> **pattern**, rather than claiming it supplies the whole loop.
>
> The two-round adversarial trace now behaves correctly: a rejected first
> candidate contributes no physical `[false]`; an accepted second candidate
> still contributes no physical verifier output; finalization emits only
> `[true]`. If all candidates reject, finalization emits only `[false]`.
> Capturing first and then examining the simulated halt covers a decider
> that emits its only bit on its last transition.

Your `REPORT.md` must map each of the six contract rows to the lemma(s)
discharging it.

## Out-of-scope sorries you will see (leave untouched)

`EXP_subset_NEXP` (your own file — epoch 3); `mem_NP_iff_exists_length_le`,
`HALT_NPHard`, `HALT_not_mem_NP` (2C, concurrent); the `Nondeterminism.lean`
compilations (2B); the `TMSAT.lean` four (2D); everything in E3/E4
(`SAT.lean`, `Tautology.lean`, `CookLevin/*`).

## REPORT.md checklist

- [ ] Target filled; the six-contract mapping table.
- [ ] Base commit hash recorded; new declarations listed (public: none
      expected; privates all).
- [ ] Requested shared lemmas — or "none". Escalations — or "none".
- [ ] Final sweep log tail (zero `error:` lines) + axiom print (at most the
      standard triple; no `sorryAx`).
- [ ] Diff touches only `EXP.lean`.

## Known pitfalls at this pin (hard-won)

- `Function.update_of_ne` (not `update_noteq`); core `Nat.pow_pos`;
  `dite_eq_right`/`dite_eq_left` don't exist (`split <;> simp <;> omega`).
- After `cases hs : cfg.state`, `dsimp only` before rewriting.
- Avoid bare `simp` with folded forms (`initCfg` is `@[simp]`).
- `omega` needs beta-reduced, non-`Fin`-projection goals.
- Vendored API: `MultiTapeTM.runFrom_succ_eq_step'`/`…_step` peel opposite
  ends; `Cfg.inputSymbol` is a double `dite`; work tapes are ℤ-indexed
  `Option Symbol` via `Function.update`; `moveInputPos` clamps.
- Destructure `ComputesInTime` after
  `simp only [FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace]`.
- For `2^(Q n)`-round budgets: `Nat.one_le_two_pow`, `Nat.pow_le_pow_right`,
  and epoch-1's `comp_time_bound` pattern (private; re-derive what you need).
