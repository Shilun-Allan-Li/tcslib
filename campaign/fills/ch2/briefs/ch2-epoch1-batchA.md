# Ch2 fill campaign — Epoch 1, Batch A: the polynomial-time calculus

## Context

You are filling Lean 4 proofs in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity* (2009), Chapter 2. The statement layer is complete
and has passed four external audit gates (`audits/ch2-phase*`); what remains
is filling audited-true `sorry`s. This batch delivers the chapter's working
calculus: polynomial-time computability of the identity, the output-length
bound, closure under composition, and the Karp-reduction consequences
(reflexivity, transitivity, downward closure of `P`, and the two
`P = NP`-equivalence corollaries). Everything here assembles **proved**
Chapter-1 infrastructure — `Turing.FinTM.computesFunInTime_id`,
`computesFunInTime_comp` (the timed total composition),
`computesFunInTime_ifEq`, `ComputesInTime.mono` — plus phase-1 campaign lemmas
(`Complexity.mem_P_iff`, `mem_P_of_dtime_le`, both proved). No new machine
needs to be built in this batch.

## Repository, branch, deliverable

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`. Base: branch
  `complexity/arora-barak-ch1` — all work is relative to it, **not** `main`.
- Work on a branch `fill/ch2-e1-A` off the base. **Delivery is by zip, not
  PR** (`workflow.md` §4): return `fill-ch2-e1-A.zip` containing `REPORT.md`,
  the full modified source files, a `git format-patch` series against the
  base branch, a git bundle of your branch, the final sweep log, the
  axiom-print log, and `SHA256SUMS` over all of it.
- Read first: `policy.md`; `workflow.md` §4 (ground rules, verbatim-binding);
  `AroraBarakChapter2Plan.md` §4 (the partition — you are batch 1A);
  `audits/ch2-phase1-findings.md` findings 4, 7, 9 (timed-composition
  discipline; the `max c (c·c')` exponent; no `ComputesFunInTime`-level
  monotonicity lemma).

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/ClassNP/PolyTime.lean` (3 targets)
- `TCSlib/Complexity/ClassNP/Reductions.lean` (5 targets)

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned.
  Setup once: `lake exe cache get`.
- **Never run `lake build`** — banned on this branch. Verification is the
  direct-`lean` check script:
  - Bootstrap once on a fresh clone:
    `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
    (53 modules).
  - Iterate: `bash scripts/lean_check_tree.sh TCSlib/Complexity/ClassNP/PolyTime`
    (resp. `…/Reductions`) after each edit, then every later module in the
    order list before delivery.
  - Final: the full 53-module sweep, **zero `error:` lines**; `sorry`
    warnings only at out-of-scope declarations.
- **Axiom prints**: a scratch file `#print axioms` for each filled target,
  log included in the zip. Expected: exactly
  `[propext, Classical.choice, Quot.sound]` — **except**
  `P_eq_NP_of_NPHard_mem_P` and `NPComplete.mem_P_iff`, which may
  additionally show `sorryAx` *only* through their dependency on
  `Complexity.P_subset_NP` (batch 1C's concurrent target; rely on its frozen
  statement, never inline its proof). Any other `sorryAx` is a defect.

## Ground rules (binding)

1. **File ownership.** Modify only the two owned files. Helpers are
   `private` unless there is a documented reason to export; list every new
   declaration (public and private) in `REPORT.md` — the next audit round
   blind-restates them. A lemma belonging in a shared file is *requested*
   under "Requested shared lemmas" in `REPORT.md` and meanwhile lives as a
   `private` copy in your file.
2. **Statement freeze.** Do not change the name, signature, statement,
   hypotheses, or `[AB09 …]` attribution of any existing declaration. You
   may append to a docstring's proof-sketch paragraph if the delivered proof
   deviates; flag such updates in `REPORT.md`.
3. **Escalation.** If a target appears false or unprovable as stated, STOP
   on that item, record the obstruction under "Escalations", and continue
   with the others.
4. Do not remove, weaken, or fill any sorry outside your target list.
5. Every remaining `sorry` keeps its docstring sketch; filled proofs keep
   their docstrings.
6. Precise imports; keep the `set_option` headers.

## Targets (fill in this order — later ones consume earlier ones)

Each target carries a policy-grade **Proof sketch** in its docstring; that
sketch is the audited route. Amplifications:

1. **`polyTimeComputable_id`** (PolyTime.lean:78). Unfold
   `PolyTimeComputable`; `computesFunInTime_id`'s linear bound enlarges
   pointwise into `C·(n+1)^c` via `ComputesInTime.mono` — do the enlargement
   at the `ComputesInTime` level, not `ComputesFunInTime` (phase-1 finding 9:
   no monotonicity lemma exists at that level, by design).
2. **`PolyTimeComputable.output_length_le`** (PolyTime.lean:88). One symbol
   per step: `Turing.MultiTapeTM.output_length_le` at the machine's own
   budget. Instantiate per input; the constants are the machine's.
3. **`PolyTimeComputable.comp`** (PolyTime.lean:107). The exponent is
   `max c (c·c')` — the `max` covers `c' = 0` (phase-1 finding 7); the
   sketch's absorption `a (C + C'(C+1)^{c'} + 1)(n+1)^{max c (c·c')}` is the
   audited budget arithmetic. Expect the bulk of the work in the `Nat`
   inequality chain; keep it a `private` lemma if sizable.
4. **`PolyTimeReducible.refl`** (Reductions.lean:65) — from target 1.
5. **`PolyTimeReducible.trans`** (Reductions.lean:73) — from target 3 plus
   equivalence chaining.
6. **`mem_P_of_polyTimeReducible`** (Reductions.lean:90). The **timed**
   composition only (`computesFunInTime_comp`); the untimed
   `exists_comp_partial` is forbidden here (phase-1 finding 4). Intermediate
   length via target 2; re-enter `P` through `mem_P_of_dtime_le`.
7. **`P_eq_NP_of_NPHard_mem_P`** (Reductions.lean:108) — target 6 plus
   `Complexity.P_subset_NP` (1C; sorried until epoch merge — use it).
8. **`NPComplete.mem_P_iff`** (Reductions.lean:116) — target 7 one way;
   rewrite along `P = NP` the other.

## Out-of-scope sorries you will see (leave every one untouched)

In your own files: `HALT_NPHard`, `HALT_not_mem_NP` (Reductions.lean — epoch
2). Elsewhere in E1 (concurrent batches): the NTIME/NDTM lemmas (1B), the
CoNP/NP/EXP set (1C), the `Formulas/` mathematics (1D). And the entire E2–E4
surface (`Nondeterminism`, `SAT`, `TMSAT`, `Tautology`, `CookLevin/*`,
`EXP.lean`'s two big ones). If a proof seems to *need* one of these, that is
an escalation, not a license.

## REPORT.md checklist

- [ ] Targets filled (8), one line each on how the proof went vs the sketch.
- [ ] New declarations (public and private) listed, for audit restatement.
- [ ] Requested shared lemmas — or "none".
- [ ] Escalations — or "none".
- [ ] Final full-sweep log tail (zero `error:` lines) + axiom-print log,
      with the two expected `sorryAx`-via-`P_subset_NP` cases called out.
- [ ] Diff touches only the two owned files.

## Known pitfalls at this pin (hard-won — read before proving)

- `Function.update_of_ne` (no `Function.update_noteq` at the pin).
- Core `Nat.pow_pos`, not mathlib `pow_pos` (missing order instances on ℕ).
- `dite_eq_right`/`dite_eq_left` do not exist: `split <;> simp <;> omega`.
- Avoid bare `simp` when hypotheses use folded forms; prefer targeted
  `simp only`.
- `ring` needs `import Mathlib.Tactic.Ring`; `omega` cannot see
  `(⟨e, h⟩ : Fin _).val` or un-beta-reduced lambdas — normalize with
  `show`/`simp only` first.
- Destructure `ComputesInTime` after
  `simp only [FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace]` as
  `⟨s, hhalt, hout, -⟩` (pattern in `Finite.lean`).
- Budget arithmetic: `(n+1)^c ≥ 1` (`Nat.one_le_pow`-shaped, core spelling
  `Nat.pos_pow_of_pos`-era names vary — `positivity` also works);
  `Nat.pow_le_pow_right`/`_left` for monotonicity.
