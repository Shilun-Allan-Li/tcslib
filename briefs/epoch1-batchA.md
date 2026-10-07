# Fill campaign — Epoch 1, Batch A: the assembly proofs

## Context

You are filling Lean 4 proofs in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity: A Modern Approach* (2009), Chapter 1. The statement
layer is complete and has passed four external audit gates (see `audits/`); what
remains is filling audited-true `sorry`s. This batch is the **integration test of
the whole interface stack**: four proofs that are pure *assembly* — they chain
already-stated results and construct no machines. Filling them machine-checks that
the phase-3/4 interfaces genuinely compose, which is the single highest
risk-retirement step of the campaign. Your proofs may (and must) cite theorems
that are themselves still `sorry`d — that is by design; citing a `sorry`d theorem
produces no new warning on your declaration.

## Repository, branch, deliverable

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`. Base: branch
  `complexity/arora-barak-ch1` — all work is relative to it, **not** `main`.
- Create a working branch `fill/epoch1-A` off `complexity/arora-barak-ch1`; when
  done, open a PR **into `complexity/arora-barak-ch1`**.
- Read first: `policy.md` (repo standards), `AroraBarakChapter1Plan.md` §5
  (phasing, audit protocol, fill-campaign ground rules), and
  `audits/phase4-findings.md` (your two hardest targets follow its derivations
  line by line).

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/Uncomputability/Computable.lean`
- `TCSlib/Complexity/Uncomputability/Diagonalization.lean`
- `TCSlib/Complexity/Uncomputability/Halting.lean`
- `TCSlib/Complexity/TuringMachine/Universal.lean` — **only** the proof of
  `universal_quadratic`; the `universal` and `timed_universal` sorries stay.

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned by the
  manifest. One-time setup from the repo root: `lake exe cache get` (first run
  installs the toolchain and downloads the mathlib build cache; several GB).
- **Never run `lake build`** — banned on this branch (plan decision log). The
  repo's `.claude/CLAUDE.md` tells agents to rely on the VS Code LeanInfoView and
  run no build commands; that rule presumes a local interactive session. For this
  cloud task the maintainer-designated verification path (recorded in the plan
  decision log) is the direct-`lean` check script:
  - Bootstrap once on a fresh clone (fills the scratch olean tree, dependency
    order):
    `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  - Iterate: `bash scripts/lean_check_tree.sh <module>` after each edit (module
    path without `.lean`). When you edit a file, re-check it and every *later*
    module in the order list before relying on the result.
  - Final sweep before the PR: the full bootstrap loop again; **zero `error:`
    lines**; `declaration uses 'sorry'` warnings only at the out-of-scope
    declarations listed below.

## Ground rules (binding)

1. **File ownership.** Modify only the owned files. Helper lemmas go in your
   owned files, `private` unless there is a documented reason to export; list
   every new declaration (public and private) in the PR description — the next
   audit round blind-restates them. If a helper belongs in a shared file
   (`Finite.lean`, say): do **not** edit that file — add a `private` copy in your
   own file and record the request under "Requested shared lemmas" in the PR.
2. **Statement freeze.** Do not change the name, signature, statement,
   hypotheses, or `[AB09 …]` attribution of any existing declaration — this is
   externally audited surface. You may append to a docstring's proof-sketch
   paragraph if your delivered proof deviates from the sketch; flag such updates
   in the PR.
3. **Escalation.** If a target appears false or unprovable as stated, STOP on
   that item, do not alter the statement, record the obstruction (approach,
   failing goal, candidate counterexample) under "Escalations" in the PR, and
   continue with your other targets. Statement changes go through the audit
   process, never through fill PRs.
4. Do not remove, weaken, or fill any sorry outside your target list — including
   in your own files.
5. Every remaining `sorry` keeps its docstring sketch (policy.md §3); filled
   proofs keep their docstrings.
6. Precise imports: add exactly what you use; never bare `import Mathlib`; keep
   the existing `set_option` headers.

## Targets

### 1. `Turing.FinTM.Computes.exists_computesFunInTime` (Computable.lean)

A machine computing `f` with no stated bound admits some time bound. Plan (per
the docstring sketch): `choose t ht using h` to name a halting time per input;
for each `n`, the inputs of length `n` form a finite type — transport `Fintype`
from `Fin n → Symbol` (via `List.Vector Symbol n` and its equivalence, or any
route you prefer, e.g. `Fintype.ofEquiv` on the subtype
`{x : List Symbol // x.length = n}`); set `T n` to the `Finset.univ.sup` of the
chosen times; conclude with `ComputesInTime.mono` (`Finite.lean`). No
monotonicity or positivity of `T` is claimed. Mind the degenerate cases the audit
checked: empty `Symbol` (positive lengths have no inputs — `sup` of an empty set
is `0`, harmless) and `n = 0` (the empty input still has its chosen time).

### 2. `Complexity.UC_not_computable` (Diagonalization.lean)

[AB09, Theorem 1.10] for an arbitrary `MachineCode`. Follow the docstring sketch
and, in more detail, `audits/phase4-findings.md`, section "The diagonalization
assembles without an effectivity assumption". Chain:
`Computes.exists_computesFunInTime` → `Turing.FinTM.one_work_tape_binary`
(in `Robustness/SingleTape.lean` — add the precise import
`TCSlib.Complexity.TuringMachine.Robustness.SingleTape` to Diagonalization.lean)
→ `Turing.exists_codeTM` → set `α₀ := c.encode N`, rewrite with
`Turing.MachineCode.decode_encode` → case on `UC c α₀` using
`Complexity.UC_eq_false_iff` and
`Turing.FinTM.ComputesInTime.output_unique`; both cases end in `[false] = [true]`
or a Bool contradiction (`simp` closes singleton-list injectivity).

### 3. `Turing.universal_quadratic` (Universal.lean)

The total-function corollary of Theorem 1.9. Plan (docstring sketch): obtain
`⟨U, hU⟩ := universal c`; given `M₀` computing `f` within `T`, apply
`one_work_tape_binary`, then `exists_codeTM`, take `α := c.encode` of the coded
machine, rewrite with `MachineCode.decode_encode`, and use the **forward clause**
of `hU α`. The constant arithmetic
`C_U * (c₁ * (T n + 1)^2 + 1) ≤ C_U * (c₁ + 1) * (T n + 1)^2` has a direct
in-repo template: the `calc` block closing `one_work_tape_binary` in
`Robustness/SingleTape.lean` (uses `Nat.pow_pos`, `Nat.mul_le_mul`, `ring`).
Finish with `ComputesInTime.mono`.

### 4. `Complexity.UC_computable_of_HALT_computable` (Halting.lean)

The [AB09, Theorem 1.11] reduction. Follow `audits/phase4-findings.md`, section
"The HALT reduction also assembles entirely through the stated interfaces" — it
is a line-by-line script. Ingredients (all stated): `universal c` (forward clause
only), `Turing.computesFunInTime_pairEncode_diag` (Encoding.lean),
`Turing.FinTM.computesFunInTime_ifEq [true] [false] [true]` and
`computesFunInTime_const [true]` (Composition.lean), `exists_comp_partial`
(three uses), `exists_cond`, `ComputesFunInTime.computes`,
`ComputesInTime.output_unique`, `HALT_pairEncode_eq_true_iff`, and the `UC`
unfolding lemmas. Suggested skeleton: first prove a small private lemma "a total
machine's halting relation is equality with its prescribed output"
(`hM : M.Computes g → ((∃ t, M.ComputesInTime x w t) ↔ w = g x)`, via
`output_unique`), which collapses each `exists_comp_partial` application; then
the two-case correctness argument over `p α`.

## Out-of-scope sorries you will see (leave every one untouched)

In your owned files: `universal`, `timed_universal` (Universal.lean). Everywhere
else: `computesFunInTime_const`, `computesFunInTime_ifEq`,
`computesFunInTime_comp`, `exists_comp_partial`, `exists_cond`
(Composition.lean); `pairEncode_injective`, `computesFunInTime_pairEncode_diag`,
`exists_effectiveMachineCode`, `exists_codeTM` (Encoding.lean);
`alphabet_reduction`, `one_work_tape`, `nonnegative_heads`,
`oblivious_of_mem_DTIME` (Robustness/); `timeConstructible_id`
(TimeConstructible.lean); `PAL_mem_DTIME_linear` (Examples.lean). After your
batch, exactly these 17 sorry warnings remain in the sweep.

## PR checklist (all of it in the PR description)

- [ ] Targets filled (4), one line each on how the proof went vs the sketch.
- [ ] New declarations added (public and private), for audit restatement.
- [ ] Requested shared lemmas — or "none".
- [ ] Escalations — or "none".
- [ ] Verification evidence: the final full-sweep log tail (per-module lines and
      warnings) and confirmation of zero `error:` lines.
- [ ] Diff touches only the owned files.

## Known pitfalls at this pin (hard-won — read before proving)

- `Function.update_of_ne` (the pin has no `Function.update_noteq`).
- Use core `Nat.pow_pos`, not mathlib `pow_pos` (missing order instances on ℕ).
- `dite_eq_right`/`dite_eq_left` do not exist: use `split <;> simp <;> omega` or
  explicit cases.
- After `cases hs : cfg.state`, goals can keep `match some q with …` unreduced —
  insert `dsimp only` before rewriting, or restructure with nested `split`.
- Avoid bare `simp` when hypotheses use folded forms (`initCfg` is `@[simp]` and
  full `simp` desynchronizes goal from hypotheses); prefer targeted `simp only`.
- `ring` needs `import Mathlib.Tactic.Ring`.
- `omega` cannot see `(⟨e, h⟩ : Fin _).val` or un-beta-reduced `(fun n => …) n`:
  normalize with `show` / `simp only` / `le_of_eq` first.
- `Nat.find` under classical: `classical` tactic plus explicit `(p := fun n : ℕ => …)`.
- `⋃`-membership via `Set.mem_iUnion`; `Language` has `Zero`
  (`(0 : Language _)`, `Language.notMem_zero`), not `∅`.
- Destructure `ComputesInTime` after
  `simp only [FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace]` as
  `⟨s, hhalt, hout, -⟩` (see `ComputesInTime.mono` / `output_unique` in
  `Finite.lean` for the pattern).
