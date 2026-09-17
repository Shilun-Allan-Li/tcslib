# Fill campaign — Epoch 1, Batch D: the classic machines

## Context

You are filling Lean 4 proofs in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity: A Modern Approach* (2009), Chapter 1. The statement
layer is complete and has passed four external audit gates (see `audits/`); what
remains is filling audited-true `sorry`s. This batch delivers the chapter's two
"textbook example" machines: the three-phase palindrome decider ([AB09,
Example 1.1]) and the binary-counter witness that the identity function is time
constructible — the latter's **amortized** step accounting is the real content.
Both have worked constructions in the phase-1 audit records; your job is to
formalize them. The worked in-repo proof pattern is `Composition.lean`'s `idTM`
/ `idTM_run` / `computesFunInTime_id`: a `private` machine, a run invariant by
induction on the step count, a final halting step, `ComputesInTime.mono`.

## Repository, branch, deliverable

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`. Base: branch
  `complexity/arora-barak-ch1` — all work is relative to it, **not** `main`.
- Create a working branch `fill/epoch1-D` off `complexity/arora-barak-ch1`; when
  done, open a PR **into `complexity/arora-barak-ch1`**.
- Read first: `policy.md`, `AroraBarakChapter1Plan.md` §5 (fill-campaign ground
  rules), and the phase-1 audit records: `audits/phase1-findings.md` (the
  per-sorry dispositions — the `PAL_mem_DTIME_linear` row spells out the
  boundary transitions and the `n = 0` trace) and
  `audits/phase1-reaudit-findings.md` (the explicit four-state counter witness
  — states named `count`/`carry`/`rewind`/`emit` — with its carry-length field
  calculation; the notation glossary at the end decodes the variables).

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/ClassP/Examples.lean` (`PAL_mem_DTIME_linear`)
- `TCSlib/Complexity/ClassP/TimeConstructible.lean` (`timeConstructible_id`)

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned. Setup
  once from the repo root: `lake exe cache get` (several GB on first run).
- **Never run `lake build`** — banned on this branch (plan decision log). The
  repo's `.claude/CLAUDE.md` LeanInfoView-only rule presumes a local interactive
  session; for this cloud task the maintainer-designated verification path is
  the direct-`lean` check script:
  - Bootstrap once on a fresh clone:
    `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  - Iterate: `bash scripts/lean_check_tree.sh TCSlib/Complexity/ClassP/Examples`
    (resp. `…/TimeConstructible`) after each edit; re-check the later modules
    in the order list before the PR.
  - Final sweep: the full loop; **zero `error:` lines**; `sorry` warnings only
    at the out-of-scope declarations listed below.

## Ground rules (binding)

1. **File ownership.** Modify only the two owned files. Helpers are `private`
   unless there is a documented reason to export; list every new declaration
   (public and private) in the PR — the next audit round blind-restates them.
   If a helper belongs in a shared file (`Finite.lean`; the vendored
   `Configuration.lean`/`Deterministic.lean` are **frozen**): add a `private`
   copy in your file and record the request under "Requested shared lemmas" in
   the PR.
2. **Statement freeze.** Do not change the name, signature, statement,
   hypotheses, or `[AB09 …]` attribution of any existing declaration. You may
   append to a docstring's proof-sketch paragraph if the delivered proof
   deviates; flag such updates in the PR.
3. **Escalation.** If a target appears false or unprovable as stated, STOP on
   that item, do not alter the statement, record the obstruction under
   "Escalations" in the PR, and continue with the other target.
4. Do not remove, weaken, or fill any sorry outside your target list.
5. Every remaining `sorry` keeps its docstring sketch; filled proofs keep their
   docstrings.
6. Precise imports; keep the `set_option` headers.

## Targets

### 1. `Complexity.PAL_mem_DTIME_linear` (Examples.lean)

`PAL ∈ DTIME (fun n => n + 1)`: exhibit `c` and a machine deciding palindromes
within `c * (n + 1)`. The file's docstring sketch gives the machine — one work
tape, phases `copy` / `rewind` / `test`:

1. *Copy* (`n + 1` steps): input head and work head move right in unison,
   copying each input symbol; ends when the input head reads the boundary blank.
2. *Rewind* (`n + 1` steps): input head walks back to the left boundary (the
   clamp at `0` — `Turing.moveInputPos` — makes the walk safe); one step of the
   work head left onto the last copied symbol.
3. *Test* (`n + 1` steps): input head right, work head left, in unison,
   comparing; mismatch → emit `false`, halt; input head reads blank again →
   emit `true`, halt.

`audits/phase1-findings.md` (the `PAL_mem_DTIME_linear` row) confirms the
boundary transitions and that constant `3` (any `c ≥ 3`, e.g. `c = 4` per the
sketch) covers every input including `n = 0` (three boundary transitions
emitting `true`). Proof shape: per-phase run invariants by induction (the copy
phase generalizes `idTM_run` with a work tape: after `t` steps, work-tape cells
`0..t-1` hold the first `t` input bits and the work head is at `t`); note the
target output is `[MultiTapeTM.indicator (PAL : Set (List Bool)) x]`, so you
will relate the mismatch/match outcome to `x = x.reverse` — expect a small
list-lemma bridge (e.g. comparing `x` against its reversal position by position:
`x.reverse.get ⟨i, _⟩ = x.get ⟨n - 1 - i, _⟩`-style, via `List.getElem_reverse`
at the pin). Work-tape cells are ℤ-indexed `Option Bool`; blanks are `none`.

### 2. `Complexity.timeConstructible_id` (TimeConstructible.lean)

`TimeConstructible id`: the `∀ n, n ≤ id n` half is `le_refl`; the content is a
machine computing `x ↦ (Nat.bits x.length)` within `c * (x.length + 1)`. The
audited construction (`audits/phase1-reaudit-findings.md`, the explicit counter
witness) is a one-work-tape, four-state machine `count`/`carry`/`rewind`/`emit`
maintaining a little-endian binary counter:

- For each input symbol read, increment the counter: walk right from cell `0`
  over `true` cells flipping them `false` (`carry`), write `true` in the first
  `false`/blank cell, walk back to cell `0` (`rewind`), advance the input head
  (`count`).
- When the input head reads the boundary blank, walk the counter left to right
  emitting each bit (`emit`), and halt at the first blank counter cell. For
  `n = 0` the counter region is empty and nothing is emitted — matching
  `Nat.bits 0 = []` (`Nat.bits` is least-significant-bit first).

**The amortized accounting is the crux.** Increment `i` costs
`Θ(trailing-ones of i)`, so a per-increment worst-case bound gives only
`O(n log n)` — not enough. You need the global bound: total carry work over
increments `0, 1, …, n−1` is at most `2n` (each cell flip `false → true`
happens once per increment and pays for the single later flip back). Two
formalization routes — pick whichever goes through:

- **Potential invariant**: strong induction maintaining "after `i` increments,
  the work tape holds the bits of `i`, the head is at `0`, and the total steps
  so far are `≤ B(i)`" with an explicit `B(i) ≤ c₀ * (i + 1)` — e.g.
  `B(i) = c₀*i + (number of true bits of i)`-style so the per-increment cost
  telescopes against the popcount change (cost of increment ≈ 2·(trailing ones)
  + O(1), and popcount drops by (trailing ones) − 1).
- **Closed sum**: prove `∑_{i<n} (trailing ones of i) ≤ n` (equivalently
  `∑ carries = n − popcount n`) as a standalone `private` arithmetic lemma by
  induction, then bound the run time by the sum.

The reaudit findings' field calculation (variables `r` = trailing ones, `v` =
high part, `j` = carry lengths) is exactly this arithmetic — mirror it. Also
budget the final `emit` phase: `O(|Nat.bits n|) ≤ O(n)` steps, and the emitted
list must be *exactly* `Nat.bits x.length` — expect small `Nat.bits` bridging
lemmas (`Nat.bits` interacts with `Nat.bit`/parity; `Mathlib.Data.Nat.Bits` is
already imported in this file). The stated bound has an existential `c > 0` —
be generous; no tight constant is needed.

## Out-of-scope sorries you will see (leave every one untouched)

`universal`, `universal_quadratic`, `timed_universal` (Universal.lean);
`computesFunInTime_const`, `computesFunInTime_ifEq`, `computesFunInTime_comp`,
`exists_comp_partial`, `exists_cond` (Composition.lean); `pairEncode_injective`,
`computesFunInTime_pairEncode_diag`, `exists_effectiveMachineCode`,
`exists_codeTM` (Encoding.lean); `alphabet_reduction`, `one_work_tape`,
`nonnegative_heads`, `oblivious_of_mem_DTIME` (Robustness/);
`Computes.exists_computesFunInTime` (Computable.lean); `UC_not_computable`
(Diagonalization.lean); `UC_computable_of_HALT_computable` (Halting.lean).

## PR checklist (all of it in the PR description)

- [ ] Targets filled (2), one line each on how the proof went vs the sketch —
      in particular, which amortization route `timeConstructible_id` took.
- [ ] New declarations (public and private) listed, for audit restatement —
      call out any standalone arithmetic lemmas (carry sums, `Nat.bits`
      bridges) that might merit later promotion.
- [ ] Requested shared lemmas — or "none".
- [ ] Escalations — or "none".
- [ ] Verification evidence: final full-sweep log tail; zero `error:` lines.
- [ ] Diff touches only the two owned files.

## Known pitfalls at this pin (hard-won — read before proving)

- `Function.update_of_ne` (no `Function.update_noteq` at the pin).
- Core `Nat.pow_pos`, not mathlib `pow_pos` (missing order instances on ℕ).
- `dite_eq_right`/`dite_eq_left` do not exist: `split <;> simp <;> omega`.
- After `cases hs : cfg.state`, insert `dsimp only` to iota-reduce
  `match some q with …` before rewriting, or use nested `split`.
- Avoid bare `simp` when hypotheses use folded forms (`initCfg` is `@[simp]`);
  prefer targeted `simp only`.
- `ring` needs `import Mathlib.Tactic.Ring`.
- `omega` cannot see `(⟨e, h⟩ : Fin _).val` or un-beta-reduced lambdas:
  normalize with `show` / `simp only` first (see `idTM_run` in
  `Composition.lean`).
- SignType lemma names at the pin: `SignType.coe_one`, `SignType.neg_eq_neg_one`,
  `SignType.coe_neg_one`, `SignType.pos_eq_one`.
- Vendored API: `MultiTapeTM.runFrom_succ_eq_step'`, `MultiTapeTM.step`,
  `Action.apply`, `Cfg.inputSymbol` (double `dite`),
  `moveInputPos_pos_of_ne_right`, `inputSymbolInner`; work tapes are ℤ-indexed
  `Option Symbol` functions updated via `Function.update`.
- Destructure `ComputesInTime` after
  `simp only [FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace]` as
  `⟨s, hhalt, hout, -⟩` (pattern in `Finite.lean`'s `mono`/`output_unique`).
