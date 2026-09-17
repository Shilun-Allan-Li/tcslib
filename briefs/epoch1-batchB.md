# Fill campaign — Epoch 1, Batch B: small machines and the branch combinator

## Context

You are filling Lean 4 proofs in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity: A Modern Approach* (2009), Chapter 1. The statement
layer is complete and has passed four external audit gates (see `audits/`); what
remains is filling audited-true `sorry`s. This batch builds **explicit machines
with machine-checked run invariants** in `Composition.lean`: two small emission
machines, then the branch combinator `exists_cond` — the first control-flow
construction in the development. The worked in-repo pattern for all three is the
already-proved `idTM` / `idTM_run` / `computesFunInTime_id` at the top of your
file: a `private` machine, a run invariant by induction on the step count, one
final halting step, `ComputesInTime.mono` to reach the stated bound. Design your
helper gadgets (especially the input-head rewind and the "fresh-tape lockstep"
lemmas) for reuse: epoch 2 fills `exists_comp_partial` in this same file and will
want them.

## Repository, branch, deliverable

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`. Base: branch
  `complexity/arora-barak-ch1` — all work is relative to it, **not** `main`.
- Create a working branch `fill/epoch1-B` off `complexity/arora-barak-ch1`; when
  done, open a PR **into `complexity/arora-barak-ch1`**.
- Read first: `policy.md`, `AroraBarakChapter1Plan.md` §5 (fill-campaign ground
  rules), and `audits/phase4-findings.md` findings 3–4 plus the surrounding
  prose (the auditor verified your constructions' key gadgets: the rewind head
  calculation and the one-emission register argument).

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/TuringMachine/Composition.lean`

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned. Setup
  once from the repo root: `lake exe cache get` (several GB on first run).
- **Never run `lake build`** — banned on this branch (plan decision log). The
  repo's `.claude/CLAUDE.md` LeanInfoView-only rule presumes a local interactive
  session; for this cloud task the maintainer-designated verification path is
  the direct-`lean` check script:
  - Bootstrap once on a fresh clone:
    `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  - Iterate: `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Composition`
    after each edit; re-check later modules in the order list before the PR.
  - Final sweep: the full loop; **zero `error:` lines**; `sorry` warnings only
    at the out-of-scope declarations listed below.

## Ground rules (binding)

1. **File ownership.** Modify only `Composition.lean`. Helpers are `private`
   unless there is a documented reason to export; list every new declaration
   (public and private) in the PR — the next audit round blind-restates them.
   If a helper belongs in a shared file (`Finite.lean`, `Configuration.lean` —
   the latter is **vendored, never touch it**): add a `private` copy in your file
   and record the request under "Requested shared lemmas" in the PR.
2. **Statement freeze.** Do not change the name, signature, statement,
   hypotheses, or `[AB09 …]` attribution of any existing declaration. You may
   append to a docstring's proof-sketch paragraph if the delivered proof
   deviates; flag such updates in the PR.
3. **Escalation.** If a target appears false or unprovable as stated, STOP on
   that item, do not alter the statement, record the obstruction under
   "Escalations" in the PR, and continue with your other targets.
4. Do not remove, weaken, or fill any sorry outside your target list — in your
   file that means `computesFunInTime_comp` and `exists_comp_partial` stay.
5. Every remaining `sorry` keeps its docstring sketch; filled proofs keep their
   docstrings.
6. Precise imports; keep the `set_option` headers.

## Targets (recommended order)

### 1. `Turing.FinTM.computesFunInTime_const`

A machine computing `fun _ => w` within `c * (n + 1)`. Simplest possible
machine: `k := 0`, `State := Fin (w.length + 1)`, transition ignoring both reads
(`fun q _ _ => …`): state `i < w.length` emits `w[i]`, keeps the input head
stationary (`SignType.zero`), steps to `i + 1`; state `w.length` takes one
halting step (`state := none`, no emission). Run invariant (induction on
`t ≤ w.length`): state is `some t`, output is `w.take t`; the input head never
moves, so no position tracking is needed — strictly easier than `idTM_run`.
Total: `w.length + 1` steps; `c := w.length + 1` works since
`c * (n + 1) ≥ c`.

### 2. `Turing.FinTM.computesFunInTime_ifEq`

The fixed-string comparator: `fun w => if w = w₀ then u else v` in linear
(actually constant) time. Note the audited disposition
(`audits/phase4-findings.md`, first table row): compare at most the first
`w₀.length + 1` positions, treating an early blank or an extra symbol as a
mismatch, then emit the selected word. Suggested state type (Fintype by
`inferInstance`): `Fin (w₀.length + 1) ⊕ Fin (u.length + 1) ⊕ Fin (v.length + 1)`
— match-progress states, then two emission chains ending in a halting step; the
transition hardcodes `w₀`, `u`, `v` by indexing. Case analysis in the invariant:
matched-so-far / mismatch-seen; the audited edge cases are `w₀ = u = v = []`
(constant machine, halts after its boundary read; no time-zero halting is
claimed) and inputs shorter/longer than `w₀`. Every run halts within
`w₀.length + max u.length v.length + 3` steps, absorbed by `c * (n + 1)`.

### 3. `Turing.FinTM.exists_cond`

The branch combinator — the substantial item. The statement is **untimed**
(halting relations only), which spares you all step accounting. Architecture,
per the audited docstring sketch:

- **State**: three phases, e.g.
  `(D.State × Option Bool) ⊕ RewindState ⊕ (M₁.State ⊕ M₂.State)` with a small
  `RewindState` carrying the register bit (`Bool × Fin 2`-style). All Fintype by
  `inferInstance`.
- **Tapes**: `D.k + M₁.k + M₂.k` fresh, disjoint tapes (no reuse — simplest).
  Define private tape-embedding helpers (`Fin.castAdd`/`Fin.natAdd`) once and
  use them consistently; expect this to be the fiddliest part.
- **Phase 1**: lockstep simulation of `D` on the true input, with `D`'s single
  emission captured in the register instead of emitted. Justification that the
  register never overflows: `hD` says the completed output is the singleton
  `[p x]`, and output is append-only
  (`Turing.MultiTapeTM.output_length_le` / `output_prefix` in `Finite.lean`),
  so `D` emits exactly one symbol over the whole run — the auditor verified
  this inference (finding 4), including *early* emission long before halting.
- **Phase 2 (rewind)**: on `D`'s halting transition, return the input head to
  its initial position (which is `1` — see `idTM_run`'s base case): one
  unconditional left step, then left while `inputSymbol` is `some _`, then one
  right step. The audited head calculation is
  `j ↦ max (j−1) 0 ↦ 0 ↦ 1` from every valid position `j ∈ [0, n+1]`,
  including the empty input (the clamp at position `0` — see
  `Turing.moveInputPos` in the vendored `Configuration.lean` — makes it safe).
  If the register is (unreachably) still empty at dispatch, have the machine
  halt — totality of the machine must not depend on `hD`; the correctness proof
  discharges reachability.
- **Phase 3 (dispatch)**: transfer to a disjoint copy of `M₁` or `M₂` per the
  register, running on the true input with its own fresh tapes and the untouched
  output tape. The key lemma is a lockstep correspondence: from (input position
  `1`, blank branch tapes, empty output, embedded branch start state), the
  composite's run mirrors the branch machine's initialized run step for step.
  The in-repo precedent for exactly this "embedded machine in lockstep" proof
  shape is the `Cfg.embedOracle_*` lemma suite in `Oracle.lean` — read it before
  designing your invariant.
- **The iff**: forward — any completed composite run decomposes into the three
  phases (phase 1 completes because `hD` gives `D` a halting time; use
  determinism, `Turing.FinTM.ComputesInTime.output_unique`, to identify the
  register with `p x`); backward — from a halting run of the selected branch,
  assemble the composite witness (D-time + rewind steps + branch time).

## Out-of-scope sorries you will see (leave every one untouched)

In your file: `computesFunInTime_comp`, `exists_comp_partial`. Elsewhere:
`universal`, `universal_quadratic`, `timed_universal` (Universal.lean);
`pairEncode_injective`, `computesFunInTime_pairEncode_diag`,
`exists_effectiveMachineCode`, `exists_codeTM` (Encoding.lean);
`alphabet_reduction`, `one_work_tape`, `nonnegative_heads`,
`oblivious_of_mem_DTIME` (Robustness/); `timeConstructible_id`
(TimeConstructible.lean); `PAL_mem_DTIME_linear` (Examples.lean);
`Computes.exists_computesFunInTime` (Computable.lean); `UC_not_computable`
(Diagonalization.lean); `UC_computable_of_HALT_computable` (Halting.lean).

## PR checklist (all of it in the PR description)

- [ ] Targets filled (3), one line each on how the proof went vs the sketch.
- [ ] New declarations (public and private) listed, for audit restatement;
      call out gadgets designed for epoch-2 reuse (rewind, tape embeddings,
      lockstep lemmas).
- [ ] Requested shared lemmas — or "none".
- [ ] Escalations — or "none".
- [ ] Verification evidence: final full-sweep log tail; zero `error:` lines.
- [ ] Diff touches only `Composition.lean`.

## Known pitfalls at this pin (hard-won — read before proving)

- `Function.update_of_ne` (no `Function.update_noteq` at the pin).
- Core `Nat.pow_pos`, not mathlib `pow_pos` (missing order instances on ℕ).
- `dite_eq_right`/`dite_eq_left` do not exist: `split <;> simp <;> omega`.
- After `cases hs : cfg.state`, insert `dsimp only` to iota-reduce
  `match some q with …` before rewriting, or use nested `split`.
- Avoid bare `simp` when hypotheses use folded forms (`initCfg` is `@[simp]`);
  prefer targeted `simp only`.
- `ring` needs `import Mathlib.Tactic.Ring` (check the file's imports before
  using it; add precisely what you use).
- `omega` cannot see `(⟨e, h⟩ : Fin _).val` or un-beta-reduced lambdas:
  normalize with `show` / `simp only` first (see `idTM_run`'s
  `show ((… ).inputPos : ℕ) + 1 = t + 2` trick).
- SignType lemma names at the pin: `SignType.coe_one`, `SignType.neg_eq_neg_one`,
  `SignType.coe_neg_one`, `SignType.pos_eq_one`.
- Vendored API you will lean on: `MultiTapeTM.runFrom_succ_eq_step'`,
  `MultiTapeTM.step`, `Action.apply`, `Cfg.inputSymbol` (a double `dite` —
  destructure with `dif_neg`/`dif_pos` as in `computesFunInTime_id`),
  `moveInputPos_pos_of_ne_right`, `inputSymbolInner`.
- Destructure `ComputesInTime` after
  `simp only [FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace]` as
  `⟨s, hhalt, hout, -⟩`.
