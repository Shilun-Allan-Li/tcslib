# Fill campaign — Epoch 2, Batch A: the guarded-composition core

## Context

You are filling Lean 4 proofs in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity: A Modern Approach* (2009), Chapter 1. Twelve of the
21 audited sorries were proved in epoch 1 (externally audited clean —
`audits/epoch1-findings.md`); nine remain. This batch delivers the two
load-bearing composition theorems: **partial (guarded) sequential composition**
`exists_comp_partial` — three already-proved theorems cite it — and the timed
total-function composition `computesFunInTime_comp`, which shares its core
construction. Fill `exists_comp_partial` first, then reuse its machinery for
`computesFunInTime_comp` with time accounting on top.

Epoch 1 left you a genuine head start, but the epoch-1 audit (finding 11)
delimited it precisely — read this before designing anything:

- `TCSlib/Complexity/TuringMachine/Simulation.lean` (public, shared) has the
  emission chains, control actions, the audited input-head rewind
  (`rewind_scan`, `rewind_from_any`), and the disjoint tape-block embeddings
  `leftCfg`/`rightCfg` with lockstep `apply`/`step`/`run` lemmas.
- **Those embeddings are NOT yet a buffered-composition simulator**: they
  preserve the *native* input tape and pass emissions to the *real* output.
  Your construction additionally needs (a) a **buffer representation** — phase
  one must redirect `M₁`'s emissions to a work tape while the real output stays
  empty — and (b) a **virtual-input relation**: phase two serves `M₂`'s input
  reads from the buffer with clamped boundary semantics mirroring
  `Turing.moveInputPos`. Neither invariant exists yet; they are the heart of
  this batch.
- The audited boundary details (phase-4 audit, finding 3; epoch-1 findings,
  `exists_comp_partial` row): after phase one the buffer head rests on the
  blank immediately *right* of the written word, so the rewind's first left
  move must be unconditional (testing before moving stops at the wrong end);
  for an **empty** intermediate word the simulation starts with the
  right-boundary tag already set, the left boundary one inward move away; at a
  boundary, supply a blank read and suppress outward moves, with *which*
  boundary known from the direction of arrival, tracked in the state.
- The composite must not have completed outputs during administrative
  transitions (rewind/dispatch): both directions of the iff concern completed
  outputs, so administrative states stay live (the epoch-1 `condTM` handled
  this with a live administrative state after the simulated halt — mirror it).
- Useful proved lemmas in `Finite.lean`: `computesInTime_iff` (space-free
  unfolding), `Computes.exists_computesInTime_iff`,
  `ComputesInTime.output_unique`, `ComputesInTime.mono`, and the raw-layer
  `MultiTapeTM.output_length_le` / `output_prefix` (each step emits at most
  one symbol; output only grows) — the last two drive the buffer invariant
  and `comp`'s length bound.

## Repository, base, deliverable (zip — there is no PR step)

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`, branch
  `complexity/arora-barak-ch1`. **Base commit: `24687122`** — verify
  `git rev-parse HEAD` after checkout. Create a local branch `fill/epoch2-A`
  and commit your work there. GitHub write access is not available from this
  environment; **do not attempt to push or open a PR.**
- **Deliverable: a single zip archive** containing, at minimum:
  1. `REPORT.md` — the full report per the checklist below.
  2. The complete modified source files at their repository paths
     (e.g. `TCSlib/Complexity/TuringMachine/Composition.lean`).
  3. `epoch2-A.patch` — `git format-patch` output of your commits against
     `24687122` (`git format-patch 24687122 --stdout > epoch2-A.patch`).
  4. `epoch2-A.bundle` — `git bundle create epoch2-A.bundle 24687122..fill/epoch2-A`
     (or the full branch).
  5. `final-sweep.log` — the complete output of the final full sweep.
  6. `axioms.log` — `#print axioms` output for each filled theorem, produced
     via a scratch file *outside* the repository (imports the owned modules,
     one `#print axioms` per target; run with the same `LEAN_PATH` the check
     script assembles). Expected: `[propext, Classical.choice, Quot.sound]`
     and **no `sorryAx`** — these are self-contained constructions.
  7. `SHA256SUMS` — a hash manifest of every file in the zip.
- Read first: `policy.md`, `AroraBarakChapter1Plan.md` §5 (campaign + ground
  rules), `audits/epoch1-findings.md` (finding 11 and the
  `exists_comp_partial` / `computesFunInTime_comp` rows), and the docstring
  sketches on both targets.

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/TuringMachine/Composition.lean` (both targets live here)
- `TCSlib/Complexity/TuringMachine/Simulation.lean` (shared gadget layer)

Placement rules: genuinely reusable infrastructure (the buffer representation,
the virtual-input serving relation and its clamping invariants) belongs in
`Simulation.lean`, **public with docstrings** — it precedes `Composition.lean`
in the import order, which also resolves Lean's no-forward-reference
constraint (epoch-1 audit, finding 11: helpers must precede their use).
Proof-specific privates may live in `Composition.lean` but must be defined
*above* the theorem that uses them. Keep `Composition.lean` under ~1000 lines
(policy §1); prefer moving generic layers to `Simulation.lean` over growing it.

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned. Setup
  once from the repo root: `lake exe cache get` (several GB on first run).
- **Never run `lake build`** (banned on this branch; plan decision log). The
  repo's `.claude/CLAUDE.md` LeanInfoView-only rule presumes a local
  interactive session; for this cloud task the maintainer-designated
  verification path is `scripts/lean_check_tree.sh` — note it was
  **strengthened after an audit finding**: it now fails on a nonzero `lean`
  exit, on `error:` diagnostics, or on a missing fresh `.olean`. Sweep recipe
  (subshell, so a failure fails the whole run):
  `( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done < scripts/ab_ch1_module_order.txt )`
- Bootstrap once on a fresh clone with that sweep; iterate per module
  (`Simulation` before `Composition`, then everything after `Composition` in
  the order list); finish with the full sweep. Pass = sweep exits 0, zero
  `error:` lines, and `declaration uses 'sorry'` warnings **only** at the
  out-of-scope declarations listed below.

## Ground rules (binding)

1. **File ownership.** Modify only the two owned files. Every new declaration
   (public in `Simulation.lean`, or private in `Composition.lean`) is listed in
   `REPORT.md` — new public declarations become audited surface and will be
   blind-restated next round, so write real docstrings. If a helper belongs in
   another shared file (`Finite.lean`; vendored files are **frozen**): add a
   `private` copy in an owned file and record the request under "Requested
   shared lemmas".
2. **Statement freeze.** Do not change the name, signature, statement,
   hypotheses, or attribution of any existing declaration. Docstring
   proof-sketch paragraphs may gain an appended implementation note; flag such
   updates in `REPORT.md`.
3. **Escalation.** If a target appears false or unprovable as stated, STOP on
   that item, do not alter the statement, record the obstruction under
   "Escalations", and continue with the other target.
4. Do not remove, weaken, or fill any sorry outside your target list.
5. Every remaining `sorry` keeps its docstring sketch; filled proofs keep
   their docstrings.
6. Precise imports; keep the `set_option` headers.

## Targets (in this order)

### 1. `Turing.FinTM.exists_comp_partial`

`∀ x w, (∃ t, M(x) ↓ w) ↔ ∃ y, (∃ t, M₁(x) ↓ y) ∧ (∃ t, M₂(y) ↓ w)` — untimed,
no totality hypotheses. Suggested architecture (the docstring sketch, plus the
audit refinements above): tapes `M₁.k + 1 + M₂.k` (buffer in the middle);
states = phase-1 controller (`M₁`'s state, lockstep, emissions redirected to
the buffer: write, move right) ⊕ live administrative rewind states ⊕ phase-2
simulator (`M₂`'s state × virtual-boundary tag). Phase-1 invariant: real
output empty, buffer holds exactly `M₁`'s emitted-so-far output contiguously
from cell 0 (use `output_prefix`/`output_length_le` style reasoning), `M₂`
block blank. Rewind per the audited procedure. Phase-2 invariant: the virtual
input relation — `M₂`'s configuration on input `y` corresponds to the
composite's, with `M₂`-input position `v` matched to the buffer head at cell
`v − 1`, boundary reads blank, outward moves suppressed. Both iff directions
by run correspondence; `output_unique` collapses the intermediate `y`; if
`M₁` diverges the composite never leaves phase 1, and if `M₂` diverges on the
unique `y` the composite never halts (administrative states are live).

### 2. `Turing.FinTM.computesFunInTime_comp`

Same construction, now with the time ledger (docstring sketch + epoch-1
findings row): phase one costs a constant per `M₁` step (≤ `T₁ n` steps);
the rewind costs at most the buffer length + 2 ≤ `T₁ n + 2` (by
`output_length_le`, `|f x| ≤ T₁ |x|`); phase two costs a constant per `M₂`
step, and `M₂` halts within `T₂ |f x| ≤ T₂ (T₁ n)` — **this is where
`Monotone T₂` is genuinely used**; bookkeeping absorbs into `c`. Conclusion:
`c * (T₁ n + T₂ (T₁ n) + 1)`. If you build 1 first, this is largely a timed
re-run of the same invariants; design them with step counts from the start.

## Out-of-scope sorries you will see (leave every one untouched)

Elsewhere only (your two files carry no other sorries): `alphabet_reduction`,
`one_work_tape`, `nonnegative_heads`, `oblivious_of_mem_DTIME` (Robustness/);
`exists_effectiveMachineCode` (Encoding.lean); `universal`, `timed_universal`
(Universal.lean). After your batch, exactly these 7 sorry warnings remain.

## REPORT.md checklist

- [ ] Targets filled (2), with how each proof relates to its sketch.
- [ ] New declarations: public (Simulation.lean — full list with one-line
      statements) and private, for audit restatement.
- [ ] Requested shared lemmas — or "none".
- [ ] Escalations — or "none".
- [ ] Docstring appendices added — or "none".
- [ ] Verification evidence: final full-sweep log reference (attached file),
      axiom log reference, confirmation of zero `error:` lines and the exact
      7 remaining sorry warnings.
- [ ] Diff touches only the two owned files.

## Known pitfalls at this pin (hard-won — read before proving)

- `Function.update_of_ne` (no `Function.update_noteq` at the pin); core
  `Nat.pow_pos` (not mathlib `pow_pos`); `dite_eq_right/left` don't exist —
  `split <;> simp <;> omega`; after `cases hs : cfg.state` insert `dsimp only`
  to iota-reduce; avoid bare `simp` when hypotheses use folded forms
  (`initCfg` is `@[simp]`) — prefer targeted `simp only`; `ring` needs
  `import Mathlib.Tactic.Ring`; `omega` can't see `(⟨e, h⟩ : Fin _).val` or
  un-beta-reduced lambdas — normalize with `show`/`simp only` first;
  `Nat.find` under classical needs `classical` + explicit `(p := …)`;
  SignType lemmas: `SignType.coe_one`, `neg_eq_neg_one`, `coe_neg_one`,
  `pos_eq_one`, and `SignType.zero_eq_zero` with `moveInputPos_zero`.
- Worked exemplars of the invariant style, in-repo and proved: `condTM` +
  `controlCfg_step`/`controlCfg_run`/`condTM_start` (Composition.lean — the
  closest relative of your construction: register capture, live
  administrative states, `Nat.find` first-halting-time, `rewind_from_any`,
  then branch lockstep), `pairDiagTM` (Encoding.lean, multi-phase with
  rewind), `counterTM` (TimeConstructible.lean, work-tape invariants via a
  `counterTape` shape function), `palTM` (Examples.lean, two-head phases).
- Tape-index bookkeeping: use `Fin.addCases` consistently (see
  `leftCfg`/`rightCfg` in Simulation.lean); define the three-block partition
  once and prove its projection lemmas before anything else.
