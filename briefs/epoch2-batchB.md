# Fill campaign — Epoch 2, Batch B: one work tape (the heavyweight)

## Context

You are filling one Lean 4 proof in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity: A Modern Approach* (2009), Chapter 1:
`Turing.FinTM.one_work_tape` — [AB09, Claim 1.6] rendered in this model as
"one work tape suffices, quadratically". This is the single heaviest
construction of the whole campaign (the Isabelle AFP `Cook_Levin` entry sank
most of its effort into exactly this simulation), and it is deliberately a
solo batch: take the time it needs. Twelve of 21 audited sorries are already
proved and audited; the already-proved `one_work_tape_binary` directly below
your target chains it with `alphabet_reduction`, so your theorem is
load-bearing for the universal machine and Theorem 1.10.

## Repository, base, deliverable (zip — there is no PR step)

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`, branch
  `complexity/arora-barak-ch1`. **Base commit: `24687122`** — verify with
  `git rev-parse HEAD` after checkout. Create a local branch `fill/epoch2-B`
  and commit your work there. GitHub write access is not available from this
  environment; **do not attempt to push or open a PR.**
- **Deliverable: a single zip archive** containing, at minimum:
  1. `REPORT.md` — the full report per the checklist below.
  2. The complete modified source file at its repository path
     (`TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean`).
  3. `epoch2-B.patch` — `git format-patch 24687122 --stdout > epoch2-B.patch`.
  4. `epoch2-B.bundle` — `git bundle create epoch2-B.bundle 24687122..fill/epoch2-B`.
  5. `final-sweep.log` — the complete output of the final full sweep.
  6. `axioms.log` — `#print axioms Turing.FinTM.one_work_tape` (and, as a
     regression check, `#print axioms Turing.FinTM.one_work_tape_binary`),
     produced via a scratch file *outside* the repository with the check
     script's `LEAN_PATH`. Expected: `[propext, Classical.choice, Quot.sound]`,
     **no `sorryAx`** for `one_work_tape`; `one_work_tape_binary` will still
     show `sorryAx` only if `alphabet_reduction` (another batch) is unfilled
     in your tree — say so in the report.
  7. `SHA256SUMS` — a hash manifest of every file in the zip.
- Read first: `policy.md`, `AroraBarakChapter1Plan.md` §5,
  `audits/phase2-findings.md` and `audits/phase2-reaudit-findings.md` (the
  audited construction: this target's sketch was *corrected* by that audit —
  the tagged-payload alphabet is the mandated design), and the docstring
  sketch on the target.

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean`

`one_work_tape_binary`, in the same file, is **proved — do not touch it**.
All helpers are `private` in this file, defined *above* the target theorem
(Lean has no forward references). If the file approaches ~1000 lines
(policy §1), prefer tighter decomposition over splitting: a split would
change shared structure, which is not this batch's call — escalate in
`REPORT.md` instead if you believe one is needed.

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned.
  Setup once from the repo root: `lake exe cache get` (several GB).
- **Never run `lake build`** (banned; plan decision log). The repo's
  `.claude/CLAUDE.md` LeanInfoView-only rule presumes a local interactive
  session; the maintainer-designated verification path is
  `scripts/lean_check_tree.sh` (strengthened after an audit finding: fails on
  nonzero `lean` exit, `error:` diagnostics, or a missing fresh `.olean`).
  Sweep recipe:
  `( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done < scripts/ab_ch1_module_order.txt )`
- Bootstrap once with that sweep; iterate on your module, then re-check
  everything after it in the order list; finish with the full sweep. Pass =
  sweep exits 0, zero `error:` lines, sorry warnings only at the out-of-scope
  list below.

## Ground rules (binding)

1. **File ownership.** Modify only the owned file; helpers `private`; list
   every new declaration in `REPORT.md` (the next audit round restates them).
   Needed lemmas that belong in shared files (`Finite.lean`,
   `Simulation.lean`; vendored files **frozen**): add a `private` copy and
   record the request under "Requested shared lemmas".
2. **Statement freeze.** No change to any existing declaration's name,
   signature, statement, hypotheses, or attribution. Docstring sketch
   paragraphs may gain an appended implementation note; flag it.
3. **Escalation.** If the target appears false or unprovable as stated, STOP,
   do not alter the statement, and record the obstruction under "Escalations".
4. No other sorry is touched. 5. Sketches stay. 6. Precise imports; keep the
   `set_option` headers.

## The target

```
theorem one_work_tape {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    (M : FinTM Γ) (f : List Γ → List Γ) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (Γ' : Type) (_ : Fintype Γ') (_ : DecidableEq Γ') (e : Γ ↪ Γ')
      (M' : FinTM Γ') (c : ℕ),
      M'.k = 1 ∧ M'.ComputesFunInTimeVia e f fun n => c * (T n + 1) ^ 2
```

The audited construction (docstring sketch + phase-2 findings, binding
corrections included):

- **`k = 0` case first and separately**: simulate `M` directly with one unused
  work tape (a lockstep embedding — `Turing.FinTM.leftCfg`-style reasoning
  from `Simulation.lean`, or a bespoke one-step commutation; no sweeps).
- **`k ≥ 1`**: the single work tape stores the `k` tapes interleaved — cell
  `j·k + i` of the simulated layout holds cell `j` of tape `i`, centered at
  `0` in both directions.
- **Alphabet (audit-mandated form)**: cells carry a *tagged payload*
  `Option Γ` — a marked **blank** must be representable, which a bare
  `Γ × flag` product misses (phase-2 audit, round 1) — together with a
  "head here" flag and zone-boundary tags; `Γ` embeds via `e` as an unmarked
  non-blank payload. Concretely something like
  `Γ' := Option Γ ⊕ (marker structure)` or a product with `Bool` flags —
  design it, but the *tagged `Option Γ` payload* requirement is fixed.
- **Simulated step = two sweeps**: left-to-right across the visited zone
  recording the `k` marked (head-here) symbols in the state; compute `M`'s
  transition from them; right-to-left updating the marked cells and moving
  the marks. Zone boundaries grow by at most one block per simulated step:
  after `t` steps the visited zone spans `O(k · (t + 1))` cells, so one
  simulated step costs `O(k · (T n + 1))` and the total is `c · (T n + 1)²`.
- **Input and output pass through unchanged**: `M'` reads the true input tape
  (via `e` on the embedded symbols — the hypothesis is `ComputesFunInTimeVia`,
  and so is the conclusion: inputs are `x.map e`-images) and emits `M`'s
  emissions mapped through `e`.
- The constant `c` is existential — be generous; no exact-step-count transfer
  from [AB09] is ever claimed (the `5kT²` of the book is *not* imported).

Proved in-repo exemplars of the invariant style (all epoch-1, audited):
`condTM`/`controlCfg_run`/`condTM_start` in `Composition.lean` (phase
decomposition, live administrative states), `counterTM` in
`TimeConstructible.lean` (work-tape shape functions like `counterTape` — you
will want an analogous "interleaved zone" shape function), `palTM` in
`Examples.lean` (two-head coordination), and the lockstep suites in
`Simulation.lean` and `StateRenaming.lean`. Expect the zone invariant to be
the real work: state it as a configuration-shape function (simulated tapes ↦
composite work tape + head positions + zone bounds) and prove one macro-step
lemma (one simulated step = one bounded burst of composite steps preserving
the shape), then induct.

## Out-of-scope sorries you will see (leave every one untouched)

`computesFunInTime_comp`, `exists_comp_partial` (Composition.lean);
`alphabet_reduction` (AlphabetReduction.lean); `nonnegative_heads`
(Bidirectional.lean); `oblivious_of_mem_DTIME` (Oblivious.lean);
`exists_effectiveMachineCode` (Encoding.lean); `universal`, `timed_universal`
(Universal.lean). After your batch, exactly these 8 sorry warnings remain.

## REPORT.md checklist

- [ ] Target filled, with how the proof relates to the sketch (and the `k = 0`
      path taken).
- [ ] New private declarations listed, for audit restatement.
- [ ] Requested shared lemmas — or "none".
- [ ] Escalations — or "none".
- [ ] Docstring appendices — or "none".
- [ ] Verification evidence: final sweep log attached, axiom log attached,
      zero `error:` lines, the exact 8 remaining sorry warnings.
- [ ] Diff touches only `SingleTape.lean`.

## Known pitfalls at this pin (hard-won — read before proving)

- `Function.update_of_ne` (no `update_noteq`); core `Nat.pow_pos`;
  `dite_eq_right/left` don't exist — `split <;> simp <;> omega`; after
  `cases hs : cfg.state` insert `dsimp only`; avoid bare `simp` against
  folded hypotheses (`initCfg` is `@[simp]`) — targeted `simp only`; `ring`
  needs `import Mathlib.Tactic.Ring`; `omega` can't see `Fin.val ⟨e, h⟩` or
  un-beta-reduced lambdas — normalize first; SignType names:
  `SignType.coe_one`, `neg_eq_neg_one`, `coe_neg_one`, `pos_eq_one`,
  `zero_eq_zero`; `moveInputPos_zero`, `moveInputPos_pos_of_ne_right`,
  `moveInputPos_neg_of_ne_left`, `moveInputPos_neg_val` (Simulation.lean).
- Work tapes are ℤ-indexed `Option Γ'` functions updated via
  `Function.update`; blanks are `none`. `Cfg.ext` proves configuration
  equality field by field; `Cfg.ext_zero_tapes` for `k = 0` machines.
- `ComputesFunInTimeVia e f T` means: on every input `x.map e`, halt within
  `T x.length` with output `(f x).map e` — mind that the *length* in the
  bound is of `x`, and `(x.map e).length = x.length` (`List.length_map`).
