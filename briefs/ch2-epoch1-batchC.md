# Ch2 fill campaign — Epoch 1, Batch C: complementation and the easy inclusions

## Context

You are filling Lean 4 proofs in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity* (2009), Chapter 2 (statement layer complete, four
audit gates closed — `audits/ch2-phase*`). This batch delivers `P ⊆ NP` with
empty certificates, closure of `P` under complement (the one small machine
assembly here — a Boolean postprocessor, both halves already proved in
Chapter 1), the ∀-certificate characterization of `coNP`,
`P ⊆ NP ∩ coNP`, `P = NP → NP = coNP`, and `P ⊆ EXP`. Proved
infrastructure: `Turing.FinTM.computesFunInTime_ifEq`,
`computesFunInTime_comp` (timed), `Complexity.mem_P_iff`,
`mem_P_of_dtime_le`, `DTIME.mono`.

## Repository, branch, deliverable

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`. Base: branch
  `complexity/arora-barak-ch1`, **not** `main`.
- Branch `fill/ch2-e1-C`. **Delivery by zip, not PR** (`workflow.md` §4):
  `fill-ch2-e1-C.zip` with `REPORT.md`, full modified sources,
  `git format-patch` series against the base, a git bundle, the final sweep
  log, the axiom-print log, and `SHA256SUMS`.
- Read first: `policy.md`; `workflow.md` §4; `AroraBarakChapter2Plan.md` §4
  (you are batch 1C); `audits/ch2-phase1-findings.md` findings 1, 2, 4, 10
  (explicit length formulas; the `P ⊆ NP` edge cases; timed composition
  only; `compl_mem_P`'s certification as a flagged statement).

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/ClassNP/CoNP.lean` (4 targets)
- `TCSlib/Complexity/ClassNP/NP.lean` (1 target: `P_subset_NP` only)
- `TCSlib/Complexity/ClassNP/EXP.lean` (1 target: `P_subset_EXP` only)

## Environment and verification

- Toolchain pinned (Lean 4 v4.25.0); setup: `lake exe cache get`.
  **Never run `lake build`.**
- Bootstrap once:
  `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`.
- Iterate: `bash scripts/lean_check_tree.sh TCSlib/Complexity/ClassNP/NP`
  (resp. `…/CoNP`, `…/EXP`) per edit, then the later modules in the order
  list. Final: full 53-module sweep, zero `error:` lines.
- Axiom prints per filled target; expected exactly
  `[propext, Classical.choice, Quot.sound]` — this batch has **no**
  out-of-batch sorried dependencies; any `sorryAx` is a defect.

## Ground rules (binding)

1. **File ownership.** Only the three owned files, and in `NP.lean` and
   `EXP.lean` only the one named target each — the other sorries there
   (`mem_NP_iff_exists_length_le`; `NP_subset_EXP`, `EXP_subset_NEXP`)
   belong to epochs 2/3. Helpers `private`; shared wishes under "Requested
   shared lemmas" with a local `private` copy; all new declarations listed.
2. **Statement freeze.** No renames, re-signatures, restatements, or
   attribution edits; sketch appendices allowed, flagged.
3. **Escalation** over alteration, always.
4. No touching sorries outside the target list. 5. Docstrings stay.
6. Precise imports; keep `set_option` headers.

## Targets (fill in this order)

1. **`P_subset_NP`** (NP.lean:93). `C = 0, c = 0, V = L`: the only length-`0`
   certificate is `[]` and `x ++ [] = x`. The audit's edge-case table
   (`L = ∅`, `L = univ`, `x = []`) all fall to the same computation; keep the
   equivalence `Iff.rfl`-adjacent rather than re-proving membership.
2. **`compl_mem_P`** (CoNP.lean:72). The batch's one assembly: decider of
   `L` (via `mem_P_iff`, output exactly `[Turing.MultiTapeTM.indicator L x]`)
   postcomposed with `computesFunInTime_ifEq [true] [false] [true]` through
   the **timed** `computesFunInTime_comp` (phase-1 finding 4: the untimed
   `exists_comp_partial` is forbidden). Return through `mem_P_of_dtime_le`.
   The budget arithmetic mirrors batch 1A's `comp` ledger at tiny scale.
3. **`mem_coNP_iff_forall`** (CoNP.lean:87). Purely logical: negate the
   exact-length existential of `NP`-membership for `Lᶜ`; the verifier
   complement is target 2. Both directions reuse the same `C, c`. No
   certificate-length computation (audit finding table).
4. **`P_subset_NP_inter_coNP`** (CoNP.lean:97) — target 1 + target 2 (via
   `Lᶜ ∈ P ⊆ NP`).
5. **`NP_eq_coNP_of_P_eq_NP`** (CoNP.lean:105) — set algebra over target 2,
   rewriting along `h : P = NP` in both directions.
6. **`P_subset_EXP`** (EXP.lean:81). Pure budget arithmetic:
   `n^c + 1 ≤ 2 · 2^(n^c)` from `n^c < 2^(n^c)` (`Nat.lt_two_pow` at this
   pin — check the exact spelling), then `DTIME.mono` and the
   constant-absorbing `DTIME` definition. No machine.

## Out-of-scope sorries you will see (leave untouched)

In your own files: `mem_NP_iff_exists_length_le` (NP.lean — epoch 2C),
`NP_subset_EXP` (EXP.lean — epoch 2A), `EXP_subset_NEXP` (EXP.lean — epoch
3A). Elsewhere: all of batches 1A/1B/1D and the E2–E4 surface. If a proof
seems to need one of them, escalate.

## REPORT.md checklist

- [ ] Targets filled (6), one line each vs the sketch.
- [ ] New declarations listed (public and private).
- [ ] Requested shared lemmas — or "none". Escalations — or "none".
- [ ] Final sweep log tail (zero `error:` lines) + axiom-print log (standard
      triple only).
- [ ] Diff touches only the three owned files, and only the named targets'
      proofs within them.

## Known pitfalls at this pin

- `Set` complement on `Language Bool`: `Lᶜ` membership unfolds with
  `Set.mem_compl_iff`; `Language Bool` is literally `Set (List Bool)`.
- Avoid bare `simp` with folded forms; prefer `simp only`.
- `Function.update_of_ne`; core `Nat.pow_pos`;
  `dite_eq_right`/`dite_eq_left` do not exist (`split <;> simp <;> omega`).
- `ring` needs `import Mathlib.Tactic.Ring`; `omega` needs normalized
  (beta-reduced, non-`Fin`-projection) goals.
- Destructure `ComputesInTime` after
  `simp only [FinTM.ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace]` as
  `⟨s, hhalt, hout, -⟩`.
- The indicator contract: deciders output exactly `[true]`/`[false]`
  (singleton lists), never bare booleans — equivalences go through
  `Turing.MultiTapeTM.indicator`.
