# Ch2 fill campaign — Epoch 1, Batch D: the formula mathematics

## Context

You are filling Lean 4 proofs in **tcslib**'s formalization of Arora–Barak,
*Computational Complexity* (2009), Chapter 2 (statement layer complete, four
audit gates closed — `audits/ch2-phase*`). This batch is **pure
mathematics — no machines**: the CNF evaluation-congruence bridge, CNF
universality (Claim 2.13), the serializer/parser round trip and its variable
bound, and the De Morgan dual layer. The carrier throughout is Lean core's
`Std.Sat.CNF ℕ`, with the campaign's layer in the `Std.Sat.CNF` namespace
(`Satisfiable`, `numVars`, `WidthAtMost`, the serialization grammar, `dual`,
`evalDNF`). Everything is structural induction over lists plus the
fuel-indexed parsers.

## Repository, branch, deliverable

- Repo: `https://github.com/Shilun-Allan-Li/tcslib`. Base: branch
  `complexity/arora-barak-ch1`, **not** `main`.
- Branch `fill/ch2-e1-D`. **Delivery by zip, not PR** (`workflow.md` §4):
  `fill-ch2-e1-D.zip` with `REPORT.md`, full modified sources,
  `git format-patch` series against the base, a git bundle, the final sweep
  log, the axiom-print log, and `SHA256SUMS`.
- Read first: `policy.md`; `workflow.md` §4; `AroraBarakChapter2Plan.md` §4
  (you are batch 1D); the grammar documentation at the top of
  `Formulas/CNFEncoding.lean` (the unary LL(1) format: a literal is
  `List.replicate (v+1) true ++ [false, b]`, a clause its literals followed
  by `false`, a formula `true ::` its clauses followed by `false`; `parse`
  supplies `x.length` as fuel; the fallback is `[]`);
  `audits/ch2-phase3-findings.md` for the serialization surface's audit and
  `audits/ch2-phase4-findings.md` note 6 for the DNF layer.

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/Formulas/CNF.lean` (2 targets)
- `TCSlib/Complexity/Formulas/CNFEncoding.lean` (3 targets)
- `TCSlib/Complexity/Formulas/DNF.lean` (2 targets)

## Environment and verification

- Toolchain pinned (Lean 4 v4.25.0); setup: `lake exe cache get`.
  **Never run `lake build`.**
- Bootstrap once:
  `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`.
- Iterate: `bash scripts/lean_check_tree.sh TCSlib/Complexity/Formulas/CNF`
  (resp. `…/CNFEncoding`, `…/DNF`) per edit, then the later modules in the
  order list (`SAT.lean`, `TMSAT.lean`, `Tautology.lean`, `CookLevin/*`
  import these — budget the downstream re-checks).
- Final: full 53-module sweep, zero `error:` lines. Axiom prints per filled
  target; expected exactly `[propext, Classical.choice, Quot.sound]` — no
  out-of-batch dependencies; any `sorryAx` is a defect.

## Ground rules (binding)

1. **File ownership.** Only the three owned files. Helpers `private`;
   shared wishes under "Requested shared lemmas" with a local `private`
   copy; every new declaration listed in `REPORT.md` (the audit
   blind-restates them). Expect several `private` strengthenings here —
   that is the intended shape, list them all.
2. **Statement freeze.** No renames, re-signatures, restatements, or
   attribution edits; sketch appendices allowed, flagged.
3. **Escalation** over alteration, always.
4. No touching sorries outside the target list. 5. Docstrings stay.
6. Precise imports; keep `set_option` headers.

## Targets (suggested order; the two files' tracks are independent)

**CNF.lean track:**

1. **`eval_congr_of_lt_numVars`** (CNF.lean:118). The one real step:
   membership-to-fold — `Std.Sat.CNF.Mem v φ → v < φ.numVars` by induction
   on the flattened clause list (each mentioned `v` contributes `v + 1` to
   the `foldr max`). Then the upstream `Std.Sat.CNF.eval_congr` closes it.
2. **`exists_cnf_boolFun`** (CNF.lean:142). The audited construction is in
   the docstring: one clause `C_v = [(i, !(v i)) : i < ℓ]` per falsifying
   `v`, e.g. over `Finset.univ.filter (fun v => f v = false)` on the
   `Fintype` of `Fin ℓ → Bool`. Key pointwise fact: `C_v.eval a = false` iff
   `a` agrees with `v` below `ℓ`. Mind the stated edge cases at `ℓ = 0`
   (`[]` vs `[[]]`) and keep the four conjuncts (`numVars ≤ ℓ`, clause
   count, width, evaluation) as separate `private` lemmas if the single
   proof grows.

**CNFEncoding.lean track (sequential):**

3. **`parse_serialize`** (CNFEncoding.lean:182). The batch's center of
   gravity. Follow the sketch's four strengthenings *verbatim* — (i)
   `takeTrues` on `replicate (k+1) true ++ false :: r`; (ii) the
   suffix-carrying `parseClause` round trip for **any fuel ≥
   `(serializeClause C).length`** (each literal consumes ≥ 3 bits, so the
   fuel decrement stays adequate — do the fuel accounting as an explicit
   hypothesis, not an afterthought); (iii) the clause-list analogue (≥ 2
   bits per clause); (iv) instantiate at the empty suffix with fuel
   `(serialize φ).length`. Resist weakening to exact-fuel statements — the
   `≥` form is what makes the induction go through.
4. **`decode_serialize`** (CNFEncoding.lean:190) — target 3 plus
   `Option.getD`.
5. **`numVars_decode_le`** (CNFEncoding.lean:206). Strengthen over the
   parsing functions: on success with remainder `r`, the consumed prefix
   has length `y.length - r.length` and every produced literal `(k, b)`
   consumed its own `k + 1` `true`s within it, so `k + 1 ≤ y.length`; the
   `foldr max` is bounded termwise. Fallback case: `numVars [] = 0`.

**DNF.lean track:**

6. **`evalDNF_dual`** (DNF.lean:90). Induction on the clause list;
   literal level is a two-boolean case check (`a v == !b = !(a v == b)`);
   push `Bool.not_and`/`Bool.not_or` through `List.any`/`List.all`
   (`List.any_map`, `List.all_map`, and the pin's spelling of
   `Bool.not_all` — check before relying on it).
7. **`dnfTautology_dual_iff`** (DNF.lean:101) — pointwise from target 6;
   "every `a` satisfies the dual" ↔ "no `a` satisfies `φ`" ↔
   `¬Satisfiable`.

## Out-of-scope sorries you will see (leave untouched)

All of batches 1A/1B/1C (`PolyTime`, `Reductions`, `NTIME`,
`TuringMachine/Nondeterministic`, `CoNP`, `NP`, `EXP`) and the E2–E4
surface — in particular `SAT.lean`/`TMSAT.lean`/`Tautology.lean`, which
import your files and whose sorries you will see in downstream re-checks.

## REPORT.md checklist

- [ ] Targets filled (7), one line each vs the sketch — note where the
      fuel-strengthening form differed from the sketch, if anywhere.
- [ ] New declarations listed (public and private) — the strengthened
      parser lemmas especially, for audit restatement.
- [ ] Requested shared lemmas — or "none". Escalations — or "none".
- [ ] Final sweep log tail (zero `error:` lines) + axiom-print log
      (standard triple only).
- [ ] Diff touches only the three owned files.

## Known pitfalls at this pin

- The campaign layer lives in the `Std.Sat.CNF` namespace: `numVars`,
  `Satisfiable`, `WidthAtMost`, `serialize`, `parse`, `decode`, `dual`,
  `evalDNF` all resolve under it; upstream core gives `eval`, `Mem`,
  `relabel`.
- Fuel is a totalization device (`parseClause : ℕ → …` is structural on
  fuel): never induct on the string where the sketch inducts on structure
  with a fuel *bound* — the `≥`-fuel form is load-bearing.
- `List.replicate` lemmas: `length_replicate`, `replicate_succ`; watch
  `replicate (k+1)` vs `replicate k` off-by-ones at the `takeTrues` base.
- `Bool` equality: `==` vs `=` — `beq_iff_eq` bridges; two-boolean cases
  close with `decide` or `cases … <;> rfl`.
- Avoid bare `simp` with folded forms; prefer `simp only`.
  `omega` needs beta-reduced, non-`Fin`-projection goals.
- `Fintype (Fin ℓ → Bool)` card: `Fintype.card_fun` with
  `Fintype.card_bool` gives `2 ^ ℓ`; `Finset.card_filter_le` bounds the
  clause count.
