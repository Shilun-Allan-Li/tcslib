# Existing Layered.auxCount_add_one proof draft

Status: inspected exact-header replacement; no native elaboration claimed. No live source
edits or Lean, lake, build, or Git commands. No helper, new import, or admission added.

## Deliverable

`LayeredAuxCountAddOne.lean.inc` replaces only the existing admitted body of
`auxCount_add_one`, currently `PartialGarbling/Layered.lean:149`. A Python assertion
matched the entire current theorem header through `:=`. One tactic block, no admitted
terms, maximum line width 75 columns.

```lean
theorem auxCount_add_one (l d : ℕ) : auxCount l d + 1 = nodeCount l d := by
  rw [auxCount_eq, nodeCount_eq, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, pow_zero]
  exact Nat.add_comm _ _
```

The two published count readers expose the sums. The existing `Fin.sum_univ_succ`
separates the depth-zero term of nodeCount from all positive-depth terms. The zero term
is 1; `Fin.val_succ` identifies the remaining exponent with the auxCount exponent.
Commutativity of natural addition aligns the order. This directly consumes the generic
finite-sum theorem, without induction or another finite-sum lemma. Degree zero is
handled by the same identity, so no nonempty/positive-degree assumption is added.

## Exact dependencies

- `Layered.lean:120`: `auxCount_eq`, the sum of `(l+1)^(k.val+1)` over `Fin d`.
- `Layered.lean:113`: `nodeCount_eq`, the sum of `(l+1)^k.val` over `Fin (d+1)`.
- `Mathlib/Algebra/BigOperators/Fin.lean:72`: the published `to_additive` counterpart
  of `Fin.prod_univ_succ` is `Fin.sum_univ_succ`:
  `sum over Fin (d+1) of f = f 0 + sum over Fin d of (fun i => f i.succ)`.
  Its use with the same `Fin.val_zero`, `Fin.val_succ`, and `pow_zero` readers already
  occurs in that Mathlib file at line 581.
- Pinned core `Init/Data/Fin/Lemmas.lean:225`: `Fin.val_zero`.
- Same file :392: `Fin.val_succ`.
- Core/Mathlib `pow_zero` and `Nat.add_comm`.

No algorithm/count definition or generated defining equation is explicitly unfolded.
There are no admitted dependencies. The existing Classes import already brings
Mathlib.Algebra.BigOperators.Fin into the current import closure.

## Actual name and shape searches

Working tree:
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

```sh
sed -n '105,150p' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/PartialGarbling/Layered.lean
sed -n '46,82p' .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean
rg -n 'auxCount_add_one|auxCount_eq|nodeCount_eq|sum_univ_succ.*pow|sum_univ_succ.*succ|Fin\.sum_univ_succ' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption TCSlib/Combinatorics .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean | head -60
rg -n 'val_succ|coe_zero' /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init/Data/Fin/Lemmas.lean | head -20
rg -n 'val_zero|val_succ|sum_univ_succ|prod_univ_succ' /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init/Data/Fin/Lemmas.lean .lake/packages/mathlib/Mathlib/Algebra/BigOperators/Fin.lean | head -28
rg -n 'auxCount.*\+ 1|\+ 1 = nodeCount|nodeCount.*auxCount' TCSlib .lake/packages/mathlib/Mathlib | head -25
rg -n 'sum_univ_succ, Fin.val_zero, Fin.val_succ|sum_univ_succ.*pow_zero|sum_univ_succ.*Nat.add_comm' TCSlib .lake/packages/mathlib/Mathlib | head -25
```

The first broad shape search included a nonexistent `TCSlib/Combinatorics` path and
reported that IO error, while still returning the relevant current Layered declarations
and the Mathlib sum-splitting consumer. Subsequent whole-library searches confirmed
there is no other source-specific count theorem to reuse; the generic public finite-sum
reader already suffices. No new helper was considered necessary.

## Verification limits and findings

Static header, width, single-tactic-block, and absence-of-admission checks passed.
Native elaboration and admission/declaration inventory refresh are for the parent.
No false/unattainable statement or missing public reader was found.
