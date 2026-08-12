<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ArrowTheorem.lean :: prod_finset_eq_prod_univ_ite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A product over a subset as a product over all of `Fin n`

**Claim.** For `A : Finset (Fin n)` and `g : Fin n → ℝ`,

`∏ j ∈ A, g j = ∏ j : Fin n, if j ∈ A then g j else 1`.

Extending the index set to the whole of `Fin n` and padding the new factors with
the multiplicative unit `1` does not change the product.

**Proof.** One line: `rw [← Finset.prod_filter]; congr 1; simp`.

1. `Finset.prod_filter` reads `∏ x ∈ s.filter p, f x = ∏ x ∈ s, if p x then f x
   else 1`; rewriting it backwards turns the right-hand side into
   `∏ j ∈ Finset.univ.filter (· ∈ A), g j`.
2. `congr 1` reduces the goal to the index sets agreeing,
   `A = Finset.univ.filter (· ∈ A)`, which `simp` closes.

**Remark.** A `private` re-indexing helper, used only to make two products
*share* an index set. In `profile_kernel_gen` the characters `chiS S` and
`chiS T` are products over the different sets `S` and `T`; after applying this
lemma to each, both range over `Fin n`, so `Finset.prod_mul_distrib` can merge
them into a single product of per-coordinate factors. That single product is what
`Fintype.prod_sum` then trades against the profile sum, turning `∑_p ∏_i` into
`∏_i ∑_k` — the step that realizes voter independence and reduces the whole
kernel to the per-voter case analysis on `i ∈ S`, `i ∈ T`.

Minor stylistic note: the lemma re-binds `{n : ℕ}` even though the file already
has `variable {n : ℕ}` in scope; harmless, just redundant.

**Used in.** Twice inside `profile_kernel_gen` (instantiated at `S` and at `T`)
via `simp_rw`, and nowhere else.
