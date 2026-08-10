<!-- generated-by: proofmatch informalization (not_in_text) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: sum_prod_subset_eq_prod_one_add -->
<!-- origin: boolean-ch01-fourier-blr run cdca27e1b5fd verdict not_in_text (0.78) -->

# Sum over all subsets equals a product of `1 + c i`

**Claim.** For any real vector `c : Fin n → ℝ`, summing the monomial
`∏ i ∈ S, c i` over *all* `S : Finset (Fin n)` gives
`∑ S, ∏ i ∈ S, c i = ∏ i : Fin n, (1 + c i)`.

**Proof.**

1. `rw [Finset.prod_one_add Finset.univ]` turns the right-hand side into
   `∑ t ∈ Finset.univ.powerset, ∏ i ∈ t, c i` — the Mathlib form of the
   identity, where the sum ranges over the powerset of `univ` rather than over
   the type `Finset (Fin n)`.
2. The two index sets are reconciled by `Finset.sum_nbij id`, with the four
   obligations discharged as: membership (`Finset.mem_powerset.mpr
   (Finset.subset_univ t)`), injectivity (`id`), surjectivity
   (`⟨t, Finset.mem_univ t, rfl⟩`), and equality of summands (`rfl`).

**Remark.** A private plumbing lemma: all the mathematics is `Finset.prod_one_add`,
and the work here is the reindexing. It feeds `sum_chiS_mul_eq`, the Walsh
completeness kernel behind `walsh_expansion`.
