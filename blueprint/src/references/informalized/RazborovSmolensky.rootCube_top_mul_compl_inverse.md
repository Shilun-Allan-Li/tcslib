<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: rootCube_top_mul_compl_inverse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The top monomial times an inverted complement monomial

**Claim.** Let `ω ≠ 0`, `x : rootCube ω n` and `s : Finset (Fin n)`. Then
`(∏ i, x.1 i) * ∏ i ∈ sᶜ, (x.1 i)⁻¹ = ∏ i ∈ s, x.1 i`.

**Proof.** Two auxiliary facts, then a `calc` chain.

* `hsplit`: `Finset.prod_compl_mul_prod` gives
  `(∏ i ∈ sᶜ, x.1 i) * (∏ i ∈ s, x.1 i) = ∏ i, x.1 i`, transported by `simpa`.
* `hcancel`: `(∏ i ∈ sᶜ, x.1 i) * (∏ i ∈ sᶜ, (x.1 i)⁻¹) = 1`. Combine the two products
  with `rw [← Finset.prod_mul_distrib]`, then `Finset.prod_eq_one` reduces to the factorwise
  identity `mul_inv_cancel₀`, whose side condition is `rootCube_coord_ne_zero`.
* The `calc` rewrites the top product by `hsplit`, reassociates with `ring`, applies
  `hcancel` under `congrArg`, and finishes with `simp` (`· * 1`).

**Remark.** This is the algebraic core of the split: a high-degree monomial `∏_{i ∈ s} x i`
factors as the top monomial times a *low-degree* monomial in the inverted coordinates,
since `|sᶜ| ≤ n / 2` when `|s| > n / 2`.
