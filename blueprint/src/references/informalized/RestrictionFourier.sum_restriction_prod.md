<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RestrictionFourier.lean :: sum_restriction_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Sums over all restrictions of coordinatewise products factor

**Claim.** For any `h : Fin n → Option Bool → ℝ`,

`∑ ρ : Restriction n, ∏ i : Fin n, h i (ρ i) = ∏ i : Fin n, ∑ v : Option Bool, h i v`.

Summing a coordinatewise product over all `3ⁿ` restrictions equals the product
of the `n` three-term coordinate sums.

**Proof.** Two rewrites.

1. `Finset.prod_univ_sum` expands the right-hand product of sums into a sum over
   `Fintype.piFinset (fun _ => univ)` of the pointwise products.
2. `Fintype.piFinset_univ` identifies that index finset with
   `Finset.univ : Finset (Fin n → Option Bool)`, which is `Restriction n` by
   definition (`abbrev`), closing the goal.

**Remark.** This is the plain distributivity fact; no probability enters. The
weighted version is `sum_bernoulli_prod`, obtained by absorbing
`bernoulliRestrWeight` into each factor.

**Used in.** `sum_bernoulli_prod`.
