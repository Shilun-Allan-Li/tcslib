<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: influential_coords_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# At most I[f]/τ coordinates are τ-influential

**Claim.** For `τ > 0`, `((influentialCoords f τ).card : ℝ) ≤ totalInfluence f / τ`,
where `influentialCoords f τ = {i | τ ≤ influence i f}`.

**Proof.** Clear the denominator with `le_div_iff₀ hτ`, then a three-step `calc`:

- `card · τ = card • τ` (`nsmul_eq_mul`);
- `card • τ ≤ ∑ i ∈ influentialCoords f τ, influence i f` by
  `Finset.card_nsmul_le_sum` — every member of the filter satisfies
  `τ ≤ influence i f`, which is `(Finset.mem_filter.mp hi).2`;
- `∑ i ∈ influentialCoords f τ, influence i f ≤ totalInfluence f` by
  `Finset.sum_le_univ_sum_of_nonneg`, since each influence is nonnegative:
  `influence_eq_sum_fourier` presents it as a sum of guarded squares, closed by
  `Finset.sum_nonneg` and `positivity`. ∎

**Why it matters.** This is the counting half of `friedgut_junta`: with
`τ = ε/(4n)` it bounds the junta's arity by `4·n·I[f]/ε`, which is exactly the
size bound in the theorem statement.

**Used in.** `friedgut_junta` (the `hjunta` step). No call sites outside
`BooleanAnalysis/KKL.lean`.
