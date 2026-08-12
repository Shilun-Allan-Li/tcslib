<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: influence_entropy_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The influence entropy sum is nonnegative

**Claim.** If `0 < totalInfluence f`, then
`0 ≤ ∑ i, (influence i f / totalInfluence f) * Real.log (totalInfluence f / influence i f)`.
Reading `Inf_i[f]/I[f]` as a probability distribution over coordinates, this is
nonnegativity of its entropy.

**Proof.** `Finset.sum_nonneg`, then per coordinate:

- `influence i f ≥ 0` from `influence_eq_sum_fourier` (`Finset.sum_nonneg` +
  `positivity`).
- If `influence i f = 0` the term is `0` by `simp` (Lean's conventions make the
  leading factor `0`).
- Otherwise `0 < influence i f`, and `influence i f ≤ totalInfluence f` by
  `Finset.single_le_sum` over the nonnegative influences; hence
  `1 ≤ totalInfluence f / influence i f` and the logarithm is nonnegative
  (`Real.log_nonneg ((one_le_div hi_pos).mpr hle)`). `mul_nonneg` finishes. ∎

**Note.** Dead declaration: nothing in the repository calls
`influence_entropy_nonneg`. Its header comment marks it as a building block for
the full KKL proof, whose hard case in `KKL_balanced` is still **`sorry`**
(KKL.lean:618); since the lemma is unused, it contributes nothing toward closing
that gap.
