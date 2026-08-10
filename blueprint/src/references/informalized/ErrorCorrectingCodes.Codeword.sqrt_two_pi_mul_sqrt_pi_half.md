<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Entropy.lean :: sqrt_two_pi_mul_sqrt_pi_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A square-root identity for the Stirling constant

**Claim.** For `0 ≤ n : ℝ`,
`√(2πn) · √(π/2) · √n = π·n`. A `private` computational helper.

**Proof.** Three rewrites.

1. `Real.sqrt_mul` (twice, backwards) merges the three roots into one:
   `√(2πn · (π/2) · n)`; the nonnegativity side goals are `positivity`.
2. `2πn · (π/2) · n = (π·n)²` by `ring_nf`, supplied as a `show`.
3. `Real.sqrt_sq` (with `0 ≤ π·n` by `positivity`) finishes. ∎

**Used in.** `stirling_comb_bound`: it is the step that trades the Stirling prefactor
`√(2πn)` against the `√(π/2)·√n` appearing in the denominator of the target ratio,
leaving the clean factor `π·n`.
