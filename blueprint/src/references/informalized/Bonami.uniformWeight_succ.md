<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: uniformWeight_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Uniform point mass halves when a coordinate is added

**Claim.** For every `n : ℕ`,

```
uniformWeight (n + 1) = uniformWeight n / 2
```

where `uniformWeight n = (2 : ℝ)⁻¹ ^ n` is the uniform point mass on
`{0,1}^n`.

**Proof.** `simp [uniformWeight, pow_succ]` unfolds the definition and rewrites
`(2⁻¹) ^ (n+1)` as `(2⁻¹) ^ n * 2⁻¹`; `ring` matches that against
`(2⁻¹) ^ n / 2`.

**Used in.** Paired with `sum_boolCube_succ` in every last-coordinate
decomposition of an expectation: `fourierCoeff_avgLast`,
`fourierCoeff_diffLast`, `expect_succ_eq`, and `degree_diffLast`.
