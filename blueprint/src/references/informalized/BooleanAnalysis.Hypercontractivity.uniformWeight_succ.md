<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Decomposition.lean :: uniformWeight_succ -->
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

**Used in.** `BooleanAnalysis.Hypercontractivity.expect_succ_eq`, `BooleanAnalysis.Hypercontractivity.fourierCoeff_avgLast`, `BooleanAnalysis.Hypercontractivity.fourierCoeff_diffLast` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Decomposition.lean`; `BooleanAnalysis.Hypercontractivity.qth_moment_decomp` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/EvenMoments.lean`; `BooleanAnalysis.Hypercontractivity.expect_succ_eq_iterated`, `BooleanAnalysis.Hypercontractivity.weighted_sum_succ_decomp` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/General/Kernel.lean`.
