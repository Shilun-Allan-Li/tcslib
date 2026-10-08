<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: uniformWeight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The uniform weight on the Boolean cube

**Definition.** For `n : ℕ`,

```
uniformWeight n = (2 : ℝ)⁻¹ ^ n
```

the mass `2⁻ⁿ` that the uniform probability measure on `{0,1}ⁿ` puts on each of
its `2ⁿ` points. It is a plain `noncomputable def` with no proof content.

**Remark.** Every averaging notion in the file is built on it: `expect f` is
`uniformWeight n * ∑ x, f x`, and `innerProduct`, `l2Norm`, `fourierCoeff`,
`influence` and `l2DistSq` all bottom out here. Note the deliberate spelling
`(2 : ℝ)⁻¹ ^ n` rather than `(2 ^ n)⁻¹` — proofs throughout exploit it by
pairing with `← mul_pow` and `inv_mul_cancel₀`, which is how the normalisation
cancels against the `2ⁿ`-point sum (`innerProduct_self_pm_one`,
`influence_chi`).

**Used in.** The uniform weight occurs throughout the Fourier and hypercontractivity
developments, often when expanding an expectation or inner product into a finite sum.
The cube calculations live in `Hypercontractivity/Cube/Decomposition.lean`,
`Hypercontractivity/Cube/FourthMoment.lean`, `Hypercontractivity/Cube/EvenMoments.lean`,
and `Hypercontractivity/Cube/General/Kernel.lean`.
