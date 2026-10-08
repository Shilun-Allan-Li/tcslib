<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Decomposition.lean :: avgLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Averaging a Boolean function over its last coordinate

**Definition.** For `f : BooleanFunc (n + 1)` (a real-valued function on the
cube `{0,1}^{n+1}`), `avgLast f : BooleanFunc n` is the function on `{0,1}^n`

```
avgLast f x = (restrictLast f false x + restrictLast f true x) / 2
```

i.e. the average of the two restrictions `f (Fin.snoc x false)` and
`f (Fin.snoc x true)` obtained by fixing the last coordinate. It is the
"even part" of `f` in the last variable; its counterpart is
`diffLast`, the half-difference. The declaration is a plain
`noncomputable def` with no proof content.

**Remark.** The pair `(avgLast f, diffLast f)` is exactly the decomposition
`f (Fin.snoc x b) = avgLast f x + boolToSign b · diffLast f x`, recorded in
`restrictLast_false_eq` and `restrictLast_true_eq`, and on the Fourier side by
`fourierCoeff_avgLast` (`avgLast f` collects the coefficients of `f` at
frequencies avoiding the last coordinate).

**Used in.** `BooleanAnalysis.Hypercontractivity.bonami_expect` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Bonami.lean`; `BooleanAnalysis.Hypercontractivity.degree_avgLast`, `BooleanAnalysis.Hypercontractivity.fourierCoeff_avgLast`, `BooleanAnalysis.Hypercontractivity.fourth_moment_decomp`, `BooleanAnalysis.Hypercontractivity.restrictLast_false_eq`, `BooleanAnalysis.Hypercontractivity.restrictLast_true_eq`, `BooleanAnalysis.Hypercontractivity.second_moment_decomp` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Decomposition.lean`; `BooleanAnalysis.Hypercontractivity.hypercontractivity_2_2k`, `BooleanAnalysis.Hypercontractivity.noise_qth_moment_decomp`, `BooleanAnalysis.Hypercontractivity.qth_moment_decomp` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/EvenMoments.lean`; `BooleanAnalysis.Hypercontractivity.fourth_moment_noise_decomp`, `BooleanAnalysis.Hypercontractivity.hypercontractivity_2_4`, `BooleanAnalysis.Hypercontractivity.noiseOp_snoc` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/FourthMoment.lean`; `BooleanAnalysis.Hypercontractivity.fourierCoeff_avgLast_restrictions`, `BooleanAnalysis.Hypercontractivity.noiseOp_snoc_slice` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/Basic.lean`.
