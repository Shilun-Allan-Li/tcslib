<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: avgLast -->
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

**Used in.** The induction on `n` in `bonami_expect` (via
`fourth_moment_decomp`, `second_moment_decomp`, `degree_avgLast`), and in
`SimpleHypercontractivity` (`noiseOp_snoc`,
`fourth_moment_noise_decomp`).
