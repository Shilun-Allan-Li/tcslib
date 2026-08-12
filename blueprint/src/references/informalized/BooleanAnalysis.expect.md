<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: expect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Uniform expectation on the hypercube

**Definition.** `expect (f : BooleanFunc n) : ℝ := uniformWeight n * ∑ x :
BoolCube n, f x`, where `uniformWeight n = (2 : ℝ)⁻¹ ^ n`. That is,
`𝔼[f] = 2⁻ⁿ · ∑_x f(x)`: the plain average of `f` over all `2ⁿ` points.

- It is a *finite sum scaled by a constant*, not a measure-theoretic integral —
  which is why the definition is unconditional and needs no integrability
  side-goals. `moment_eq_expect` supplies the bridge: for any probability
  measure `P` whose atoms all have mass `uniformWeight n`,
  `ProbabilityTheory.moment f p P = expect (fun x ↦ f x ^ p)`, via
  `MeasureTheory.integral_fintype` and `Finset.mul_sum`.
- Everything metric is layered on top: `innerProduct f g = expect (fun x ↦ f x *
  g x)`, then `l2Norm f = Real.sqrt (innerProduct f f)`, `fourierCoeff f S =
  innerProduct f (chiS S)`, and `influence i f = expect (fun x ↦ (f x - f
  (flipBit x i)) ^ 2 / 4)`.

**Remark.** The normalisation is written `(2⁻¹) ^ n`, not `(2 ^ n)⁻¹`. Unfolding
therefore leaves the literal `2⁻¹ ^ n`, and cancelling it against
`Fintype.card (BoolCube n) = 2 ^ n` takes `← mul_pow` followed by
`inv_mul_cancel₀` and `one_pow` (the closing lines of
`innerProduct_self_pm_one`) rather than a single `field_simp`.

**Used in.** Pervasive — `fourierCoeff_empty` identifies `f̂(∅) = expect f`, and
`expect`/`uniformWeight` are unfolded together in essentially every quantitative
proof of the layer (`parseval`, `noiseOp_fourier`, `fourierCoeff_odd_even`,
`innerProduct_self_pm_one`).
