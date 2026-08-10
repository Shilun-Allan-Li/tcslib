<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean :: paley_zygmund_ineq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Paley–Zygmund inequality

**Claim.** Let `μ` be a probability measure on `Ω` and `Z : Ω → ℝ` measurable,
almost everywhere nonnegative, with `Z` and `Z²` integrable and
`0 < moment Z 1 μ`. Then for every `θ` with `0 ≤ θ ≤ 1`,

```
(1 - θ)^2 * (moment Z 1 μ)^2 / moment Z 2 μ ≤ (μ {ω | θ * moment Z 1 μ < Z ω}).toReal
```

i.e. `P[Z > θ·E Z] ≥ (1 − θ)² (E Z)² / E[Z²]`.

**Proof.** Write `A = {ω | θ * ∫ Z < Z ω}`, measurable by
`measurableSet_lt`.

1. Split the mean: `integral_add_compl` gives
   `∫ Z = ∫_A Z + ∫_{Aᶜ} Z` (`h_split`).
2. Bound the complement: on `Aᶜ` we have `Z ω ≤ θ ∫ Z` (`not_lt.mp` under
   `ae_restrict_iff'`), so `integral_mono_ae` plus `integral_const` gives
   `∫_{Aᶜ} Z ≤ (θ ∫ Z) · μ(Aᶜ) ≤ θ ∫ Z`, using `prob_le_one` and
   `ENNReal.toReal_mono` for `μ(Aᶜ) ≤ 1`.
3. Hence `(1 − θ) ∫ Z ≤ ∫_A Z` (`linarith` on steps 1–2).
4. Cauchy–Schwarz on `A`:
   `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` with `p = q = 2` applied
   to `Z · 1` (membership via `memLp_two_iff_integrable_sq`, `memLp_const`),
   then squaring and cancelling the `1/2` exponents (`Real.rpow_mul`), yields
   `(∫_A Z)² ≤ (∫_A Z²) · μ(A)`.
5. Case `∫ Z² = 0`: the left side is `… / 0 = 0` and the right side is
   nonnegative (`ENNReal.toReal_nonneg`).
6. Otherwise `∫ Z² > 0`, so `div_le_iff₀` clears the denominator; chaining
   step 3 squared (`nlinarith`) with step 4 and
   `integral_mono_measure Measure.restrict_le_self` (from `∫_A Z²` to `∫_Ω Z²`)
   gives `(1 − θ)² (∫ Z)² ≤ μ(A) · ∫ Z²`. ∎

**Used in.** `b_reasonable_anticon_zero`, instantiated at `Z = X²` and `θ = t²`
(with `moment (X²) 1 = moment X 2` and `moment (X²) 2 = moment X 4`) to turn
`B`-reasonability into the anticoncentration bound `(1 − t²)²/B`.
