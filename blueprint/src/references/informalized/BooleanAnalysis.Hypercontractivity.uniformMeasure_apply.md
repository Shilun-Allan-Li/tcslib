<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Bonami.lean :: uniformMeasure_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The canonical uniform measure agrees with the combinatorial weight

**Claim.** For every point `x : BoolCube n`,

```
((uniformMeasure n) {x}).toReal = uniformWeight n
```

that is, the measure coming from `PMF.uniformOfFintype (BoolCube n)` gives each
singleton the mass `2⁻ⁿ` used by the combinatorial `expect`.

**Proof.**

1. `dsimp [uniformMeasure]` exposes the PMF-to-measure coercion, and
   `PMF.toMeasure_apply_singleton` (side goal `MeasurableSet.singleton x`)
   reduces the measure of `{x}` to the PMF value at `x`.
2. `PMF.uniformOfFintype_apply` evaluates that to `(Fintype.card (BoolCube n))⁻¹`
   in `ℝ≥0∞`; `ENNReal.toReal_inv` and `ENNReal.toReal_natCast` move the
   inversion and the cardinal into `ℝ`.
3. `Fintype.card_pi`, `Fintype.card_bool`, `Finset.prod_const`,
   `Finset.card_univ`, `Fintype.card_fin` compute the cardinality as `2 ^ n`.
4. Unfolding `uniformWeight` and `simp [Nat.cast_pow, inv_pow]` identifies
   `(2 ^ n : ℝ)⁻¹` with `(2⁻¹) ^ n`.

**Used in.** `BooleanAnalysis.Hypercontractivity.lowDegree_anticoncentration` in `TCSlib/BooleanAnalysis/Hypercontractivity/Applications/LowDegree.lean`; `BooleanAnalysis.Hypercontractivity.bonami_lemma` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Bonami.lean`.
