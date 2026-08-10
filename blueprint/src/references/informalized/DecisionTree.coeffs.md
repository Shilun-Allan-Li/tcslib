<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean :: coeffs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The Fourier coefficients of a decision tree, by structural recursion

**Definition.** `DecisionTree.coeffs : DecisionTree n → Finset (Fin n) → ℝ`
assigns to a tree `T` and a frequency `S` a real number, by structural
recursion on the tree:

- `coeffs (.leaf b) S = if S = ∅ then boolToSign b else 0` — a constant
  function has all its weight at the empty frequency, with sign
  `boolToSign b` (`false ↦ 1`, `true ↦ -1`);
- `coeffs (.branch i lo hi) S = (coeffs lo S + coeffs hi S) / 2
  + (coeffs lo (S ∆ {i}) - coeffs hi (S ∆ {i})) / 2`, where `∆` is
  `symmDiff`.

The branch clause is the coefficient-level transcription of the pointwise
identity `f = (f_lo + f_hi)/2 + χ_i · (f_lo − f_hi)/2`: multiplying by `χ_i`
sends frequency `S ∆ {i}` to `S`, so the second half of the expansion is read
off at the shifted frequency.

Note that this is a *definition*, not a claim: nothing here asserts that these
numbers are the Fourier coefficients of the tree function. That is the content
of `signEval_eq_sum_coeffs` and `fourierCoeff_signEval`.

**Used in.** Every result in the file. `signEval_eq_sum_coeffs` identifies
`coeffs` as a genuine character expansion, `fourierCoeff_signEval` upgrades it
to `fourierCoeff T.signEval = T.coeffs`, and the four structural properties
(`coeffs_eq_zero_of_depth_lt`, `sum_abs_coeffs_le`, `coeffs_mul_two_pow_int`,
`coeffs_granular`) are all proved by induction along this same recursion.
