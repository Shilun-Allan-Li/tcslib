<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/BooleanBlocks.lean :: BooleanAnalysis.GaussianSpace.bobkov_inequality_finite_index -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bobkov Inequality for Finite Coordinates

**Claim.** For a function on a finite Boolean cube taking values in $[0,1]$, the closed Gaussian profile of its uniform expectation is at most the uniform expectation of the square root of the squared profile plus the sum of squared coordinate derivatives.

**Proof.** Replace the finite coordinate set $I$ by a coordinate set of the form $\mathrm{Fin}(k)$ using a bijection, and pull the function back along the resulting reindexing map. This map preserves the product uniform measure. It also carries each single-coordinate update to the corresponding update at the reindexed coordinate, so the sum of squared derivatives is unchanged after reindexing. The uniform product integral equals the uniform expectation (`integral_uniformBool_pi_eq_expect`), while measure preservation transports both the mean and the right-hand integrand between the two coordinate descriptions. Apply the natural-number-coordinate Bobkov inequality (`bobkov_inequality`) to the pulled-back function, which still takes values in $[0,1]$, and transport its two sides back to obtain the finite-index assertion.

**Key facts.** `BooleanAnalysis.GaussianSpace.bobkov_inequality`, `BooleanAnalysis.GaussianSpace.integral_uniformBool_pi_eq_expect`.
