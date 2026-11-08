<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Tensorization.lean :: BooleanAnalysis.GaussianSpace.BobkovInterpolation.extendedFunctional_restrictLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Last-Coordinate Splitting of the Functional

**Claim.** The extended functional on the full cube is the average of the extended functionals on its two last-coordinate restrictions, with the last-coordinate difference included as an additional function.

**Proof.** Express the uniform expectation on the $(n+1)$-dimensional cube as the average of the expectations on the false and true last-coordinate slices (`expect_succ_eq`). On either slice, the sum of squared derivatives over all coordinates equals the sum over the first $n$ coordinates of the derivative of the restricted function, plus the square of the last-coordinate derivative; that last derivative is the difference function. This decomposition is exactly `sum_sq_derivative_snoc`. The additional coordinates on the slice are the restrictions of the original $g_j$, while the new first coordinate is the difference function. Substitution into each square-root integrand identifies the two slice expectations with the two extended functionals in the formula, proving the equality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.expect_succ_eq`, `BooleanAnalysis.GaussianSpace.sum_sq_derivative_snoc`.
