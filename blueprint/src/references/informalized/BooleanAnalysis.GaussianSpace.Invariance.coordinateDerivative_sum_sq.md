<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Coordinates.lean :: BooleanAnalysis.GaussianSpace.Invariance.coordinateDerivative_sum_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative coefficient energy and influence

**Claim.** The sum of the squares of the coordinate derivative polynomial's coefficients equals the influence of coordinate $i$ for the Boolean-cube evaluation of $F$.

**Proof.** Parseval's identity for the Walsh expansion of a multilinear polynomial identifies the expected square of its Boolean-cube evaluation with the sum of the squares of its coefficients. Apply this to the coordinate derivative polynomial. Its evaluation is the Boolean-cube derivative of $F$'s evaluation, by the coordinate derivative evaluation identity. Finally, influence equals the expected square of the Boolean-cube derivative. Combining these identities gives the stated equality.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.expect_eval_sq`, `BooleanAnalysis.GaussianSpace.Invariance.coordinateDerivative_eval`, `BooleanAnalysis.ThresholdFunctions.influence_eq_expect_derivative_sq`.
