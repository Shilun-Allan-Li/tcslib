<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.heterogeneousOutputPivotalProbability_eq_mass_mul_derivativeMean_of_monotone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotone Output Pivotal Probability

**Claim.** For a monotone Boolean-valued function, the probability that the function outputs $b$ and is pivotal at coordinate $i$ equals the mass of $b$ at that coordinate times the expected discrete derivative at $i$.

**Proof.** First identify the pivotal-output indicator pointwise with the discrete derivative times the indicator that the input's coordinate equals $b$. If the input is pivotal, monotonicity forces its output to equal its coordinate (`monotone_output_eq_coordinate_of_isPivotal`), and the pivotal indicator agrees with the discrete derivative (`pivotalIndicator_eq_discreteDerivative_of_monotone`): both are one. Hence the product is one exactly when the output is $b$. If the input is not pivotal, the output is unchanged by the flip and the same derivative identity makes both sides zero. Taking expectations of this pointwise identity, the expected derivative times the coordinate indicator factors as the coordinate mass of $b$ times the expected derivative, by `pmfExpectation_discreteDerivative_mul_coordinateIndicator`.

**Key facts.** `FABL.monotone_output_eq_coordinate_of_isPivotal`, `FABL.pivotalIndicator_eq_discreteDerivative_of_monotone`, `FABL.pmfExpectation_discreteDerivative_mul_coordinateIndicator`.
