<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.sigma_sq_mul_heterogeneousOutputPivotalProbability_eq_mass_mul_influence_of_monotone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pivotal Probability and Influence

**Claim.** For the monotone Boolean function in the statement, the squared bias scale times the probability of being $b$-pivotal equals the mass of $b$ times the heterogeneous biased influence.

**Proof.** First express the output-pivotal probability as the mass of $b$ times the mean discrete derivative, using the monotone output-pivotal identity (\texttt{heterogeneousOutputPivotalProbability\_eq\_mass\_mul\_derivativeMean\_of\_monotone}). Next, express the heterogeneous influence as the squared bias scale times the flip probability (\texttt{heterogeneousBiasedInfluence\_eq\_sigma\_sq\_mul\_flipProbability}). Monotonicity identifies the indicator of a flip with the discrete derivative pointwise (\texttt{pivotalIndicator\_eq\_discreteDerivative\_of\_monotone}); taking expectations therefore identifies the flip probability with the mean derivative. Substituting these identities gives the desired equality after rearranging the real factors.

**Key facts.** `FABL.heterogeneousOutputPivotalProbability_eq_mass_mul_derivativeMean_of_monotone`, `FABL.heterogeneousBiasedInfluence_eq_sigma_sq_mul_flipProbability`, `FABL.pivotalIndicator_eq_discreteDerivative_of_monotone`.
