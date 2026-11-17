<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.printed_shapley_four_integral_formula_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shapley and Integral Values Differ

**Claim.** For the one-element dictator set function, the Shapley value is not equal to four times the specified integral of the Bernoulli subset influence.

**Proof.** The Shapley value of this dictator is $1$, by `shapleyValue_shapleyDictator`. Four times the integral in the claim is $2/3$, by `four_mul_integral_influence_shapleyDictator`. Since $1\ne 2/3$, the asserted equality fails.

**Key facts.** `FABL.shapleyValue_shapleyDictator`, `FABL.four_mul_integral_influence_shapleyDictator`.
