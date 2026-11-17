<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.heterogeneousOutputPivotalProbability_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Pivotal Probability Under Constant Bias

**Claim.** When all coordinates have bias $p$, the heterogeneous probability that the function outputs $b$ and is pivotal at coordinate $i$ equals the corresponding probability under the product distribution with common bias $p$.

**Proof.** With constant bias, each coordinate law in the heterogeneous product is the same biased sign law. Thus the heterogeneous product distribution agrees with the product distribution used in the definition of the common-bias probability. The event being measured is also identical in both definitions, so the two probabilities agree by unfolding the definitions.
