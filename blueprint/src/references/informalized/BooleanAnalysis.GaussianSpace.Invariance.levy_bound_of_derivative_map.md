<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InvarianceDistribution.lean :: BooleanAnalysis.GaussianSpace.Invariance.levy_bound_of_derivative_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lévy bound for mapped variables

**Claim.** The derivative-based integral error hypothesis for the mapped random variables implies that the Lévy distance between their distributions is at most $((m+2)+2^m)B^{1/(m+2)}$.

**Proof.** Because $U$ and $V$ are measurable almost everywhere and the original measures are probability measures, their pushforward measures under $U$ and $V$ are probability measures. Apply the derivative bound for measures (`levy_bound_of_derivative`) to these pushforwards. For any admissible smooth test function, integration against a pushforward equals integration of its composition with the map, by the change-of-variables formula for mapped measures (`integral_map`). The assumed error estimate therefore supplies the required test-function bound for the pushforwards, and the result follows.

**Key facts.** `BooleanAnalysis.GaussianSpace.Invariance.levy_bound_of_derivative`.
