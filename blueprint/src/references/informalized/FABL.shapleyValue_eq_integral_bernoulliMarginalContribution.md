<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.shapleyValue_eq_integral_bernoulliMarginalContribution -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integral Formula for the Shapley Value

**Claim.** The Shapley value of $f$ at $i$ equals the integral from $0$ to $1$ of its Bernoulli marginal contribution as the inclusion probability varies.

**Proof.** Set $h(S)=f(S\cup\{i\})-f(S\setminus\{i\})$. By definition, the Shapley value is the Shapley expectation of $h$, while the Bernoulli marginal contribution at parameter $p$ is the Bernoulli subset expectation of $h$. The integral of the latter over $p\in[0,1]$ equals the Shapley expectation of any such function (`integral_bernoulliSubsetExpectation_eq_shapleyExpectation`). Applying that identity to $h$ gives the result.

**Key facts.** `FABL.integral_bernoulliSubsetExpectation_eq_shapleyExpectation`.
