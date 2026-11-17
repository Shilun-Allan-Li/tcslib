<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.four_mul_integral_influence_shapleyDictator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrated influence of a dictator

**Claim.** For the dictator on subsets of a one-coordinate set, four times the integral of its influence over $p\in[0,1]$ equals $2/3$.

**Proof.** The dictator's influence at coordinate $0$ is $p(1-p)$ (`bernoulliSubsetInfluence_shapleyDictator`). Thus the required integral is four times $\int_0^1 p(1-p)\,dp$. The beta-integral formula gives $\int_0^1 p^1(1-p)^1\,dp=1!1!/3!=1/6$ (`integral_pow_mul_one_sub_pow`). Multiplying by four yields $2/3$.

**Key facts.** `FABL.bernoulliSubsetInfluence_shapleyDictator`, `FABL.integral_pow_mul_one_sub_pow`.
