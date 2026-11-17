<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.bernoulliMarginalContribution_shapleyDictator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dictator Marginal Contribution

**Claim.** For every real parameter $p$, the Bernoulli marginal contribution of the singleton dictator function at its sole coordinate is $1$.

**Proof.** There are exactly two subsets of a singleton: the empty set and the set containing its sole coordinate. The dictator's marginal difference is $1$ on either subset: inserting the coordinate makes the function equal to $1$, while erasing it makes the function equal to $0$. Thus the Bernoulli expectation sums the two weights $ (1-p)+p$, which equals $1$.
