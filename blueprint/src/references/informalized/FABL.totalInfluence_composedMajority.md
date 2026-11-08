<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ComposedMajorityInfluence.lean :: FABL.totalInfluence_composedMajority -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence of Composed Majority

**Claim.** For every natural number $m$, the total influence of the composed majority function equals $1$ plus one half of the total influence of majority on $2m+1$ sign coordinates.

**Proof.** Set $q=1/2$. At this bias, the biased sign distribution is uniform (`FABL.biasedSignPMF_one_half_eq_uniform`), and the square of the bias scale is $1$ (`FABL.biasSigma_sq`). The derivative of the biased minus-probability polynomial of any monotone Boolean function at an interior bias is its product total influence divided by the squared bias scale (`FABL.hasDerivAt_biasedMinusProbabilityPolynomial_eq_totalInfluence`). Since majority and composed majority are monotone (`FABL.majority_monotone`, `FABL.composedMajority_monotone`), this identifies their derivatives at $q$ with their respective uniform total influences. For the composed function, its probability polynomial is $p^2+2p(1-p)$ times the majority probability polynomial, with the latter multiplied by $2p(1-p)$ (`FABL.composedMajority_probability_formula`). At $p=1/2$, the derivative of $p^2$ is $1$, the factor $2p(1-p)$ is $1/2$, and its derivative is zero. The product rule therefore gives the composed derivative as $1$ plus half the majority derivative. Substituting the total-influence interpretations of both derivatives proves the identity.

**Key facts.** `FABL.biasSigma_sq`, `FABL.biasedSignPMF_one_half_eq_uniform`, `FABL.hasDerivAt_biasedMinusProbabilityPolynomial_eq_totalInfluence`, `FABL.majority_monotone`, `FABL.composedMajority_monotone`, `FABL.composedMajority_probability_formula`, `FABL.productTotalInfluence_uniformSign_eq_totalInfluence`.
