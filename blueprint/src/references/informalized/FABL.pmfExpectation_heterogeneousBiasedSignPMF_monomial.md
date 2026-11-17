<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.pmfExpectation_heterogeneousBiasedSignPMF_monomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected biased-cube monomial

**Claim.** Under the independent product distribution with coordinate parameters $p_i\in(0,1)$, the expectation of the sign monomial indexed by $S$ is $\prod_{i\in S}(1-2p_i)$.

**Proof.** Apply the mixed-monomial expectation formula with its first subset taken to be $S$ and its second subset empty (\texttt{FABL.pmfExpectation_monomial_mul_heterogeneousBiasedMonomial}). The empty-indexed heterogeneous monomial is the constant $1$, and the empty subset is contained in every set. The formula therefore reduces to the product of the coordinate means over $S$, which is the claimed expectation.

**Key facts.** `FABL.pmfExpectation_monomial_mul_heterogeneousBiasedMonomial`.
