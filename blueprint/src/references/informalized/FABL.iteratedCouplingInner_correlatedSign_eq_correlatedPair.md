<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.iteratedCouplingInner_correlatedSign_eq_correlatedPair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterated and joint correlated expectations

**Claim.** The iterated coupling expectation for the coordinatewise correlated sign law equals the expectation of the product of the two functions under the joint correlated-pair law.

**Proof.** First express the iterated coupling as expectation under the product law of independent coordinate pairs, with the two sign vectors formed from the first and second entries (`iteratedCouplingInner_eq_productProbabilityPMF`). The product law of the single-coordinate correlated sign-pair law, transported to a pair of sign vectors, is precisely the joint correlated-pair law (`productProbabilityPMF_correlatedSignPair_map`). Expectations are preserved under this transport: the expectation under a mapped probability law is the original expectation after composing the payoff with the map (`pmfExpectation_map`). The composed payoff is exactly the product of the function evaluated on each vector, which proves the equality.

**Key facts.** `FABL.iteratedCouplingInner_eq_productProbabilityPMF`, `FABL.productProbabilityPMF_correlatedSignPair_map`, `FABL.pmfExpectation_map`.
