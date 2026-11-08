<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.pmfExpectation_literalProductSelectorPairPMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation under selector sampling

**Claim.** The expectation of any function of the selected pair $(X,Y)$ under the literal product-selector distribution equals the nested expectation obtained by averaging over the independent vectors $U,V$ and then over the correlated selector vectors.

**Proof.** First express the literal distribution as a pushforward of the joint construction: the expectation of $H$ after a map is the expectation of its composite with that map (the mapped-expectation formula, `FABL.pmfExpectation_map`). The expectation under the successive sampling of the plus vector, minus vector, and coordinate selector pairs then expands into nested expectations, by the expectation formula for a bind (`FABL.pmfExpectation_bind`). For fixed plus and minus vectors, the selector distribution is the product of independent coordinatewise correlated sign pairs. The correlated-pair coordinate identity (`FABL.correlatedPairPMF_map_pairCoordinatesEquiv`) identifies this product distribution with the coordinatewise view of the correlated pair-vector distribution. Applying the mapped-expectation formula once more changes to that vector distribution. Under this identification, selecting from the plus and minus vectors coordinatewise according to the first and second selector signs is exactly the pair $(X,Y)$ in the statement, so the resulting expression is the claimed nested expectation.

**Key facts.** `FABL.pmfExpectation_map`, `FABL.pmfExpectation_bind`, `FABL.correlatedPairPMF_map_pairCoordinatesEquiv`.
