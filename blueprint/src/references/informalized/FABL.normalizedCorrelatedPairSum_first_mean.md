<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/CorrelatedMajority.lean :: FABL.normalizedCorrelatedPairSum_first_mean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of the First Normalized Coordinate

**Claim.** The expected first coordinate of the normalized correlated pair sum is zero.

**Proof.** The first coordinate of the normalized pair sum is the normalized sum of the signs in the first vector (\texttt{FABL.correlationFirstCoordinate_normalizedCorrelatedPairSum}). Rewrite this normalized margin as a linear form with constant coefficient $(\sqrt n)^{-1}$ (\texttt{FABL.normalizedMargin_eq_linearForm}). The first vector has the uniform distribution under the correlated-pair law (\texttt{FABL.pmfExpectation_correlatedPairPMF_fst}), and expectation under the uniform law is the Boolean-cube average (\texttt{FABL.pmfExpectation_uniformPMF_eq_expect}). Expand the linear form as a sum over coordinates and interchange the finite sum with expectation. Each coordinate sign is the singleton monomial, whose uniform expectation is zero by the monomial expectation formula (\texttt{FABL.expect_monomial}). Hence every summand has mean zero, and so does the first coordinate.

**Key facts.** `FABL.correlationFirstCoordinate_normalizedCorrelatedPairSum`, `FABL.normalizedMargin_eq_linearForm`, `FABL.pmfExpectation_correlatedPairPMF_fst`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.expect_monomial`.

**Caveat.** The supplied informal statement also mentions the second mean, second moments, and covariance matrix, but the formal declaration and proof provided establish only the first-coordinate mean.
