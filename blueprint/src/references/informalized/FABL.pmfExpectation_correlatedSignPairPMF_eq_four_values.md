<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.pmfExpectation_correlatedSignPairPMF_eq_four_values -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a Correlated Sign Pair

**Claim.** For the stated distribution of a uniform sign $X$ and its possibly flipped partner $Y$, the expectation of $H(X,Y)$ is the given weighted sum of the four values of $H$.

**Proof.** Expand the arbitrary function $H$ on the four sign pairs in the basis $1$, $X$, $Y$, and $XY$ (`FABL.signPair_fourier_expansion`). The constant coefficient is the average of the four values of $H$; the other three coefficients multiply the respective sign functions. By linearity of expectation (`FABL.pmfExpectation_add`), the expectation is the sum of the expectations of these four terms. The constant term contributes its coefficient (`FABL.pmfExpectation_const`); the coefficient factors out of each sign term (`FABL.pmfExpectation_const_mul`). The two individual signs have mean zero, while their product has mean $\theta$ (`FABL.correlatedSignPairPMF_expect_signValue_fst`, `FABL.correlatedSignPairPMF_expect_signValue_snd`, `FABL.correlatedSignPairPMF_expect_signValue_mul`). Substituting these values and collecting the four evaluations of $H$ gives the displayed formula.

**Key facts.** `FABL.signPair_fourier_expansion`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_const_mul`, `FABL.correlatedSignPairPMF_expect_signValue_fst`, `FABL.correlatedSignPairPMF_expect_signValue_snd`, `FABL.correlatedSignPairPMF_expect_signValue_mul`.
