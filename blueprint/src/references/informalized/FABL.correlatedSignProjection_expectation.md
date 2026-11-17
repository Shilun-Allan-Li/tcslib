<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/CorrelatedGaussianLimit.lean :: FABL.correlatedSignProjection_expectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of the Correlated Sign Projection

**Claim.** For every $\rho\in[-1,1]$ and every vector $t=(t_1,t_2)$ in the real two-dimensional correlation plane, the expected value of $Xt_1+Yt_2$ under the correlated sign-pair law with parameter $\rho$ is zero.

**Proof.** Expand the projection into the sum of its two coordinate terms. Linearity of expectation and the rule that a constant factor may be taken outside an expectation reduce the result to the two marginal means of the signs. Each marginal has mean zero under the correlated sign-pair law (the first- and second-coordinate mean identities, `correlatedSignPairPMF_expect_signValue_fst` and `correlatedSignPairPMF_expect_signValue_snd`). Thus both terms vanish, and the expected projection is zero.

**Key facts.** `FABL.pmfExpectation_add`, `FABL.pmfExpectation_mul_const`, `FABL.correlatedSignPairPMF_expect_signValue_fst`, `FABL.correlatedSignPairPMF_expect_signValue_snd`.
