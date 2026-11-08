<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RegularThresholdNoiseStability.lean :: FABL.integral_regularThresholdPairSummand_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of one correlated pair summand

**Claim.** Under the correlated sign-pair distribution, the expected vector $(a_i x_i,a_i y_i)$ is zero.

**Proof.** The summand has finite third moment, hence is integrable. To show that the vector integral vanishes, check its two coordinates. The first coordinate is $a_i x_i$; converting its integral to expectation and factoring out $a_i$ reduces it to $a_i$ times the mean of the first sign, which is zero (`correlatedPairPMF_expect_signValue_fst`). The second coordinate is handled in the same way using the zero mean of the second sign (`correlatedPairPMF_expect_signValue_snd`). Thus both coordinates vanish.

**Key facts.** `FABL.regularThresholdPairSummand_memLp`, `FABL.pmfExpectation_eq_integral`, `FABL.pmfExpectation_const_mul`, `FABL.correlatedPairPMF_expect_signValue_fst`, `FABL.correlatedPairPMF_expect_signValue_snd`.
