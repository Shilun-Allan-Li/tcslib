<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.correlatedSignPairPMF_expect_signValue_snd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second-sign mean

**Claim.** Under the correlated sign-pair law, the expected value of the second sign is zero.

**Proof.** Use the one-coordinate identification to view the correlated sign-pair law as the image of the one-coordinate cube-pair law (`correlatedPairPMF_one_map_signPairCubeOneEquiv`). The image-expectation rule turns the expectation of the second sign into the expectation of the second cube coordinate (`pmfExpectation_map`). That expectation is zero by the second-coordinate mean theorem in dimension one (`correlatedPairPMF_expect_signValue_snd`).

**Key facts.** `FABL.correlatedPairPMF_one_map_signPairCubeOneEquiv`, `FABL.pmfExpectation_map`, `FABL.correlatedPairPMF_expect_signValue_snd`.
