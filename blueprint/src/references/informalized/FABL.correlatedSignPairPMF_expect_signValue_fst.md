<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.correlatedSignPairPMF_expect_signValue_fst -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-sign mean

**Claim.** Under the correlated sign-pair law, the expected value of the first sign is zero.

**Proof.** Use the one-coordinate identification to express the correlated sign-pair law as the image of the law of a correlated pair of one-coordinate cube points (`correlatedPairPMF_one_map_signPairCubeOneEquiv`). Expectations under an image law are expectations of the pulled-back function (`pmfExpectation_map`). Under this identification, the first sign is the first cube coordinate. Its expected value is zero by the first-coordinate mean theorem in dimension one (`correlatedPairPMF_expect_signValue_fst`).

**Key facts.** `FABL.correlatedPairPMF_one_map_signPairCubeOneEquiv`, `FABL.pmfExpectation_map`, `FABL.correlatedPairPMF_expect_signValue_fst`.
