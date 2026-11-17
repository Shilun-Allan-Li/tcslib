<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseKernels.lean :: FABL.correlatedSignPairPMF_expect_signValue_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product mean of a correlated sign pair

**Claim.** Under the correlated sign-pair law, the expected product of the two signs is $\rho$.

**Proof.** Transport the correlated sign-pair law back to the one-coordinate cube-pair law using the coordinate identification (`correlatedPairPMF_one_map_signPairCubeOneEquiv`). The expectation under the transported law is the expectation of the corresponding pulled-back function (`pmfExpectation_map`); that function is the product of the two signs at the sole coordinate. The one-coordinate cube-pair product-mean theorem gives this expectation as $\rho$ (`correlatedPairPMF_expect_signValue_mul`).

**Key facts.** `FABL.correlatedPairPMF_one_map_signPairCubeOneEquiv`, `FABL.pmfExpectation_map`, `FABL.correlatedPairPMF_expect_signValue_mul`.
