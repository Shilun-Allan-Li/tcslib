<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.quadraticPairRankOneTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rank-One Tester Acceptance Formula

**Claim.** The rank-one tester’s acceptance probability equals the uniform average, over independent uniform x, y, and z, of the indicator that ℓ(x)ℓ(y)=q(Z)+q(Z+xyᵀ), where Z is the reshaping of z.

**Proof.** By definition, acceptance probability is the expectation of the indicator that the tester accepts its transcript. The tester’s seed is a triple consisting of x, y, and z, sampled uniformly; averaging over this product space is the iterated uniform expectation over x, then y, then z. For a fixed triple, the queries return ℓ(x), ℓ(y), q(Z), and q(Z+xyᵀ), with Z the reshaping of z. Its acceptance condition is precisely the displayed equality, so the pointwise acceptance indicator is the one in the claimed average.

**Key facts.** `FABL.pmfExpectation_uniformPMF_eq_expect`.
