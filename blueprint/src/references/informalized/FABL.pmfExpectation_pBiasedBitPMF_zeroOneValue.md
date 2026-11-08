<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RandomFunctions.lean :: FABL.pmfExpectation_pBiasedBitPMF_zeroOneValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Biased Bit

**Claim.** Under the law assigning probability $p$ to true and $1-p$ to false, the expectation of the indicator of true is $p$.

**Proof.** The expectation is the sum of the two point masses multiplied by the indicator values. The false point contributes zero, while the true point contributes its mass $p$, so the sum is $p$.
