<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RandomFunctions.lean :: FABL.integral_zeroOneValue_pBiasedBitPMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a biased bit

**Claim.** If a Boolean random variable is true with probability $p$ and false with probability $1-p$, then the mean of its value, with true assigned $1$ and false assigned $0$, is $p$.

**Proof.** First identify integration against the measure induced by a probability mass function with the probability-mass-function expectation (`pmfExpectation_eq_integral`). The expectation of the zero-one value under the specified biased-bit distribution is $p` (`pmfExpectation_pBiasedBitPMF_zeroOneValue`), and therefore so is the integral.

**Key facts.** `FABL.pmfExpectation_eq_integral`, `FABL.pmfExpectation_pBiasedBitPMF_zeroOneValue`.
