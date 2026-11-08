<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.BinarySubspaceSplit.vectorFourierCoeff_cosetAverage -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficient of a coset average

**Claim.** The vector Fourier coefficient of the coset average at a complementary frequency equals the ambient expectation of the function times the character associated to that frequency.

**Proof.** Use the expectation formula for vector Fourier coefficients (FABL.vectorFourierCoeff_eq_expect) to express the left side as an average over the ambient cube. Reindex this uniform average through the splitting isomorphism, so points are represented uniformly as pairs $(h,x)$ with $h\in H$ and $x$ in the complementary cube. The character at the image of $(h,x)$ depends only on $x$ and is the corresponding Walsh character: its sign value is the binary sign of the dot product (FABL.signValue_signEncode_eq_binarySign; FABL.vectorWalshCharacter_apply). The resulting average over pairs can be written as an iterated average, and the order of averaging over the two finite factors is exchanged. For each fixed $x$, the Walsh-character factor is constant as $h$ varies, so it factors out of the average over $H$. That inner average is exactly the coset average of the function at $x$. The remaining average over $x$ is the Fourier coefficient of the coset average, as required.

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`, `FABL.signValue_signEncode_eq_binarySign`, `FABL.vectorWalshCharacter_apply`.

**Caveat.** The supplied informal statement describes a Poisson summation formula, but the formal theorem and its proof establish the stated Fourier-coefficient identity for the coset average.
