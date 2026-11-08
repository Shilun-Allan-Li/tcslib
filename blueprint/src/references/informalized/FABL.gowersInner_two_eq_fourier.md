<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersInner_two_eq_fourier -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier formula for the two dimensional inner product

**Claim.** For a family of four functions indexed by the vertices of the two dimensional cube, its Gowers inner product is the sum over frequencies of the product of the four corresponding vector Fourier coefficients.

**Proof.** Apply the decomposition of a Gowers inner product into its two half expectations (`gowersInner_succ`). At each of the two values of the last coordinate, the half expectation is the convolution of the two functions on the corresponding opposite vertices (`gowersHalfExpectation_two_eq_convolution`). Thus the original average becomes the average over a single cube point of the product of these two convolutions. The domain of the remaining average is a function on a singleton coordinate, so identifying it with the cube itself gives the ordinary inner product of the two convolutions. By the vector-valued Plancherel identity (`vector_plancherel`), this inner product is the sum over frequencies of the products of their vector Fourier coefficients. Finally, the Fourier coefficient of a convolution is the product of the Fourier coefficients (`vectorFourierCoeff_convolution`); applying this to each convolution and regrouping the four real factors gives the stated formula.

**Key facts.** `FABL.gowersInner_succ`, `FABL.gowersHalfExpectation_two_eq_convolution`, `FABL.vector_plancherel`, `FABL.vectorFourierCoeff_convolution`.
