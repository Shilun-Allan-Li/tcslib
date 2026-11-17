<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLR.lean :: FABL.exists_vectorFourierFourthMoment_le_sq_vectorFourierCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A fourth-moment bound

**Claim.** For a sign-valued function on the binary cube, its vector Fourier fourth moment is at most the square of one of its vector Fourier coefficients.

**Proof.** Choose a vector $\gamma$ maximizing the square of the vector Fourier coefficient; such a maximizer exists because the cube is finite. For every $\delta$, maximality gives $\widehat f(\delta)^2\le\widehat f(\gamma)^2$. The fourth-moment sum is $\sum_\delta \widehat f(\delta)^2\widehat f(\delta)^2$. Multiplying the maximality inequality by the nonnegative quantity $\widehat f(\delta)^2$ and summing yields an upper bound of $\widehat f(\gamma)^2\sum_\delta\widehat f(\delta)^2$. Parseval's identity for sign-valued functions (`sum_sq_vectorFourierCoeff_eq_one`) says the remaining sum is one. The resulting bound is exactly $\widehat f(\gamma)^2$.

**Key facts.** `FABL.sum_sq_vectorFourierCoeff_eq_one`.
