<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ReasonableProductPolynomials.lean :: FABL.productMultilinearRandomVariable_secondMoment_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Moment Under a Product Distribution

**Claim.** For a product distribution whose first-coordinate variable has mean zero, the second moment of the product multilinear random variable is the sum of the first-coordinate second moment times the second moment of the odd-coefficient polynomial on the remaining coordinates, and the second moment of the even-coefficient polynomial there.

**Proof.** First condition on the remaining coordinates, using the product expectation decomposition (FABL.pmfExpectation_independentProductPMF_cons). For each fixed tail, the first-coordinate decomposition (FABL.productMultilinearRandomVariable_cons) writes the random variable as $X_0(z)d+e$, where $d$ is the odd-coefficient polynomial evaluated on the tail and $e$ is the even-coefficient polynomial evaluated there. The centered affine-square identity (FABL.pmfExpectation_centered_affine_sq) says that averaging its square over the first coordinate gives $\mathbb E[X_0^2]d^2+e^2$, because $\mathbb E[X_0]=0$. Averaging over the tail then separates this sum by linearity of expectation (FABL.pmfExpectation_add); pulling the constant factor $\mathbb E[X_0^2]$ outside its expectation (FABL.pmfExpectation_const_mul) yields the claimed formula.

**Key facts.** `FABL.pmfExpectation_independentProductPMF_cons`, `FABL.productMultilinearRandomVariable_cons`, `FABL.pmfExpectation_centered_affine_sq`, `FABL.pmfExpectation_add`, `FABL.pmfExpectation_const_mul`.
