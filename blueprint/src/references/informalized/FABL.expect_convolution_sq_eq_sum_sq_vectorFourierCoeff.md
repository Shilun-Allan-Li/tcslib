<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/ViolaAuxiliary.lean :: FABL.expect_convolution_sq_eq_sum_sq_vectorFourierCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convolution Parseval identity

**Claim.** The uniform average of $(\varphi*F)^2$ equals the sum over binary frequencies of the products of the squared Fourier coefficients of $\varphi$ and $F$.

**Proof.** First rewrite the square as the product of two identical factors. Parseval's identity for the binary cube expresses the average of that product as the sum of the products of the corresponding Fourier coefficients (`vector_plancherel`). The Fourier coefficient of a convolution is the product of the two Fourier coefficients (`vectorFourierCoeff_convolution`). Substituting this formula into each summand and regrouping gives $\sum_\gamma\widehat\varphi(\gamma)^2\widehat F(\gamma)^2$.

**Key facts.** `FABL.vector_plancherel`, `FABL.vectorFourierCoeff_convolution`.
