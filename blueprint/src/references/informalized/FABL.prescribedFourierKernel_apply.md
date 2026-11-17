<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.prescribedFourierKernel_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prescribed Fourier kernel formula

**Claim.** The prescribed Fourier kernel at $a,x$ is $1/|\mathcal F|$ times the sum over $S\in\mathcal F$ of the product of the monomial at $a$ and the monomial at $x$.

**Proof.** Expand the kernel and its Fourier projection. The Fourier coefficient of the indicator polynomial at a set $S$ is the reciprocal of the cube cardinality times the monomial at $a$ (`fourierCoeff_indicatorPolynomial`). Substituting this coefficient into the finite sum gives a factor of the cube cardinality times its reciprocal, which cancels. Distributing the remaining scalar across the sum leaves the reciprocal of $|\mathcal F|$ multiplying the sum of the products of the two monomials.

**Key facts.** `FABL.fourierCoeff_indicatorPolynomial`.
