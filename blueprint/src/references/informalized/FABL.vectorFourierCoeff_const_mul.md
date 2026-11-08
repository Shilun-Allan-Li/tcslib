<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.vectorFourierCoeff_const_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling a Fourier Coefficient

**Claim.** For a real constant $c$, the vector Fourier coefficient of $x\mapsto cf(x)$ at $\gamma$ is $c$ times the vector Fourier coefficient of $f$ at $\gamma$.

**Proof.** Express both coefficients as expectations of the function times the Walsh character (`FABL.vectorFourierCoeff_eq_expect`). The integrand for the scaled function is $c$ times the original integrand, after associating the real products. Linearity of finite expectation pulls the constant $c$ outside, giving the claimed identity.

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`.
