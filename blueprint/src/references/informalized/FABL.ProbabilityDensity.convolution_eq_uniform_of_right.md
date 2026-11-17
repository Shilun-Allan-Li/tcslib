<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/Viola.lean :: FABL.ProbabilityDensity.convolution_eq_uniform_of_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Convolution with the Uniform Density

**Claim.** If $\phi$ is identically $1$, then the convolution of probability densities $\psi$ and $\phi$ is identically $1$.

**Proof.** Fix $x\in\mathbb F_2^n$. The convolution formula (\texttt{convolution_apply}) expresses the value at $x$ as the uniform expectation over $y$ of $\psi(y)\phi(x-y)$. Since $\phi$ is identically $1$, the integrand reduces to $\psi(y)$. Its uniform expectation is $1$ because $\psi$ is a probability density (\texttt{ProbabilityDensity.expect_eq_one}). Thus the convolution has value $1$ at every $x$.

**Key facts.** `FABL.convolution_apply`, `FABL.ProbabilityDensity.expect_eq_one`.
