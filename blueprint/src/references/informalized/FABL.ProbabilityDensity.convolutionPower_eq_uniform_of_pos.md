<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/Viola.lean :: FABL.ProbabilityDensity.convolutionPower_eq_uniform_of_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Powers of the Uniform Density

**Claim.** If a probability density on $\mathbb F_2^n$ is identically $1$, then every positive convolution power of it is also identically $1$.

**Proof.** Write the positive integer $d$ as a successor, say $d=k+1$. By the recursive definition of convolution power, its $d$-fold power is the convolution of the $k$-fold power with the original density. The convolution-with-uniform-density result (\texttt{ProbabilityDensity.convolution_eq_uniform_of_right}) says that convolving any probability density on the left with an identically $1$ density on the right gives the identically $1$ function. Applying it to these two factors proves the claim.

**Key facts.** `FABL.ProbabilityDensity.convolution_eq_uniform_of_right`.
