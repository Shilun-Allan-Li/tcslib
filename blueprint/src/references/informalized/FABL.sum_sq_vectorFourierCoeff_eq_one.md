<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentFunctions.lean :: FABL.sum_sq_vectorFourierCoeff_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vector Fourier Parseval Identity

**Claim.** If a real-valued function on the $n$-dimensional vector space over $\mathbb F_2$ has absolute value $1$ at every input, then the sum over all vectors of the squares of its vector Fourier coefficients is $1.

**Proof.** First rewrite each square as a product of the coefficient with itself. The vector Plancherel identity (`FABL.vector_plancherel`), applied with the function in both slots, identifies this sum with the expectation of $f(x)f(x)$. Since $f(x)^2=|f(x)|^2=1$ at every input by the sign-valued hypothesis, the integrand is constantly $1$. The expectation of a constant function on the finite cube is that constant, so the sum is $1$.

**Key facts.** `FABL.vector_plancherel`.
