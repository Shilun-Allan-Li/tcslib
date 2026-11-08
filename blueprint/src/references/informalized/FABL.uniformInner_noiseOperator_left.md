<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/KKL.lean :: FABL.uniformInner_noiseOperator_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Self-adjointness of the noise operator

**Claim.** The noise operator is self-adjoint for the uniform inner product: moving it from the first argument to the second does not change the inner product.

**Proof.** Apply Plancherel to both inner products, expressing each as a sum of products of Fourier coefficients. The Fourier coefficient of the noise-smoothed function at $S$ is $\rho^{|S|}$ times the original coefficient (\texttt{FABL.fourierCoeff_noiseOperator}). Thus both inner products have, term by term, the same factor $\rho^{|S|}$ multiplying the two Fourier coefficients of $f$ and $g$. Commutativity of real multiplication makes the sums equal.

**Key facts.** `FABL.plancherel`, `FABL.fourierCoeff_noiseOperator`.
