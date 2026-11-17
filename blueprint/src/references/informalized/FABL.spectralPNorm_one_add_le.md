<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.spectralPNorm_one_add_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Triangle inequality for the spectral one-norm

**Claim.** For real-valued functions $f,g$ on the $n$-dimensional Boolean vector space, the spectral one-norm of $f+g$ is at most the sum of their spectral one-norms.

**Proof.** By the formula for the spectral one-norm as the sum of the absolute values of the Fourier coefficients (\(\texttt{spectralPNorm\_one\_eq\_sum\_abs}\)), and the additivity of each Fourier coefficient under addition of functions (\(\texttt{vectorFourierCoeff\_add}\)), the left-hand side becomes \(\sum_\gamma |\widehat f(\gamma)+\widehat g(\gamma)|\). The triangle inequality in \(\mathbb R\) bounds each summand by \(|\widehat f(\gamma)|+|\widehat g(\gamma)|\). Summing these inequalities and distributing the finite sum over addition gives \(\sum_\gamma |\widehat f(\gamma)|+\sum_\gamma |\widehat g(\gamma)|\), which is the desired right-hand side.

**Key facts.** `FABL.spectralPNorm_one_eq_sum_abs`, `FABL.vectorFourierCoeff_add`.
