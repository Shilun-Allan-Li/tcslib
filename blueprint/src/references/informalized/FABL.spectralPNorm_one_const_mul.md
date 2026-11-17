<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.spectralPNorm_one_const_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneity of the spectral one-norm

**Claim.** For every real number $c$ and real-valued function $f$, the spectral one-norm of $x\mapsto c f(x)$ equals $|c|$ times the spectral one-norm of $f$.

**Proof.** Rewrite each spectral one-norm as the sum of the absolute values of its Fourier coefficients (\(\texttt{spectralPNorm\_one\_eq\_sum\_abs}\)). The Fourier coefficient of \(x\mapsto c f(x)\) is \(c\) times the corresponding coefficient of \(f\) (\(\texttt{vectorFourierCoeff\_const\_mul}\)). Taking absolute values turns each summand into \(|c|\,|\widehat f(\gamma)|\); factoring the common scalar \(|c|\) out of the finite sum proves the identity.

**Key facts.** `FABL.spectralPNorm_one_eq_sum_abs`, `FABL.vectorFourierCoeff_const_mul`.
