<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/FourierFormulas.lean :: FABL.noiseOperator_fourier_expansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Expansion of the Noise Operator

**Claim.** At each point, the noise operator equals the sum over subsets $S$ of $\rho^{|S|}\widehat f(S)\chi_S(x)$.

**Proof.** Expand the function in its Fourier basis, so $f=\sum_S\widehat f(S)\chi_S$ (`fourier_expansion`). Apply the linear noise operator to this finite sum term by term. Each character $\chi_S$ is an eigenfunction with eigenvalue $\rho^{|S|}$ (`noiseOperator_monomial`). Evaluating at $x$ and collecting the scalar factors gives the claimed expansion.

**Key facts.** `FABL.fourier_expansion`, `FABL.noiseOperator_monomial`.
