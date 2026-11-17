<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FourierCoefficientsOfMajority.lean :: FABL.eval_middleLayerFourierPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Middle-Layer Fourier Polynomial Evaluation

**Claim.** For every real number $\rho$, evaluating the middle-layer Fourier polynomial at $\rho$ gives the sum of its Fourier coefficients weighted by $\rho$ raised to the corresponding subset sizes.

**Proof.** The polynomial is a finite sum over coordinate subsets $U$, with summand the constant polynomial given by the Fourier coefficient at $U$ multiplied by $X^{|U|}$. Evaluation at $\rho$ distributes over this finite sum. Each summand evaluates to $\widehat f(U)\rho^{|U|}$, since a constant polynomial evaluates to its constant and $X^{|U|}$ evaluates to $\rho^{|U|}$. Summing gives the claimed formula.
