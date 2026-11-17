<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/CorrelationDistillation.lean :: FABL.pmfExpectation_apply_left_mul_right_eq_fourierCoeff_mul_correlation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Correlation and Fourier Coefficient

**Claim.** Under the stated coordinatewise mean-zero and correlation assumptions, the expectation of the product of $f$ on the first sign vector and the $i$th coordinate of the second sign vector is $\widehat f(\{i\})\rho_i$.

**Proof.** At each first sign vector, expand $f$ in its Fourier basis: $f(x)=\sum_S\widehat f(S)\,\mathrm{monomial}_S(x)$ (\texttt{FABL.fourier\_expansion}). Substitute this expansion into the expectation and use linearity to write it as the sum over $S$ of $\widehat f(S)$ times the expectation of $\mathrm{monomial}_S$ on the first vector multiplied by the $i$th sign on the second. Independence across coordinates, together with the zero means of both signs and their product expectation $\rho_k$, gives this latter expectation as $\rho_i$ when $S=\{i\}$ and zero otherwise (\texttt{FABL.independentSignPair\_monomial\_right\_expectation}). Consequently only the singleton term remains, giving $\widehat f(\{i\})\rho_i$.

**Key facts.** `FABL.fourier_expansion`, `FABL.pmfExpectation_sum`, `FABL.pmfExpectation_const_mul`, `FABL.independentSignPair_monomial_right_expectation`.
