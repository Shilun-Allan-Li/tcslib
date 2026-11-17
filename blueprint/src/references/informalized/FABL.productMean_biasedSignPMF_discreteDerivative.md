<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.productMean_biasedSignPMF_discreteDerivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Biased Discrete Derivative

**Claim.** For $0<p<1$, the mean under the biased product distribution of the discrete derivative of $f$ in coordinate $i$ is $\sum_{S\ni i}\widehat f(S)(1-2p)^{|S|-1}$.

**Proof.** First express the discrete derivative as a Fourier sum over sets containing $i$: its term for $S$ is the Fourier coefficient of $f$ at $S$ times the monomial on $S\setminus\{i\}$ (`discreteDerivative_eq_fourier_sum`). Linearity of expectation lets us take the mean term by term (`pmfExpectation_sum`), and filtering retains exactly the sets containing $i$. For each such set, pull its Fourier coefficient outside the expectation (`pmfExpectation_const_mul`). The mean of a monomial under the biased sign product distribution is the bias mean raised to the size of its index set (`productMean_biasedSignPMF_monomial`); since $i\in S$, removing $i$ leaves $|S|-1$ indices. The terms for sets not containing $i$ vanish, yielding the stated formula.

**Key facts.** `FABL.discreteDerivative_eq_fourier_sum`, `FABL.pmfExpectation_sum`, `FABL.pmfExpectation_const_mul`, `FABL.productMean_biasedSignPMF_monomial`, `FABL.pmfExpectation_const`.
