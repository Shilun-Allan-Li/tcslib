<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.pmfExpectation_heterogeneousBiasedSignPMF_discreteDerivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected discrete derivative under biased signs

**Claim.** Under the independent product distribution with coordinate parameters $p_j\in(0,1)$, the expectation of the discrete derivative of $f$ in coordinate $i$ equals the cube partial derivative of $f$ at the coordinate means $1-2p_j$.

**Proof.** Write the discrete derivative as a Fourier sum over subsets $S$ containing $i$, with each term the Fourier coefficient indexed by $S$ multiplied by the monomial indexed by $S\setminus\{i\}$. This is the Fourier expansion of the derivative (\texttt{FABL.discreteDerivative_eq_fourier_sum}). Linearity of expectation moves the expectation inside this finite sum. For a fixed subset containing $i$, pull its Fourier coefficient out of the expectation, then use the biased-cube monomial formula: the expected monomial on $S\setminus\{i\}$ is the product of the coordinate means over that set (\texttt{FABL.pmfExpectation_heterogeneousBiasedSignPMF_monomial}). Subsets not containing $i$ contribute zero in the equivalent sum over all subsets. The resulting sum is exactly the cube partial derivative at the singleton $\{i\}$, by its defining subset sum.

**Key facts.** `FABL.discreteDerivative_eq_fourier_sum`, `FABL.pmfExpectation_sum`, `FABL.pmfExpectation_const_mul`, `FABL.pmfExpectation_heterogeneousBiasedSignPMF_monomial`.
