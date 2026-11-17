<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.fourierCoeff_fknOptimalityLowerSlice_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty-Frequency Centered Indicator Coefficient

**Claim.** The empty-frequency Fourier coefficient of the centered indicator $x\mapsto 2\mathbf{1}_A(x)-1$ is $2m-1$, where $m$ is the uniform mass of $A$ on the chosen tail cube.

**Proof.** At the empty frequency, the monomial is the empty product, hence is constantly $1$. The coefficient is therefore the expectation of $2\mathbf{1}_A-1$. Linearity of expectation gives twice the expectation of the indicator minus the expectation of $1$; these are $m$ and $1$, respectively. The result is $2m-1$.
