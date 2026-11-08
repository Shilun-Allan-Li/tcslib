<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.IsVectorFourierGranular.add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addition Preserves Fourier Granularity

**Claim.** If every Fourier coefficient of each of two functions is an integer multiple of the same real number $\varepsilon$, then every Fourier coefficient of their sum is also such a multiple.

**Proof.** Use the coefficientwise characterization of vector Fourier granularity (`isVectorFourierGranular_iff`). At any frequency $\gamma$, the coefficients of the two functions are $a\varepsilon$ and $b\varepsilon$ for some integers $a,b$. Fourier coefficients are additive (`vectorFourierCoeff_add`), so the coefficient of the sum is $(a+b)\varepsilon$. Since $a+b$ is an integer, this proves the required property at every frequency.

**Key facts.** `FABL.isVectorFourierGranular_iff`, `FABL.vectorFourierCoeff_add`.
