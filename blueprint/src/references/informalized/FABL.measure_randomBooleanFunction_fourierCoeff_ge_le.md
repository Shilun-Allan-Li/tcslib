<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RandomBooleanFourierMaximum.lean :: FABL.measure_randomBooleanFunction_fourierCoeff_ge_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Fourier coefficient tail bound

**Claim.** For any fixed subset \(S\) of coordinates and any \(\varepsilon\ge 0\), the probability that the absolute Fourier coefficient of a uniformly chosen Boolean function at \(S\) is at least \(\varepsilon\) is at most \(2\exp(-2^n\varepsilon^2/2)\).

**Proof.** Reindex a Boolean function by the cube inputs and multiply its value at each input by the corresponding character. This gives an equivalence between uniformly chosen Boolean functions and sequences of signs; the character multiplication preserves the uniform distribution (\(\texttt{map_uniformPMF_equiv}\)). Under this reindexing, the Fourier coefficient is exactly the empirical mean of the resulting signs (\(\texttt{finiteUniformEmpiricalMean_randomBooleanCoefficientSampleEquiv}\)). A uniform sign has mean zero (\(\texttt{expect_signValue_eq_zero}\)) and lies in \([-1,1]\) (\(\texttt{signValue_mem_Icc}\)). The empirical-mean concentration estimate with sample size equal to the number of cube inputs therefore gives the stated bound. Transporting the event through the equivalence identifies it with the Fourier-coefficient tail event, completing the argument (\(\texttt{measure_finiteUniformEmpiricalMean_sub_expect_ge_le}\)).

**Key facts.** `FABL.expect_signValue_eq_zero`, `FABL.signValue_mem_Icc`, `FABL.measure_finiteUniformEmpiricalMean_sub_expect_ge_le`, `FABL.map_uniformPMF_equiv`, `FABL.finiteUniformEmpiricalMean_randomBooleanCoefficientSampleEquiv`.
