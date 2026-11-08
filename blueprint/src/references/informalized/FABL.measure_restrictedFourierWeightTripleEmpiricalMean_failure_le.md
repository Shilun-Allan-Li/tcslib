<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/GoldreichLevin/RestrictedWeights.lean :: FABL.measure_restrictedFourierWeightTripleEmpiricalMean_failure_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted Fourier Weight Concentration

**Claim.** For the specified triple-input observation, the probability that its empirical mean differs from the restricted Fourier weight by at least $\varepsilon$ is at most $2\exp(-m\varepsilon^2/2)$.

**Proof.** Each triple-input observation lies in $[-1,1]$ (\texttt{restrictedFourierWeightObservationFromInputs\_mem\_Icc}). Its expectation equals the restricted Fourier weight (\texttt{expect\_restrictedFourierWeightTripleObservation}). Apply the finite-sample Hoeffding bound (\texttt{measure\_finiteUniformEmpiricalMean\_sub\_expect\_ge\_le}) to these bounded observations, using $m>0$ and $\varepsilon\ge0$. Replacing the expectation in the resulting deviation event by the equal restricted Fourier weight gives the claimed estimate.

**Key facts.** `FABL.restrictedFourierWeightObservationFromInputs_mem_Icc`, `FABL.measure_finiteUniformEmpiricalMean_sub_expect_ge_le`, `FABL.expect_restrictedFourierWeightTripleObservation`.
