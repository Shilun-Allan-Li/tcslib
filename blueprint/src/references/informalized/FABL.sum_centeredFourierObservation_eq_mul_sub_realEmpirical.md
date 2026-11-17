<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FourierEstimation.lean :: FABL.sum_centeredFourierObservation_eq_mul_sub_realEmpirical -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Centered Fourier observation sum

**Claim.** The sum of the centered Fourier observations over a positive number $m$ of samples equals $m$ times the difference between their empirical Fourier coefficient and the Fourier coefficient.

**Proof.** Distribute the finite sum across each difference. The sum of the observation terms remains unchanged, while the constant Fourier coefficient is repeated once for each of the $m$ sample indices, contributing $m\widehat f(S)$. By definition, the empirical coefficient is the sum of the observations divided by $m$. Since $m>0$, its real cast is nonzero, and rearranging this defining identity gives the claimed equality.
