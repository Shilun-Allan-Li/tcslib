<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictionWeights.lean :: FABL.sum_abs_indexedFourierCoeff_restrictionFourierCoeff_le_fourierOneNorm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Norm of Restriction Coefficients

**Claim.** The Fourier one-norm, over the signs fixed outside $J$, of the restriction Fourier coefficient function at a free-coordinate set $S\subseteq J$ is at most the Fourier one-norm of $f$.

**Proof.** For each fixed-coordinate frequency $T$, the coefficient of the restriction Fourier coefficient function equals the Fourier coefficient of $f$ at the union of the lifted free frequency $S$ and lifted fixed frequency $T$ (`indexedFourierCoeff_restrictionFourierCoeff`). Thus the left side is the sum over $T$ of the absolute values of these coefficients for the chosen $S$. Each summand is nonnegative, so this partial sum is at most the sum over all free frequencies $S'$ and all fixed frequencies $T$. The split-frequency identity `sum_abs_split_fourierCoeff_eq_fourierOneNorm` identifies that full sum with the Fourier one-norm of $f$.

**Key facts.** `FABL.indexedFourierCoeff_restrictionFourierCoeff`, `FABL.sum_abs_split_fourierCoeff_eq_fourierOneNorm`.
