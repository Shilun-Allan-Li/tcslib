<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LearningModel.lean :: FABL.fourierCoeff_sub_sparseFourierApproximation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficient after sparse approximation

**Claim.** The Fourier coefficient at $T$ of a function minus its sparse Fourier approximation is its original coefficient minus $c(T)$ when $T$ belongs to the selected family, and is unchanged otherwise.

**Proof.** First distribute the Fourier coefficient over the pointwise difference, using the linearity of finite expectation. The result is the coefficient of $f$ minus the coefficient of the sparse approximation. The latter is $c(T)$ if $T$ is in the family and zero otherwise (`FABL.fourierCoeff_sparseFourierApproximation`). Splitting into these two membership cases gives the formula.

**Key facts.** `FABL.fourierCoeff_sparseFourierApproximation`.
