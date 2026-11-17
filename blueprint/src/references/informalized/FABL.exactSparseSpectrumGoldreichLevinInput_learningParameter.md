<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.exactSparseSpectrumGoldreichLevinInput_learningParameter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Learning Parameter Identity

**Claim.** For natural numbers $n$ and $k$ with $n>0$, the learning parameter of the exact sparse-spectrum Goldreich–Levin input equals the degree-$(k+1)$ Fourier coefficient accuracy parameter.

**Proof.** Equality of these positive rational parameters follows by comparing their rational values. The input's learning parameter, after casting to the reals, equals its encoded accuracy (`DeterministicGoldreichLevinInput.learningParameter_cast`); for this input the numerator and denominator are $1$ and $4\cdot 2^k$, so its rational value is $1/(4\cdot 2^k)$. The degree-$(k+1)$ coefficient accuracy has value $2^{-(k+2)}$ (`degreeFourierCoefficientAccuracy_value`). Since $4\cdot 2^k=2^{k+2}$, these are the same rational number. Two elements of the subtype of positive learning parameters with the same value are equal.

**Key facts.** `FABL.DeterministicGoldreichLevinInput.learningParameter_cast`, `FABL.degreeFourierCoefficientAccuracy_value`.
