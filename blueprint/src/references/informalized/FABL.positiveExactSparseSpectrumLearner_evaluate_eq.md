<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.positiveExactSparseSpectrumLearner_evaluate_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Exact Recovery by the Sparse Spectrum Learner

**Claim.** For $n>0$, if a sign-valued function on the Boolean cube has at most $2^{k+1}$ nonzero Fourier coefficients, the positive exact sparse spectrum learner with parameters $n,k$ returns a hypothesis whose evaluation agrees with the function at every input.

**Proof.** 1. Set the learner's input parameters to those prescribed by $n$ and $k$. The spectral sparsity hypothesis bounds the Fourier one-norm of the target by the input's Fourier bound (\(\texttt{fourierOneNorm\_toReal\_le\_of\_spectralSparsity\_le}\)). Thus the deterministic Goldreich–Levin correctness theorem applies (\(\texttt{deterministicGoldreichLevinProgram\_isCorrectOutput}\)). It supplies an active family that is complete for the target's sufficiently large Fourier coefficients and meets the threshold needed for the second stage.

2. The learner runs the deterministic Goldreich–Levin program and then uses its resulting active family in the coefficient-estimation program. The run-of-a-bind rule identifies this sequential execution with first running the program and then running the selected second stage (\(\texttt{DeterministicQueryProgram.runWithCost\_bind}\)). The active-family and threshold conclusions ensure that this second stage is the coefficient program. Its output is exactly the hypothesis formed from the oracle answers on the prescribed sample points (\(\texttt{DeterministicQueryProgram.runWithCost\_deterministicGoldreichLevinCoefficientProgram}\)).

3. The learner maps that hypothesis through the rounding operation. Running a mapped program applies the map to its output while preserving its cost (\(\texttt{DeterministicQueryProgram.runWithCost\_map}\)). The theorem on rounded deterministic Goldreich–Levin hypotheses says that, for a complete family under the assumed spectral sparsity bound, this rounded hypothesis evaluates to the target everywhere (\(\texttt{roundedDeterministicGoldreichLevinHypothesis\_evaluate\_eq}\)). Applying it to the family from the correctness theorem proves exact recovery.

**Key facts.** `FABL.fourierOneNorm_toReal_le_of_spectralSparsity_le`, `FABL.deterministicGoldreichLevinProgram_isCorrectOutput`, `FABL.DeterministicQueryProgram.runWithCost_bind`, `FABL.DeterministicQueryProgram.runWithCost_deterministicGoldreichLevinCoefficientProgram`, `FABL.DeterministicQueryProgram.runWithCost_map`, `FABL.roundedDeterministicGoldreichLevinHypothesis_evaluate_eq`.

**Caveat.** The provided statement for the deterministic Goldreich–Levin correctness theorem does not define the fields of `IsCorrectOutput`; the proof uses its consequences that the active family is complete and satisfies the stated threshold condition.
