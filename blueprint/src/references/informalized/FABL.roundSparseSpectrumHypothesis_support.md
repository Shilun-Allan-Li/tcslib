<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.roundSparseSpectrumHypothesis_support -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Support preservation under rounding

**Claim.** For every natural number $k$ and every sparse Fourier hypothesis on $n$ coordinates, rounding its coefficients preserves its support.

**Proof.** The rounded hypothesis is formed by applying `ofCoefficients` to the original support, changing only the coefficient function. Since `ofCoefficients` stores that support unchanged, the two supports are definitionally equal.
