<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.roundSparseSpectrumHypothesis_coefficient -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coefficient after spectrum rounding

**Claim.** For every supported character, its coefficient in the rounded sparse Fourier hypothesis is the original coefficient rounded to the prescribed granularity at level $k+1$.

**Proof.** The rounded hypothesis is defined with the same support and with each coefficient assigned by applying the degree-granularity rounding operation at level $k+1$. Evaluating its coefficient at a supported character therefore gives exactly that rounded original coefficient; this is definitional unfolding.
