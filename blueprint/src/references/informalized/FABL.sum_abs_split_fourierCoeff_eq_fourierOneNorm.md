<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictionWeights.lean :: FABL.sum_abs_split_fourierCoeff_eq_fourierOneNorm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Norm Under a Coordinate Split

**Claim.** Summing the absolute Fourier coefficients over all choices of a subset of $J$ and a subset of its complement gives the Fourier one-norm of $f$.

**Proof.** First combine the two nested finite sums into a single sum over pairs $(S,T)$, where $S$ is a subset of $J$ and $T$ is a subset of its complement. The frequency-splitting equivalence sends each such pair to the union of the corresponding coordinate subsets, and its value is exactly `liftFreeFrequency S ∪ liftFixedFrequency T` (the frequency-splitting formula, `FABL.frequencySplitEquiv_apply`). Reindexing the sum by this equivalence therefore makes it the sum of $|\widehat f(U)|$ over every subset $U$ of the full coordinate set. By definition, this is the Fourier one-norm of $f$.

**Key facts.** `FABL.frequencySplitEquiv_apply`.
