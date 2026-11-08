<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.sum_abs_fourierCoeff_tupleSymmDiff_eq_parityTuple_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier Weights of Parity Tuples

**Claim.** For a function whose nonzero Fourier coefficients are all indexed by sets of cardinality $k$, the sum of absolute products over all ordered $q$-tuples with empty symmetric difference equals the sum of products of absolute Fourier coefficients over those tuples whose sets all have cardinality $k$.

**Proof.** Call a tuple parity-admissible when its symmetric difference is empty, and call it good when it is parity-admissible and every set in it has cardinality $k$. Any parity-admissible tuple that is not good has some coordinate set of cardinality different from $k$. By the homogeneity hypothesis, the Fourier coefficient at that set must be zero; hence the product of coefficients for the tuple, and its absolute value, is zero. Removing all such zero terms leaves the sum over good tuples. A good tuple is exactly an element of the subtype defining `LevelKParityTuple`, so reindexing by that subtype identifies the remaining sum with the claimed sum. Finally, the absolute value of a finite product is the product of the absolute values, giving the specified weights.
