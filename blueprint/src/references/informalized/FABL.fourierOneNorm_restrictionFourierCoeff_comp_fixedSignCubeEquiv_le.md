<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictionWeights.lean :: FABL.fourierOneNorm_restrictionFourierCoeff_comp_fixedSignCubeEquiv_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier norm of a restriction coefficient

**Claim.** For any real-valued function on the cube, any coordinate set $J$, and any $S\subseteq J$, the Fourier one-norm of the function of outside signs given by the restriction’s coefficient at $S$ is at most the Fourier one-norm of the original function.

**Proof.** Use the reindexing equality (\texttt{fourierOneNorm_restrictionFourierCoeff_comp_fixedSignCubeEquiv_eq}) to write the left side as the sum of absolute values of the indexed Fourier coefficients of the restriction coefficient function over subsets of the outside-coordinate set. The bound for that sum (\texttt{sum_abs_indexedFourierCoeff_restrictionFourierCoeff_le_fourierOneNorm}) says it is at most the Fourier one-norm of the original function, giving the result.

**Key facts.** `FABL.fourierOneNorm_restrictionFourierCoeff_comp_fixedSignCubeEquiv_eq`, `FABL.sum_abs_indexedFourierCoeff_restrictionFourierCoeff_le_fourierOneNorm`.

**Caveat.** The informal statement mentions a sparsity bound as well, but the formal statement and proof supplied establish only the Fourier one-norm bound.
