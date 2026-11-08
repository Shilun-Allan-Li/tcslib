<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.relativeHammingDist_unflattenBinaryMatrix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relative Distance Under Matrix Unflattening

**Claim.** Representing binary matrices by their coordinate arrays preserves the relative Hamming distance between functions on those matrices.

**Proof.** Rewrite each relative distance as the uniform probability of disagreement (\texttt{uniformProbability\_ne\_eq\_relativeHammingDist}). The coordinate-array representation is a bijection between the matrix domain and the array domain, so changing variables along this equivalence preserves the uniform average. For a matrix $A$, unflattening its flattened array recovers $A$ (\texttt{unflattenBinaryMatrix\_flattenBinaryMatrix}); therefore the disagreement indicators before and after the change of variables are equal. Their uniform probabilities, and hence the relative distances, agree.

**Key facts.** `FABL.uniformProbability_ne_eq_relativeHammingDist`, `FABL.unflattenBinaryMatrix_flattenBinaryMatrix`.
