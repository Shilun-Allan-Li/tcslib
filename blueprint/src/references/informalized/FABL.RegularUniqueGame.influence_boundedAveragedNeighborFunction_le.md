<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.influence_boundedAveragedNeighborFunction_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence of the Averaged Neighbor Function

**Claim.** The influence of a coordinate in the function obtained by averaging the twisted neighbor functions is at most the average of the influences of the corresponding permuted coordinates in the neighbor functions.

**Proof.** First apply the influence convexity inequality for a finite uniform average (\texttt{influence_uniformExpectation_le}) to the twisted neighbor functions. It bounds the influence of their pointwise average at the chosen coordinate by the average of their influences at that same coordinate. For each neighbor, the input permutation changes which coordinate is being measured: influence under input permutation equals influence at the inverse-permuted coordinate (\texttt{influence_comp_permuteInput}). Substituting this identity gives the claimed bound over neighbors.

**Key facts.** `FABL.RegularUniqueGame.influence_uniformExpectation_le`, `FABL.RegularUniqueGame.influence_comp_permuteInput`.
