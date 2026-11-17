<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.stableInfluence_averagedNeighborFunction_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable Influence of an Averaged Neighbor Function

**Claim.** At parameter $1-\varepsilon$, the stable influence of the averaged neighbor function at a vertex and coordinate is at most the uniform neighbor average of the stable influences of the table functions at the corresponding inverse-permuted coordinates.

**Proof.** The assumption $0\leq\varepsilon\leq1$ gives $0\leq1-\varepsilon\leq1$. Apply the convexity inequality for stable influence under a uniform function average (`stableInfluence_uniformExpectation_le`) to the twisted neighbor functions at this parameter and coordinate. The pointwise average of these functions is the averaged neighbor function. For each neighbor, the twisted function is the table function composed with the edge's input permutation; stable influence under such a composition is the influence of the original function at the inverse-permuted coordinate (`stableInfluence_comp_permuteInput`). Rewriting these terms gives the claimed bound.

**Key facts.** `FABL.RegularUniqueGame.stableInfluence_uniformExpectation_le`, `FABL.RegularUniqueGame.stableInfluence_comp_permuteInput`.
