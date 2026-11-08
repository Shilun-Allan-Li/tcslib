<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.stableInfluence_boundedAveragedNeighborFunction_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable Influence of a Bounded Neighbor Average

**Claim.** At parameter $1-\varepsilon$, the stable influence of the bounded averaged neighbor function is at most the uniform neighbor average of the table functions' stable influences at the corresponding inverse-permuted coordinates.

**Proof.** Since $0\leq\varepsilon\leq1$, the parameter $1-\varepsilon$ lies in $[0,1]$. Apply the uniform-average convexity inequality for stable influence (`stableInfluence_uniformExpectation_le`) to the bounded twisted neighbor functions. Their pointwise uniform average is the bounded averaged neighbor function. Each twisted function composes the table function with the edge permutation, and stable influence of such a composition equals the original stable influence at the inverse-permuted coordinate (`stableInfluence_comp_permuteInput`). These identifications yield the stated inequality.

**Key facts.** `FABL.RegularUniqueGame.stableInfluence_uniformExpectation_le`, `FABL.RegularUniqueGame.stableInfluence_comp_permuteInput`.
