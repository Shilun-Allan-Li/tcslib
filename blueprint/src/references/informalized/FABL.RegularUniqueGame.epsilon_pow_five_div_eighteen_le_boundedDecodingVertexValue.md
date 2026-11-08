<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.epsilon_pow_five_div_eighteen_le_boundedDecodingVertexValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Decoding Value Bound

**Claim.** If a coordinate has stable influence greater than $\varepsilon$ in the neighbor-averaged, constraint-permuted function at a vertex, then the bounded decoding value at that vertex is at least $\varepsilon^5/18$.

**Proof.** Choose a coordinate $i$ witnessing the hypothesis. For each neighbor, if the inverse-permuted coordinate is notable at the neighboring vertex, the edge estimate gives decoding value at least $\varepsilon^4/9$. Otherwise, the corresponding pointwise lower bound is zero, which is at most the edge value by nonnegativity (`boundedDecodingEdgeValue_nonneg`). Averaging over neighbors, the vertex value is therefore at least $\varepsilon^4/9$ times the fraction of neighbors for which that coordinate is notable. By the notable-neighbor probability estimate (`half_epsilon_le_boundedNotableNeighborProbability`), this fraction is at least $\varepsilon/2$. Thus the vertex value is at least $(\varepsilon^4/9)(\varepsilon/2)=\varepsilon^5/18$.

**Key facts.** `FABL.RegularUniqueGame.epsilon_pow_four_div_nine_le_boundedDecodingEdgeValue`, `FABL.RegularUniqueGame.boundedDecodingEdgeValue_nonneg`, `FABL.RegularUniqueGame.half_epsilon_le_boundedNotableNeighborProbability`.
