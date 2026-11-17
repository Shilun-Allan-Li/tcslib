<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.epsilon_div_eight_mul_q_sq_le_boundedOrdinaryDecodingVertexValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ordinary Decoding Value Bound

**Claim.** If a coordinate has stable influence greater than $\varepsilon$ in the neighbor-averaged, constraint-permuted function at a vertex, then the ordinary decoding value at that vertex is at least $\varepsilon/(8q^2)$.

**Proof.** Choose such a coordinate $i$. For each neighbor, consider whether its inverse-permuted image is influential at the neighboring vertex. If it is, the edge decoding bound gives value at least $1/(4q^2)$; if it is not, the claimed pointwise lower bound is zero and follows from nonnegativity of the edge value (`boundedOrdinaryDecodingEdgeValue_nonneg`). Averaging these inequalities over neighbors bounds the vertex value below by $1/(4q^2)$ times the fraction of neighbors where the image is influential. The influence-to-probability estimate (`half_epsilon_le_boundedInfluentialNeighborProbability`) says this fraction is at least $\varepsilon/2$. Multiplying gives $\varepsilon/(8q^2)$.

**Key facts.** `FABL.RegularUniqueGame.one_div_four_mul_q_sq_le_boundedOrdinaryDecodingEdgeValue`, `FABL.RegularUniqueGame.boundedOrdinaryDecodingEdgeValue_nonneg`, `FABL.RegularUniqueGame.half_epsilon_le_boundedInfluentialNeighborProbability`.
