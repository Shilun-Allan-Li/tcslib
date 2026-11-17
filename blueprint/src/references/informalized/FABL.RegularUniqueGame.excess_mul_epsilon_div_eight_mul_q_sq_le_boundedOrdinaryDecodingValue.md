<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.excess_mul_epsilon_div_eight_mul_q_sq_le_boundedOrdinaryDecodingValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ordinary Decoding Lower Bound

**Claim.** If the averaged-neighbor tester value is at least $\alpha+\operatorname{error}(\varepsilon)+\tau$, then the ordinary decoding value at threshold $\varepsilon$, using default label $0$, is at least $\tau\varepsilon/(8q^2)$.

**Proof.** First, the excess bound shows that the fraction of vertices with an influential averaged-neighbor coordinate is at least $\tau$ (\texttt{excess\_le\_boundedNeighborInfluentialVertexFraction}). At each such vertex, the vertex decoding value is at least $\varepsilon/(8q^2)$ (\texttt{epsilon\_div\_eight\_mul\_q\_sq\_le\_boundedOrdinaryDecodingVertexValue}). At every other vertex, its decoding value is nonnegative: it is an average of nonnegative edge decoding values (\texttt{boundedOrdinaryDecodingEdgeValue\_nonneg}). Averaging these pointwise bounds over vertices, and using that the indicator of being influential has average equal to the influential-vertex fraction, gives a decoding value of at least that fraction times $\varepsilon/(8q^2)$. The scale factor is nonnegative because $\varepsilon>0$ and $q>0$. Multiplying the fraction bound by this factor yields $\tau\varepsilon/(8q^2)$ as required.

**Key facts.** `FABL.RegularUniqueGame.excess_le_boundedNeighborInfluentialVertexFraction`, `FABL.RegularUniqueGame.epsilon_div_eight_mul_q_sq_le_boundedOrdinaryDecodingVertexValue`, `FABL.RegularUniqueGame.boundedOrdinaryDecodingEdgeValue_nonneg`.
