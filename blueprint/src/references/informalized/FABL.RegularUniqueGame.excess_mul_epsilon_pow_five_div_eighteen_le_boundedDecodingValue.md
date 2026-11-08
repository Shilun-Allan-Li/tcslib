<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.excess_mul_epsilon_pow_five_div_eighteen_le_boundedDecodingValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Excess and Decoding Value

**Claim.** If the averaged-neighbor tester value is at least $\alpha+\operatorname{error}(\varepsilon)+\tau$, then the decoding value at threshold $\varepsilon$, using default label $0$, is at least $\tau\varepsilon^5/18$.

**Proof.** The excess bound implies that at least a fraction $\tau$ of vertices have a notable coordinate in their averaged-neighbor function (\texttt{excess\_le\_boundedNeighborNotableVertexFraction}). For each such vertex, the decoding vertex value is at least $\varepsilon^5/18$ (\texttt{epsilon\_pow\_five\_div\_eighteen\_le\_boundedDecodingVertexValue}). At vertices without a notable coordinate, the decoding vertex value is nonnegative, as it averages nonnegative edge decoding values (\texttt{boundedDecodingEdgeValue\_nonneg}). Averaging over vertices therefore bounds the decoding value below by the notable-vertex fraction times $\varepsilon^5/18$. This factor is nonnegative since $\varepsilon>0$. Multiplying the fraction bound by it proves the desired inequality.

**Key facts.** `FABL.RegularUniqueGame.excess_le_boundedNeighborNotableVertexFraction`, `FABL.RegularUniqueGame.epsilon_pow_five_div_eighteen_le_boundedDecodingVertexValue`, `FABL.RegularUniqueGame.boundedDecodingEdgeValue_nonneg`.
