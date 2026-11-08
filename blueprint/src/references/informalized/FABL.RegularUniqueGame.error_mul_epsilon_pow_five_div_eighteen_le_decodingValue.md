<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.error_mul_epsilon_pow_five_div_eighteen_le_decodingValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Global Decoding Value Bound

**Claim.** If the long-code value is at least $\alpha+2\operatorname{error}(\varepsilon)$, then decoding with notable-coordinate candidates at threshold $\varepsilon$ and default label $0$ has value at least $\operatorname{error}(\varepsilon)\varepsilon^5/18$.

**Proof.** Take the default label to be $0$. The error-to-fraction estimate (`error_le_neighborNotableVertexFraction`) shows that the fraction of vertices with a notable neighbor-averaged coordinate is at least $\operatorname{error}(\varepsilon)$. At each such vertex, the vertex decoding estimate (`epsilon_pow_five_div_eighteen_le_decodingVertexValue`) gives value at least $\varepsilon^5/18$. At vertices without such a coordinate, the vertex value is nonnegative, since it is an average of nonnegative edge decoding values (`decodingEdgeValue_nonneg`). Averaging these pointwise bounds over vertices shows that global decoding value is at least the notable-vertex fraction times $\varepsilon^5/18$. Since $\varepsilon>0$, this factor is nonnegative, so the fraction bound gives the claimed lower bound.

**Key facts.** `FABL.RegularUniqueGame.error_le_neighborNotableVertexFraction`, `FABL.RegularUniqueGame.epsilon_pow_five_div_eighteen_le_decodingVertexValue`, `FABL.RegularUniqueGame.decodingEdgeValue_nonneg`.
