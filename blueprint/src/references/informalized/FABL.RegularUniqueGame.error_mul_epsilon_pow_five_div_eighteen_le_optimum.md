<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.error_mul_epsilon_pow_five_div_eighteen_le_optimum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimum Bound from Decoding

**Claim.** If the long-code value of the table is at least $\alpha+2\operatorname{error}(\varepsilon)$ for $0<\varepsilon\le1$, then the optimum value of the associated constraint satisfaction instance is at least $\operatorname{error}(\varepsilon)\varepsilon^5/18$.

**Proof.** Apply the decoding lower bound: the assumed tester value implies that the decoding value at threshold $\varepsilon$, with default label $0$, is at least $\operatorname{error}(\varepsilon)\varepsilon^5/18$ (\texttt{error\_mul\_epsilon\_pow\_five\_div\_eighteen\_le\_decodingValue}). The decoding value is at most the optimum value of the associated constraint satisfaction instance (\texttt{decodingValue\_le\_optimum}). Combining these inequalities gives the claim.

**Key facts.** `FABL.RegularUniqueGame.error_mul_epsilon_pow_five_div_eighteen_le_decodingValue`, `FABL.RegularUniqueGame.decodingValue_le_optimum`.
