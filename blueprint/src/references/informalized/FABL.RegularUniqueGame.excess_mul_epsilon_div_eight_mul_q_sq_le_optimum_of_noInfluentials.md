<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.excess_mul_epsilon_div_eight_mul_q_sq_le_optimum_of_noInfluentials -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimum Bound from Tester Excess

**Claim.** If the averaged-neighbor tester value is at least $\alpha+\operatorname{error}(\varepsilon)+\tau$, then the optimum value of the associated constraint satisfaction instance is at least $\tau\varepsilon/(8q^2)$.

**Proof.** The ordinary decoding bound shows that the decoding value, using default label $0$, is at least $\tau\varepsilon/(8q^2)$ (\texttt{excess\_mul\_epsilon\_div\_eight\_mul\_q\_sq\_le\_boundedOrdinaryDecodingValue}). The decoding value is at most the optimum value of the associated constraint satisfaction instance (\texttt{boundedOrdinaryDecodingValue\_le\_optimum}). Transitivity gives the stated lower bound.

**Key facts.** `FABL.RegularUniqueGame.excess_mul_epsilon_div_eight_mul_q_sq_le_boundedOrdinaryDecodingValue`, `FABL.RegularUniqueGame.boundedOrdinaryDecodingValue_le_optimum`.
