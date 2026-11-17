<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.excess_mul_epsilon_pow_five_div_eighteen_le_optimum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Excess Forces CSP Value

**Claim.** Under the stated hypotheses, if the tester’s averaged acceptance value on the table is at least $\alpha+\operatorname{error}(\epsilon)+\tau$, then $\tau\epsilon^5/18$ is at most the optimum value of the constraint satisfaction instance associated to $G$.

**Proof.** Apply the excess-to-decoding estimate to the table: the assumed acceptance lower bound implies that its decoded value is at least $\tau\epsilon^5/18$. The decoded value is at most the CSP optimum, by the bound comparing bounded decoding with the optimum (using any default label, available since the label set is nonempty). Chaining these inequalities gives the claim.

**Key facts.** `FABL.RegularUniqueGame.excess_mul_epsilon_pow_five_div_eighteen_le_boundedDecodingValue`, `FABL.RegularUniqueGame.boundedDecodingValue_le_optimum`.
