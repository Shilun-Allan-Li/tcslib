<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.coalitionalInfluenceToward_criticalTribes_one_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Bound for Critical Tribes

**Claim.** For positive block width and any coalition of at most $k$ coordinates, the influence of the critical tribes function toward $1$ is at most $k2^{-w}$.

**Proof.** Apply the general tribes bound `coalitionalInfluenceToward_tribes_one_le_card_mul_inv_pow` with the critical number of blocks. It bounds the influence by the coalition's cardinality times $2^{-w}$. Since the cardinality is at most $k$ and $2^{-w}$ is nonnegative, multiplying that inequality by $2^{-w}$ gives the stated bound.

**Key facts.** `FABL.coalitionalInfluenceToward_tribes_one_le_card_mul_inv_pow`.
