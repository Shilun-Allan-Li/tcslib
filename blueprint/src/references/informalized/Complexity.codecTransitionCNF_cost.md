<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecTransitionCNF_cost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition Formula Cost

**Claim.** The transition CNF cost is at most the product of the numbers of position choices, transition cases, and encoded bits, multiplied by $2^{3k+7}(3k+8)$.

**Proof.** The transition formula is a concatenation, over every gate index, of the CNF assigned to that gate. Each such gate CNF has cost at most $2^{3k+7}(3k+8)$ by the gate-CNF cost bound (\texttt{Complexity.codecGateCNF_spec}). The cost of a concatenation of CNFs is at most the number of list entries times a common upper bound on each entry’s cost (\texttt{Complexity.codecCnfCost_flatMap_le}). The gate indices range over the product of positions, transition cases, and encoded bits; their number is therefore the product of the three corresponding cardinalities. Multiplying this count by the per-gate bound gives the stated inequality.

**Key facts.** `Complexity.codecCnfCost_flatMap_le`, `Complexity.codecGateCNF_spec`.
