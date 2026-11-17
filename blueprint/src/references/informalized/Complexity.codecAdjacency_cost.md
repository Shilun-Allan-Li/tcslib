<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecAdjacency_cost -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adjacency Encoding Cost Bound

**Claim.** If the machine coefficient is at most $C$, then the cost of the input-equality CNF concatenated with the transition CNF is at most $(6+T)C(s+n+2)^{k+2}$, where $T$ is the transition coefficient in the statement.

**Proof.** First, the coefficient hypothesis implies $C\ge1$. Put $X=(s+n+2)^{k+2}$. Since $n\le s+n+2$ and $s+n+2\ge1$, we have $n\le X\le CX$. The cost of concatenating the two CNFs is the sum of their costs (`Complexity.codecCnfCost_append`). The input-equality CNF costs at most $6n$ (`Complexity.codecInputEquality_cost`), while the transition CNF costs at most $TX$ times $C$ (`Complexity.codecTransitionCNF_cost_poly`). Replacing $n$ by its bound $CX$ gives a total cost at most $6CX+TCX=(6+T)CX$, as required.

**Key facts.** `Complexity.codecCnfCost_append`, `Complexity.codecInputEquality_cost`, `Complexity.codecTransitionCNF_cost_poly`.
