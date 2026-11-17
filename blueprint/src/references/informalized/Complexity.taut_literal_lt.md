<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_literal_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Literal Index Bound

**Claim.** If a clause belongs to a CNF formula and a literal belongs to that clause, the literal’s variable index is less than the formula’s variable count.

**Proof.** The variable count is the fold maximum of the list formed by flattening the formula’s clauses and replacing each literal index $v$ by $v+1$. The membership hypotheses put $v+1$ in this flattened list. The fold-maximum bound (`Complexity.taut_le_max`) therefore gives $v+1\leq N(\varphi)$, which is equivalent to $v<N(\varphi)$.

**Key facts.** `Complexity.taut_le_max`.
