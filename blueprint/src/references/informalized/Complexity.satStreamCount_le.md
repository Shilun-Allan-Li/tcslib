<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamCount_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Round-count bound

**Claim.** For every CNF formula $\varphi$, its round count is at most the length of its binary serialization.

**Proof.** Induct on the list of clauses. For the empty formula, the round count and serialization length satisfy the bound directly. For a formula $C :: \varphi$, the induction hypothesis bounds the count for the remaining formula. The clause measure estimate gives $|C|+1 \leq |\mathrm{serializeClause}(C)|$. The serialization of $C :: \varphi$ has length one plus the length of the serialization of $C$, plus the length of the remaining formula's serialization. Combining these expressions with the induction hypothesis yields the desired bound.

**Key facts.** `Complexity.sat_clause_measure`.
