<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/CNF.lean :: Complexity.falsifyingCNF_numVars -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truth-Table CNF Variable Count

**Claim.** The variable count of the truth-table CNF of a Boolean function on $\ell$ bits is at most $\ell$.

**Proof.** The variable count is obtained by taking the maximum, with $0$ as the initial value, of one plus each variable index appearing in the clauses. Every clause comes from a vector $v$ and lists exactly the positions $i<\ell$; thus each index-plus-one is at most $\ell$. The maximum of these values, including the initial $0$, is consequently at most $\ell$ (`Complexity.foldr_max_le_of_forall`).

**Key facts.** `Complexity.foldr_max_le_of_forall`.
