<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.CNFFormula.clauseAt_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership of an indexed clause

**Claim.** If $i$ is a valid index among the clauses of a CNF formula $\psi$, then the clause at position $i$ belongs to the list of clauses of $\psi$.

**Proof.** The clause at position $i$ is obtained by indexing into the formula’s clause list. Because $i$ is within the list’s length, that indexed element is a member of the list.
