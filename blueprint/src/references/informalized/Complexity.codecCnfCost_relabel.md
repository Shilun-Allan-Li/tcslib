<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecCnfCost_relabel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance of CNF cost under relabeling

**Claim.** Relabeling the variables of a CNF by any function preserves its cost, the sum over clauses of one plus the clause length.

**Proof.** Relabeling a CNF maps each clause by relabeling its literals, and relabeling a clause maps each literal without changing the number of literals. Thus the mapped list of clauses has the same clause lengths as before, term by term; summing the quantities one plus those lengths gives the same cost.
