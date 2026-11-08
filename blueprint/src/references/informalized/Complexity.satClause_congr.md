<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satClause_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clause evaluation under agreement

**Claim.** If two truth assignments agree at the variable index of every literal in a clause, then the clause has the same evaluation under both assignments.

**Proof.** The clause evaluation depends only on the truth values assigned to the variables occurring in the clause. For any variable used in evaluating the clause, its positive or negative literal occurs in the clause. Applying the assumed agreement to that literal shows that the two assignments give the same value at the variable. Hence all values consulted in evaluating the clause agree, so the evaluations are equal.
