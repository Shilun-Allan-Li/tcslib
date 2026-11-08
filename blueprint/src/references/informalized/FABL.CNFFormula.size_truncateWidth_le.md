<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.CNFFormula.size_truncateWidth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size under width truncation

**Claim.** The number of clauses remaining after retaining only clauses of width at most $w$ is no greater than the original number of clauses.

**Proof.** Width truncation filters the clause list, keeping only those clauses whose width is at most $w$. A filtered list cannot be longer than the original list, so its length, which is the truncated formula’s size, is at most the original size.
