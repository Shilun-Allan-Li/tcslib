<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: CNF.dual_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duplicate-free terms under dualization

**Claim.** If every clause of a CNF has no repeated literal, then every term in its De Morgan dual DNF has no repeated literal.

**Proof.** Any term in the dual DNF is obtained by flipping each literal in one of the original clauses. The flip operation is injective (`Literal.flipNeg_injective`), so it sends distinct literals to distinct literals. Thus the image of a duplicate-free clause is still duplicate-free, proving the result for each term.

**Key facts.** `Literal.flipNeg_injective`.
