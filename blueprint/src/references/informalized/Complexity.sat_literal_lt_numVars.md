<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.sat_literal_lt_numVars -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Literal Indices Below the Variable Bound

**Claim.** Every literal in a clause of a CNF formula has variable index strictly less than the formula's variable count.

**Proof.** The variable count is the maximum, with initial value zero, of the numbers one greater than the indices of all literals appearing in the formula. Since the clause belongs to the formula and the literal belongs to the clause, the literal's index plus one occurs in that flattened list. A list fold by maximum is at least each entry, so the index plus one is at most the variable count. Hence the index is strictly smaller than the variable count.
