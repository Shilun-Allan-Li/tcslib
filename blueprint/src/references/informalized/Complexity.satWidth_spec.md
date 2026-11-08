<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satWidth_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width Test Characterization

**Claim.** The width test of a CNF formula returns true if and only if every clause has at most three literal occurrences.

**Proof.** The width test applies the Boolean list predicate to the formula's clauses, with each clause passing exactly when its length is at most three. A list-wide Boolean predicate returns true precisely when each element passes; hence the test is true exactly when every clause satisfies that bound.
