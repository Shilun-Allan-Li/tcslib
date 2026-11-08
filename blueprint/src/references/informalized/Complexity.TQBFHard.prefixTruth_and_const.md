<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean :: Complexity.TQBFHard.prefixTruth_and_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conjunction Through a Quantified Prefix

**Claim.** Truth of the quantified prefix with matrix $K\land P(\tau)$ is equivalent to $K$ holding together with truth of the same prefix with matrix $P(\tau)$.

**Proof.** Induct on the quantifier list, with the starting assignment and index arbitrary. For the empty prefix the assertion is the matrix equivalence itself. For an existential first quantifier, apply the induction hypothesis after updating the assignment for each chosen Boolean value; the constant proposition $K$ can then be moved outside the existential quantifier. For a universal first quantifier, the induction hypothesis gives $K\land P$ for every Boolean value. This implies $K$ (use either value, for example false) and that $P$ holds for every value. Conversely, a single proof of $K$ together with universal truth of $P$ gives the conjunction for each value.
