<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.tautDual_clause -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polarity-Flipping Scan of a Clause

**Claim.** Scanning the serialization of a clause followed by a bit string, from the clause state, yields the serialization of the clause with each literal's polarity negated, followed by scanning the remaining string from the formula state.

**Proof.** Induct on the clause. For the empty clause, its serialization is just the terminator, and the scan agrees directly with the empty transformed clause followed by the formula-state scan of the remainder. For a clause consisting of a literal followed by a shorter clause, the clause serialization splits into the serialization of that literal followed by the shorter clause serialization. The single-literal scan identity (`tautDual_literal`) transforms the first segment by flipping its polarity and leaves the scan in the clause state for the remaining segment. Apply the induction hypothesis to that shorter clause and the remainder, then reassociate the concatenated lists. This gives exactly the serialization of the polarity-flipped clause followed by the formula-state scan of the appended bit string.

**Key facts.** `Complexity.tautDual_literal`.
