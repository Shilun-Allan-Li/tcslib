<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.oracleRelabel_wellFormed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relabeling preserves well-formedness

**Claim.** If an oracle Turing machine's query, positive-answer, and negative-answer states are pairwise distinct, then relabeling those states through a bijection preserves their pairwise distinctness.

**Proof.** Each required inequality follows from injectivity of the state bijection: if two relabeled designated states were equal, injectivity would imply that the corresponding original states were equal, contrary to the assumed well-formedness. Applying this to the query and positive-answer states, the query and negative-answer states, and the two answer states proves the result.
