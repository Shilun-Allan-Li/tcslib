<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetComposition.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.map_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity under output post-processing

**Claim.** Applying any function to a protocol's output leaves its communication complexity unchanged.

**Proof.** Proceed by structural induction on the protocol. At an output node, mapping changes only the output value, while both complexities are zero. At an Alice node, mapping preserves the same query and maps each continuation. By the induction hypothesis, every mapped continuation has the same complexity as its original; thus the supremum of continuation complexities, and hence the node's complexity, is unchanged. The Bob case is identical, with the query depending on Bob's input.
