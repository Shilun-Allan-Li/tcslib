<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Parity.lean :: BoolCircuit.isDual_xorPairUp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality Under Pairwise XOR Construction

**Claim.** If every pair in a list of circuit pairs is dual, then every pair produced by combining consecutive pairs with the specified XOR construction is dual as well.

**Proof.** Proceed by cases on the list. For the empty list the claim is vacuous. For a singleton list, the construction leaves its pair unchanged, so its duality follows directly from the hypothesis. For a list beginning with $p,q$ and followed by a tail, apply the same claim inductively to the tail; the hypothesis restricts to that tail, so every pair produced from it is dual. The first output pair is the XOR combination of $p$ and $q$, and is dual by the fact that this construction preserves duality for two dual input pairs (`xorNode_isDual`). Every output is either this first pair or one of the pairs produced from the tail, proving the result.

**Key facts.** `BoolCircuit.xorNode_isDual`.
