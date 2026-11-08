<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetComposition.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.prod_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity for two protocols

**Claim.** The complexity of the product protocol for two finite-message protocols is the sum of their individual complexities.

**Proof.** Induct on the first protocol. If it is an output node, the product construction reindexes the second protocol's inputs and maps its output to a pair with the fixed first value. These operations leave the communication cost equal to the second protocol's complexity, while the first protocol has complexity zero. If the first protocol begins with an Alice message, the product begins with the same message, and after each possible message continues with the product of the corresponding subtree and the second protocol. By induction, each continuation has complexity equal to that subtree's complexity plus the fixed complexity of the second protocol. The supremum over messages of these continuation costs is the supremum of the subtree costs plus that fixed constant (`finset_sup_add_const`). Adding the cost of the initial message then gives the first protocol's complexity plus the second's. When the first protocol begins with a Bob message, the same argument applies to Bob's message branches.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.finset_sup_add_const`.
