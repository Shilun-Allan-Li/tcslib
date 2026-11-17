<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetComposition.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.pi_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity of product protocols

**Claim.** The complexity of the product of a finite family of protocols equals the sum of their individual complexities.

**Proof.** Induct on the number of factors. With no factors, the product protocol outputs the unique empty tuple and has complexity zero, matching the empty sum. For the successor case, the product construction first runs the protocol for the head coordinate, then binds its output to the mapped product protocol on the tail coordinates. By induction, the latter protocol has constant complexity equal to the sum of the tail complexities, regardless of the head output. The constant-cost bind formula therefore gives the complexity of the whole construction as the head protocol's complexity plus that tail sum (`bind_complexity_const`). Splitting the finite sum into its head term and tail terms yields the desired equality.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_complexity_const`.
