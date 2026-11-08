<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetBasic.lean :: CommunicationComplexity.Deterministic.Protocol.swap_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Role Swap Preserves Output

**Claim.** Running the role-swapped protocol on $(y,x)$ returns the same value as running the original protocol on $(x,y)$.

**Proof.** Induct on the protocol. At an output node both executions return its label. At an Alice node, the swapped protocol has a Bob node testing the same function on its second input; on $(y,x)$ this test evaluates at $x$, just as the original Alice test does. Both executions therefore continue into the corresponding child, where the induction hypothesis gives equal outputs. At an original Bob node, the swapped Alice test evaluates at $y$, again matching the original test, and the induction hypothesis applies to the selected child.
