<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetComposition.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.map_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution after output mapping

**Claim.** Running a protocol whose outputs have been mapped by $g$ gives the result of the original run with $g$ applied to it.

**Proof.** Proceed by structural induction on the protocol. At an output node with value $a$, the mapped protocol returns $g(a)$, which is $g$ of the original output. At an Alice node, both protocols inspect the same query on $x$ and select the same continuation; applying the induction hypothesis to that continuation gives the result. At a Bob node, they likewise inspect the same query on $y$, and the induction hypothesis again gives the equality.
