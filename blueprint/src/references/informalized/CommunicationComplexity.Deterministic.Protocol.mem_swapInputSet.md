<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean :: CommunicationComplexity.Deterministic.Protocol.mem_swapInputSet -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in the swapped set

**Claim.** A pair $(y,x)$ belongs to the coordinate-swapped set if and only if $(x,y)$ belongs to $R$.

**Proof.** By definition, the swapped set contains precisely those pairs whose coordinates, when reversed, belong to $R$. Reversing $(y,x)$ gives $(x,y)$, proving the equivalence.
