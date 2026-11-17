<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean :: CommunicationComplexity.Deterministic.Protocol.aux_bob_bit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bob’s Bit on a Leaf Rectangle

**Claim.** If a leaf rectangle arises from a protocol restricted to inputs whose second coordinate lies in $B\cap\{y:f(y)=b\}$, then every point in that rectangle has second coordinate satisfying $f(y)=b$.

**Proof.** By the containment property of auxiliary leaf rectangles (`CommunicationComplexity.Deterministic.Protocol.aux_subset`), the rectangle lies inside $A\times(B\cap\{y:f(y)=b\})$. Thus any point $(x,y)$ in it has $y\in B\cap\{y:f(y)=b\}$, which gives $f(y)=b$.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.aux_subset`.
