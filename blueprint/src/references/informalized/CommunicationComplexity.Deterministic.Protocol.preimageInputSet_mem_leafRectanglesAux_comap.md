<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean :: CommunicationComplexity.Deterministic.Protocol.preimageInputSet_mem_leafRectanglesAux_comap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pullback of Constrained Leaf Rectangles

**Claim.** For arbitrary input maps $f_X$ and $f_Y$, pulling back a leaf rectangle of $p$ relative to $A\times B$ gives a leaf rectangle of the pulled-back protocol relative to $f_X^{-1}(A)\times f_Y^{-1}(B)$.

**Proof.** Induct on the structure of $p$, keeping the constraint sets $A$ and $B$ arbitrary. If $p$ is an output node, its only constrained leaf rectangle is $A\times B$. Its pullback is exactly $f_X^{-1}(A)\times f_Y^{-1}(B)$, the sole leaf rectangle of the pulled-back output protocol. If Alice branches, membership in the family of leaf rectangles means membership in the family for one of the two child protocols, with Alice’s constraint narrowed to $A\cap\{x:f(x)=b\}$ for the corresponding bit $b$. Apply the induction hypothesis to that child and constraint; the pulled-back rectangle then belongs to the corresponding branch of the pulled-back protocol’s union of leaf-rectangle families. If Bob branches, the same reasoning applies with Bob’s constraint narrowed to $B\cap\{y:f(y)=b\}$.
