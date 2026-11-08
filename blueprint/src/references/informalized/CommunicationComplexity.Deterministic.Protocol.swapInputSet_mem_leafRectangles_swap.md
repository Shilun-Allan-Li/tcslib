<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean :: CommunicationComplexity.Deterministic.Protocol.swapInputSet_mem_leafRectangles_swap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Swapping Leaf Rectangles

**Claim.** If $R$ is a leaf rectangle of $p$, then its coordinate swap is a leaf rectangle of the role-swapped protocol.

**Proof.** A leaf rectangle is an auxiliary leaf rectangle with both starting sets equal to the full input sets. Apply the auxiliary rectangle swap result with $A=X$ and $B=Y$. The swapped starting sets are then $Y$ and $X$, so the resulting rectangle belongs to the leaf-rectangle collection of the role-swapped protocol.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.swapInputSet_mem_leafRectanglesAux_swap`.
