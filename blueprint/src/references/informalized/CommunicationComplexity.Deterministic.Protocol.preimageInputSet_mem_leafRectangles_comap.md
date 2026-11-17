<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetRectangle.lean :: CommunicationComplexity.Deterministic.Protocol.preimageInputSet_mem_leafRectangles_comap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pullback of Leaf Rectangles

**Claim.** For arbitrary maps on the two input spaces, the pullback of a leaf rectangle of a protocol is a leaf rectangle of the protocol obtained by precomposing its message functions with those maps.

**Proof.** Apply the constrained pullback result to the entire input spaces, taking $A=X$ and $B=Y$. Their inverse images are the whole new input spaces, so the constrained leaf-rectangle families in the result are precisely the ordinary leaf-rectangle families of $p$ and its pulled-back protocol. Thus the pullback of $R$ belongs to the latter family.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.preimageInputSet_mem_leafRectanglesAux_comap`.
