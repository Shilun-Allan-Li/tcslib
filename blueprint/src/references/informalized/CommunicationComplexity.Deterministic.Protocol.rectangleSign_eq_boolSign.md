<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Discrepancy.lean :: CommunicationComplexity.Deterministic.Protocol.rectangleSign_eq_boolSign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rectangle sign on a leaf rectangle

**Claim.** On any leaf rectangle of a Boolean protocol, the rectangle sign equals the Boolean sign of the protocol's output at each point in that rectangle.

**Proof.** Fix a point $(x,y)$ in the leaf rectangle. If every point of the rectangle has output false, its rectangle sign is $+1$, which is the Boolean sign at $(x,y)$. Otherwise, leaf-rectangle monochromaticity says the protocol's output is constant throughout the rectangle (`leafRectangles_mono`, applied to the protocol's own execution function). Since the output is not false everywhere and the rectangle contains $(x,y)$, this constant value is true. The rectangle sign is then $-1$, again equal to the Boolean sign at $(x,y)$.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.leafRectangles_mono`.
