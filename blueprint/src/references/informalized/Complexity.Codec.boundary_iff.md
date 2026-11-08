<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Step.lean :: Complexity.Codec.boundary_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Window Preservation Boundary Test

**Claim.** Under the window assumptions on $C$, the two endpoint update conditions are equivalent to the updated configuration remaining within the window and blank outside it.

**Proof.** First, evaluate the local update at each endpoint. At the left endpoint, the only way a work-tape head can move out of the window is by moving left from position $-s$; the endpoint update is empty exactly when no tape does this. Thus its condition is that every left-moving tape has head position different from $-s$. At the right endpoint, the corresponding condition is that every right-moving tape has head position different from $s$.

Assume these two conditions. For each tape, its old head lies between $-s$ and $s$. A stationary head stays there; a head moving right or left also stays there unless it starts at the respective endpoint and moves outward, which the endpoint conditions exclude. Hence every updated head remains in the window. For any position outside the window, the old tape cell is blank. A write can change a cell only at the old head position, and that position is within the window, so every outside cell remains blank.

Conversely, suppose the updated configuration is within the window. If a tape moved left from $-s$, its new head would be $-s-1$, outside the window; if it moved right from $s$, its new head would be $s+1$. Both contradict the updated head bound. Therefore neither outward endpoint move occurs, giving the two endpoint conditions. The conversion of each movement into the integer displacement $0,1,$ or $-1$ is the sign interpretation supplied by `signType_cast`.

**Key facts.** `Complexity.Codec.signType_cast`.
