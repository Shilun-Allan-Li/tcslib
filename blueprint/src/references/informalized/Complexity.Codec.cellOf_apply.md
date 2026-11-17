<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Step.lean :: Complexity.Codec.cellOf_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cell Encoding Under One Step

**Claim.** For a configuration in the radius-$s$ window, each encoded cell after one action is obtained by applying the local update to that cell and its neighbors, with empty cells supplied beyond the window endpoints.

**Proof.** Compare the components of the encoded cells. For the head-and-output summary, only position $0$ carries a summary. At that position, appending the action's optional output updates the summary according to `sumIdx_append`; elsewhere the summary slot remains absent. This is precisely the summary component prescribed by the local update.

For each work tape, the symbol at the cell is the old symbol unless the head was at that position, in which case the action's optional write replaces it. This agrees with the symbol component of the local update, including when no write is specified. For the head marker, a stationary head remains at its cell. A right-moving head arrives from the cell immediately to the left, and a left-moving head arrives from the cell immediately to the right. At an endpoint the missing neighbor is empty; the old head bound ensures a head cannot cross the window boundary in a single such move. The movement is interpreted as displacement $0,1,$ or $-1$ by `signType_cast`. These componentwise comparisons establish equality of the encoded cell and the local update.

**Key facts.** `Complexity.Codec.signType_cast`, `Complexity.Codec.sumIdx_append`.
