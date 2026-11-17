<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.DepthCircuit.depth_truncateWidth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth Preservation Under Width Truncation

**Claim.** For every circuit and width bound, truncating the first layer to gates of width at most the bound and pulling the later circuit’s inputs back to the retained gates leaves the circuit’s depth unchanged.

**Proof.** The depth is one plus the layer count of the circuit’s tail. Pulling the tail’s inputs back along the embedding of retained gates preserves its layer count (`layerCount_pullInputs`). The input cast used to match the truncated first layer’s size changes only the indexing type, not the tail’s layers. Thus the truncated circuit has the same depth as the original.

**Key facts.** `FABL.CircuitTail.layerCount_pullInputs`.
