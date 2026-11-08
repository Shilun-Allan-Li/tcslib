<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.DepthCircuit.depth_ge_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Depth Lower Bound

**Claim.** Every depth circuit has depth at least two.

**Proof.** The tail of a circuit contains at least one layer (`CircuitTail.one_le_layerCount`). The circuit’s depth is one plus the number of layers in that tail, so it is at least two.

**Key facts.** `FABL.CircuitTail.one_le_layerCount`.
