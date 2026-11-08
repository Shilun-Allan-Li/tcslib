<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.DepthCircuit.hasDepthCircuit_truncateWidth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Representation of a width-truncated circuit

**Claim.** The function computed by the width-truncated circuit has a representation of the original circuit's depth, with size at most the original size and first-layer width at most the threshold.

**Proof.** Use the width-truncated circuit itself as the representation witness. The truncation preserves the circuit's depth, does not increase its size, and makes its first-layer width at most the chosen threshold. Its represented function is definitionally the function in the claim, so these three parameter facts establish the result.

**Key facts.** `FABL.DepthCircuit.depth_truncateWidth`, `FABL.DepthCircuit.size_truncateWidth_le`, `FABL.DepthCircuit.width_truncateWidth_le`.
