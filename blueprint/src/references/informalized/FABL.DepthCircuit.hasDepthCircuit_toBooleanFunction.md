<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.DepthCircuit.hasDepthCircuit_toBooleanFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A circuit represents its computed function

**Claim.** Every layered circuit provides a representation of its associated Boolean function with exactly its depth, size, and first-layer width.

**Proof.** Use the circuit itself as the witness. Its computed function is, by definition, the circuit's associated Boolean function, and its depth, size, and width equal themselves. These equalities give all the required representation conditions.
