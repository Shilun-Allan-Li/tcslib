<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticExtensionProof_join -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering the Extension from a Joined Proof

**Claim.** Extracting the extension coordinates from the proof obtained by joining an extension assignment with an inner proof recovers the original extension assignment.

**Proof.** Fix any extension coordinate. Its designated position in the joined proof lies in the extension block, where the joined proof returns the original extension value. Thus the extracted value agrees with the original at every coordinate, so the two functions are equal.
