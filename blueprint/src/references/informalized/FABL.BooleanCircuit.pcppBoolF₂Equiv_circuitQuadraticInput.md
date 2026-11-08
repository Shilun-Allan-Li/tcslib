<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.pcppBoolF₂Equiv_circuitQuadraticInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean input encoding identity

**Claim.** For every input index, encoding the Boolean value obtained by decoding its coordinate in $z$ recovers that coordinate in $[?]$.

**Proof.** The circuit's input assignment is defined by decoding the coordinate of $z$ corresponding to the chosen input index. Since the encoding and decoding maps are inverse equivalences, encoding that decoded value returns the original coordinate.
