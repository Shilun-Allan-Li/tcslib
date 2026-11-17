<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticWitness_gate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate witness coordinate

**Claim.** At the coordinate assigned to gate $i$, the quadratic witness equals the field element corresponding to the Boolean value of gate $i$ on input $w$.

**Proof.** The gate coordinate is obtained by selecting the gate summand in each of the two indexing decompositions. At such an index, the witness definition returns the Boolean-to-field correspondence applied to the circuit’s evaluation at that gate. This is the stated value.
