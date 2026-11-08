<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.BooleanCircuit.gateCoordinate_ne_previousGateCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct Coordinates for Earlier Gates

**Claim.** If $j$ is strictly earlier than gate $i$, then the coordinate assigned to $i$ differs from the coordinate assigned to the earlier gate at index $j$.

**Proof.** Suppose the two gate coordinates were equal. Injectivity of the map that appends the gate index after the $n$ input coordinates then gives equality of the gate indices themselves. The earlier gate index has value $j$, by the value formula for the previous-gate index (`FABL.BooleanCircuit.previousGateIndex_val`), so this would give $i=j$. This contradicts $j<i$.

**Key facts.** `FABL.BooleanCircuit.previousGateIndex_val`.
