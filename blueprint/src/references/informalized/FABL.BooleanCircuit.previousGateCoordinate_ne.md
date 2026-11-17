<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.BooleanCircuit.previousGateCoordinate_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct earlier gate coordinates

**Claim.** Distinct earlier gate indices $j,k<i$ have distinct coordinates in the circuit's coordinate assignment.

**Proof.** Suppose the coordinates assigned to the earlier gates $j$ and $k$ are equal. The gate-coordinate map is the natural-number addition embedding, which is injective, so the corresponding earlier gate indices are equal. Their values are respectively $j$ and $k$ (the earlier-gate index preserves the value, `previousGateIndex_val`), hence $j=k$, contradicting their assumed distinctness.

**Key facts.** `FABL.BooleanCircuit.previousGateIndex_val`.
