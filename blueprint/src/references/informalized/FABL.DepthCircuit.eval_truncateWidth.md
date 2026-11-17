<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.DepthCircuit.eval_truncateWidth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation After Width Truncation

**Claim.** The truncated circuit’s value at $x$ equals the value obtained by evaluating the original later layers with each retained gate’s value at $x$ on its corresponding input and each omitted gate assigned the neutral sign for the dual of the first-layer gate type.

**Proof.** The truncated tail is the original tail with its inputs pulled back along the embedding of retained first-layer gates, followed by a cast that reconciles the finite index types. Evaluation is unchanged by this cast (`eval_castInput`). Pulling back inputs makes the original tail evaluate on an extended assignment: retained indices receive their corresponding values, and indices outside the embedding receive the neutral value for the tail gate (`eval_pullInputs`). Finally, each gate in the retained first layer is exactly the original gate at the embedded index (`get_retainedLayer1`); the finite-index identification uses that the retained list has length equal to the number of retained indices (`length_retainedLayer1`). This gives the stated evaluation formula.

**Key facts.** `FABL.CircuitTail.eval_castInput`, `FABL.CircuitTail.eval_pullInputs`, `FABL.DepthCircuit.get_retainedLayer1`, `FABL.DepthCircuit.length_retainedLayer1`.
