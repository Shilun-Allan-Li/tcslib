<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonSearch.lean :: BoolCircuit.MultiDAGCircuit.outputCircuit_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Selected Output

**Claim.** For a valid output index $i$, evaluating the single-output circuit selecting the $i$th designated output gives the $i$th entry of the multi-output circuit's evaluation list.

**Proof.** The selected circuit uses the same gates as the original circuit and designates its $i$th output vertex. Its evaluation therefore looks up that vertex in the shared list of gate and input values. The multi-output evaluation maps the same lookup over the designated output vertices, so its $i$th entry is that same value.
