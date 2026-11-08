<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.nil_faninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Empty-input gate fan-in

**Claim.** If a gate kind $k$ is not NOT, then the gate of kind $k$ with no input vertices is well formed and has at most two inputs.

**Proof.** The empty list has no repeated entries, and its length is zero, so it meets the fan-in bound. Since the gate kind is not NOT, the implication requiring exactly one input for a NOT gate holds vacuously. These facts give well-formedness and the claimed bound.
