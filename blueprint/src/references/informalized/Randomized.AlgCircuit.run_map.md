<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.run_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation Under a Ring Homomorphism

**Claim.** Applying a ring homomorphism to the input assignment and then successively evaluating a gate list gives the same values as applying the homomorphism to each value from the original successive evaluation.

**Proof.** Induct on the gate list by removing its last gate. For the empty list, both executions are empty. For a list with a final gate, execution of the list is execution of the prefix followed by that gate's value (`Randomized.AlgCircuit.run_append_singleton`). By induction, the prefix values on the mapped inputs are the images of the original prefix values. A ring homomorphism preserves the operations used by each gate, so the image of the final gate's value equals its value on the mapped inputs and mapped prefix values (`Randomized.AlgGate.map_eval`). Appending these equal final values proves the assertion.

**Key facts.** `Randomized.AlgCircuit.run_append_singleton`, `Randomized.AlgGate.map_eval`.
