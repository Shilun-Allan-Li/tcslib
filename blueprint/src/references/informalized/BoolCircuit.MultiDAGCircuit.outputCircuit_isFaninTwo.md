<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonSearch.lean :: BoolCircuit.MultiDAGCircuit.outputCircuit_isFaninTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fan-In of a Selected Output Circuit

**Claim.** Every valid single-output circuit selected from a multi-output circuit with the stated fan-in-two property retains that property.

**Proof.** The selected output circuit has exactly the same gate list as the original multi-output circuit. Hence every gate still has pairwise distinct arguments, each NOT gate still has exactly one argument, and every gate still has at most two arguments. These are precisely the two conditions in the fan-in-two property, so they hold for the selected circuit as well.
