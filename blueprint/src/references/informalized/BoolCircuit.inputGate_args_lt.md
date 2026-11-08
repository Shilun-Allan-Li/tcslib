<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PairEncode.lean :: BoolCircuit.inputGate_args_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Gate Argument Bounds

**Claim.** Every argument index of the gate associated with a selector is less than the number of available inputs.

**Proof.** There are two cases. If the selector is an input index $i$, its gate has the singleton argument list containing $i$; the defining bound for a finite index gives $i<n$. If the selector is a Boolean constant, its gate has no arguments, so there is no argument index to check.
