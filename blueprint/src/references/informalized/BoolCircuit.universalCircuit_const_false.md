<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Universal.lean :: BoolCircuit.universalCircuit_const_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Universal Circuit for the Zero Function

**Claim.** For every $n$, the universal circuit for the constant-zero Boolean function is an OR gate with no children.

**Proof.** The universal circuit is an OR node whose children are minterms for assignments on which the function is true. For the constant-zero function there are no such assignments, so the filtered set is empty and its list of minterms is empty. Hence the circuit is the OR node with no children.
