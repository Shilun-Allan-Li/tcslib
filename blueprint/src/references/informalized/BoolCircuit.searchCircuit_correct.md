<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonSearch.lean :: BoolCircuit.searchCircuit_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the search circuit

**Claim.** Under the stated circuit hypotheses, the search circuit outputs a length-$m$ list related to the input bit list whenever a related list of length $m$ exists.

**Proof.** The search circuit's evaluation on $x$ is exactly the sequential search applied to the bit list of $x$ (`searchCircuit_eval`). That bit list has length $n$, and the assumed witness is related to it. The sequential-search correctness theorem (`searchBits_spec`) therefore shows that the circuit output is related to the input. Its output list has length $m$ by `length_searchBits`.

**Key facts.** `BoolCircuit.searchCircuit_eval`, `BoolCircuit.searchBits_spec`, `BoolCircuit.length_searchBits`.
