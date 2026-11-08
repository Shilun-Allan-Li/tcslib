<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean :: BoolCircuit.unaryFamily_circuit_of_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Family on Accepted Words

**Claim.** If the word of $n$ copies of true belongs to $L$, then the unary family’s circuit for inputs of length $n$ is the all-ones circuit on $n$ inputs.

**Proof.** By definition, the unary family chooses the all-ones circuit when the length-$n$ all-true word belongs to $L$. The hypothesis therefore selects that branch of the defining conditional, giving the claimed equality.
