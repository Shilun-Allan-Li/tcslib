<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UnaryLanguages.lean :: BoolCircuit.unaryFamily_circuit_of_not_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Family on Rejected Words

**Claim.** If the word of $n$ copies of true does not belong to $L$, then the unary family’s circuit for inputs of length $n$ is the constant-zero circuit on $n$ inputs.

**Proof.** By definition, the unary family chooses the constant-zero circuit when the length-$n$ all-true word does not belong to $L$. The hypothesis selects that branch of the defining conditional, giving the claimed equality.
