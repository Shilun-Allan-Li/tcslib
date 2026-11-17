<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSound.lean :: Complexity.Meyer.avOf_ite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional Auxiliary Value

**Claim.** The value assigned to the auxiliary symbol chosen by the Boolean condition equals the corresponding conditional choice between its two assigned values.

**Proof.** Split on whether $s$ is true or false. If $s$ is true, the chosen symbol is $A$, and both sides equal $v_{a,j}(A)$. If $s$ is false, the chosen symbol is $B$, and both sides equal $v_{a,j}(B)$. Thus the equality holds in either case.
