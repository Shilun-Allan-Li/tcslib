<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SizeClasses.lean :: finTwoEquiv_symm_eq_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean encoding of one

**Claim.** For a Boolean value $b$, the inverse of the standard bijection from Booleans to the two-element type maps $b$ to $1$ exactly when $b$ is true.

**Proof.** There are two cases. If $b$ is false, direct evaluation of the inverse bijection gives a value different from $1$, and the assertion that $b$ is true is also false. If $b$ is true, direct evaluation gives $1$, and the assertion that $b$ is true holds. Thus both sides of the equivalence agree in each case.
