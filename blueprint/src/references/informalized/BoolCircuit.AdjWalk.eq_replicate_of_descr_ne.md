<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformAdj.lean :: BoolCircuit.AdjWalk.eq_replicate_of_descr_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonempty Description Forces Unary Input

**Claim.** If the description of a bit string $x$ is nonempty, then $x$ is the string of $|x|$ ones.

**Proof.** Unfold the definition of the description and split according to whether $x$ is the specified unary input. In the affirmative case, that branch gives $x=1^{|x|}$. In the other branch, the description is empty, contradicting the hypothesis that it is nonempty. Thus only the affirmative case is possible.
