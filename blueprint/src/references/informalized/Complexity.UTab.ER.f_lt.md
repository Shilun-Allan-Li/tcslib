<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean :: Complexity.UTab.ER.f_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Loop-counter register value

**Claim.** For a register record $e$, the value of its register function at index $6$ is its inner step-loop counter $e.lt$.

**Proof.** By definition, index $6$ is assigned the counter $e.lt$. As $rLT$ is index $6$, evaluating the register function there gives $e.lt$.
