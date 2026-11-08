<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean :: Complexity.UTab.ER.f_lb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step-loop register lookup

**Claim.** For a register record $e$, the function assigning its eleven fields to indices $0$ through $10$ returns the step-loop counter $e.lb$ at index $5$.

**Proof.** By definition, index $5$ is assigned the step-loop counter $e.lb$. Since $rLB$ is index $5$, the lookup is exactly $e.lb$.
