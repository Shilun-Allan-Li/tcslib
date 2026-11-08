<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean :: Complexity.UTab.ER.f_i -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Current instruction lookup

**Claim.** For a register record $e$, the function assigning its eleven fields to indices $0$ through $10$ takes the value $e.i$ at index $3$.

**Proof.** By definition, index $3$ is assigned the current-instruction field $e.i$. Since $rI$ is index $3$, the lookup is exactly $e.i$.
