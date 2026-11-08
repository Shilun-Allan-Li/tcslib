<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean :: Complexity.UTab.ER.f_ll -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner-loop counter lookup

**Claim.** For every register record $e$, the function assigning its eleven fields to indices $0$ through $10$ takes the value $e.ll$ at index $7$.

**Proof.** By definition, index $7$ is assigned the inner-loop counter $e.ll$. Thus the lookup at index $7$, which is $rLL$, equals $e.ll$.
