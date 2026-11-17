<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean :: Complexity.UTab.ER.f_q -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Previous cell lookup

**Claim.** For a register record $e$, the function from the eleven indices $0$ through $10$ to the natural numbers has at index $4$ the value of the record's field for the current instruction's cell one step earlier.

**Proof.** By definition, index $4$ is assigned the field $e.q$, which records the current instruction's cell one step earlier. Since $rQ$ is index $4$, the lookup equals $e.q$.
