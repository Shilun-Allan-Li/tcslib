<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean :: Complexity.UTab.ER.f_pa -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hard-wired input position lookup

**Claim.** For any register record $e$, the value of its field-assignment function at index $8$ is $e.pa$, the position in the hard-wired part of the input.

**Proof.** The function assigns index $8$ to the hard-wired input position $e.pa$. Since $rPA$ is index $8$, evaluating the function at $rPA$ gives $e.pa$.
