<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean :: Complexity.UTab.ER.f_nc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input-count register lookup

**Claim.** For every register record $e$, the value of its register function at the input-count index is $e.nc$.

**Proof.** The input-count index $rNC$ is index $0$, and the function is defined to return $e.nc$ at index $0$. The claimed equality follows directly from this definition.
