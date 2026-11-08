<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean :: Complexity.UTab.ER.f_z -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hard-wired length lookup

**Claim.** For any register state $e$, reading its hard-wired-input-length coordinate returns the length stored in $e$.

**Proof.** The hard-wired-input-length coordinate is $1$, where the register lookup function returns $e.z$. As $rZ=1$, the lookup yields $e.z$.
