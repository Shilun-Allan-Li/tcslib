<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.ER.set_pa -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Setting the Hard-Wired Input Position

**Claim.** Setting the hard-wired input position of $e$ to $v$ replaces that field by $v$ and leaves every other field unchanged.

**Proof.** The slot designated for the hard-wired input position is slot $8$. By the definition of the record update, setting slot $8$ to $v$ is exactly the record update that replaces $e.pa$ with $v$.
