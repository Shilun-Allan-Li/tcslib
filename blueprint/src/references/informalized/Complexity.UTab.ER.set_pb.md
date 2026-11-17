<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.ER.set_pb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Setting the Free Input Position

**Claim.** Setting the free input position of $e$ to $v$ replaces that field by $v$ and leaves every other field unchanged.

**Proof.** The slot designated for the free input position is slot $9$. By the definition of the record update, setting slot $9$ to $v$ is exactly the record update that replaces $e.pb$ with $v$.
