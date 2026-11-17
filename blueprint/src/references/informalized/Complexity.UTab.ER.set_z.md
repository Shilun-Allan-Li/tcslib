<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.ER.set_z -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Setting the Hard-Wired-Bit Count

**Claim.** Setting the hard-wired-bit count of $e$ to $v$ replaces that field by $v$ and leaves every other field unchanged.

**Proof.** The hard-wired-bit count occupies slot $1$. By the definition of the record update, setting slot $1$ to $v$ replaces $e.z$ by $v$ and leaves all other fields unchanged.
