<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.ER.set_t -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Setting the Step Budget

**Claim.** Setting the step budget of $e$ to $v$ replaces that field by $v$ and leaves every other field unchanged.

**Proof.** The step budget occupies slot $2$. By the definition of the record update, setting slot $2$ to $v$ gives the record obtained by replacing $e.t$ with $v$ and keeping every other field fixed.
