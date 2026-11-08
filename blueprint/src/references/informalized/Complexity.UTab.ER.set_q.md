<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.ER.set_q -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Setting the Preceding Cell

**Claim.** Setting the preceding-cell field of $e$ to $v$ replaces that field by $v$ and leaves every other field unchanged.

**Proof.** The preceding-cell field occupies slot $4$. Thus the definition of the record update at slot $4$ gives precisely the record obtained by replacing $e.q$ with $v$, leaving all other fields fixed.
