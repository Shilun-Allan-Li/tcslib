<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.ER.set_tmp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Setting the Scratch Field

**Claim.** Setting the scratch field of $e$ to $v$ replaces that field by $v$ and leaves every other field unchanged.

**Proof.** The scratch field occupies slot $10$. The definition of the record update at that slot is exactly the update replacing $e.tmp$ with $v$, with the other fields unchanged.
