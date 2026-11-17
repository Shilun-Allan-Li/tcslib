<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.ER.set_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner loop counter update

**Claim.** For every register state $e$ and natural number $v$, setting coordinate $6$ of $e$ to $v$ gives the state obtained by replacing its inner loop counter with $v$ and leaving all other fields unchanged.

**Proof.** Coordinate $6$ is the field $lt$. The definition of register update therefore changes $lt$ to $v$ and preserves the remaining fields, giving $e$ with $lt:=v$.
