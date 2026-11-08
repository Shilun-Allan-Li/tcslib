<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.ER.set_i -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Current instruction update

**Claim.** For every register state $e$ and natural number $v$, setting coordinate $3$ of $e$ to $v$ gives the state obtained by replacing its current instruction with $v$.

**Proof.** The current-instruction coordinate is $3$. By the definition of register update, setting that coordinate to $v$ replaces the field $i$ by $v$ and leaves the other fields unchanged. Thus the resulting state is $e$ with $i:=v$.
