<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.ER.set_ll -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inner-loop counter update

**Claim.** For any register state $e$ and natural number $v$, setting the inner-loop counter to $v$ yields the state obtained by replacing its inner-loop counter with $v$.

**Proof.** The inner-loop-counter coordinate is $7$. By the definition of register update, setting it to $v$ replaces $ll$ by $v$ while preserving all other fields. The resulting state is $e$ with $ll:=v$.
