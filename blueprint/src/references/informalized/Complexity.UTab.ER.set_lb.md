<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.ER.set_lb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step-loop counter update

**Claim.** For any register state $e$ and natural number $v$, updating its step-loop counter to $v$ gives the state that agrees with $e$ in every other register and has step-loop counter $v$.

**Proof.** The step-loop-counter coordinate is $5$. Updating this coordinate replaces the field $lb$ by $v$ and leaves every other field unchanged, so the result is $e$ with $lb:=v$.
