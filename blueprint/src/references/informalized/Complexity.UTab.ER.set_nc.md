<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.ER.set_nc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit-input count update

**Claim.** For any register state $e$ and natural number $v$, setting its circuit-input-count coordinate to $v$ yields the state obtained by replacing that coordinate of $e$ with $v$.

**Proof.** The circuit-input-count coordinate is $0$. Updating it to $v$ replaces the field $nc$ by $v$ and leaves the other fields unchanged. Hence the resulting state is $e$ with $nc:=v$.
