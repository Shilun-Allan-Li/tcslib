<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterLayer.lean :: Complexity.UTab.range'_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addition for Consecutive Ranges

**Claim.** The range of $s$ consecutive natural numbers starting at $a+b$ is the concatenation of the range of $s$ numbers starting at $a$ and the range of $b$ numbers starting at $s+a$.

**Proof.** The general concatenation identity for stepped ranges splits a range of total length $s+b$ into an initial segment of length $s$ starting at $a$ and a remaining segment of length $b$ starting at $a+s$. Specializing the step to $1$ gives the claimed identity, after reversing the equality's sides.
