<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.boolToSign_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity of a Sign Power

**Claim.** For a Boolean value $b$ and natural number $c$, the $c$th power of its sign encoding equals that encoding when $c$ is odd, and equals one when $c$ is even.

**Proof.** If $b$ is false, its sign encoding is $1$, so every power is $1$, which agrees with either parity case. If $b$ is true, its sign encoding is $-1$. When $c$ is even, $(-1)^c=1$; when $c$ is odd, $(-1)^c=-1$. These are exactly the two asserted values.
